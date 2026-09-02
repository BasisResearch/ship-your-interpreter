import Vsa.Sim.EvalCallNative
import Vsa.Sim.NativeAssertSites
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.OmegaHelpers2
import Vsa.Sim.ValueSpec
import Vsa.Sim.ReprCopy
import Vsa.Sim.EvalNotSim
import Vsa.Sim.EvalNullSim
import Vsa.Sim.ObsAvoid
import Vsa.Sim.StepFrameOut

/-!
# Layer 4 — M4: discharging the `native_assert` INTERNAL run (`Call.assertOk`)

`NativeAssertOkSpec` (`EvalCallNative.lean`) bundles the WHOLE native branch of
`Call.assertOk`: the `fv`-kind dispatch (`0x80003254`), the native arm marshal +
indirect `jalr a6` (`0x800039e0`), the `native_assert` internal run
(`0x80002df4 … ret`), and the return to the epilogue join (`0x800033ec`). This
file lands the CORE, reusable piece: the `native_assert` internal run itself,
threaded straight-line against the 33-site battery (`NativeAssertSites.lean`)
composing `value_truthy_spec` and `value_null_spec` — exactly the `blockC_not`
(Value copy → `value_truthy` → tail value-call) discharge shape.

`nativeAssertInternal` is a `Triple` in `native_assert`'s OWN 80-byte frame:
from the entry (`0x80002df4`, ABI `a0 = sret`, `a2 = argc`, `a3 = args base`,
with `args[0]` a `ValueRepr` of a TRUTHY `v` and `argc ∈ {1,2}`) to the `ret`
(`0x80002e74`) with `.null` written into the `sret` buffer (`ValueRepr … sret
.null`), the console output UNCHANGED, and the callee-saved registers + frame
restored.

The truthy machine path is gated by the `Call.assertOk` premises: `argc ∈ {1,2}`
(⇒ `argc-1 ∈ {0,1}` ⇒ the arity `bltu 1,argc-1` is NOT taken) and `v.truthy =
true` (⇒ `value_truthy` returns non-zero ⇒ the `beqz` at `0x80002e50` is NOT
taken and falls through to the `value_null` write). The falsy / arity-error arms
call `runtime_error` and are underivable in the spec (M5), matching
`Call.assertOk`.

STILL RESIDUAL (the dispatch/`jalr` wrapper): composing this internal run into
`NativeAssertOkSpec`'s `SegEntry → SegExit` shape needs the `fv`-kind dispatch
decode, the native-arm marshal, and the indirect `jalr a6 = N.addr .assert`
(`stepObs_jalr`) plus the `SegEntry` `StoreRepr → ValueRepr(.native .assert)` /
arg-vector bridge — deferred here.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 12000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Region facts for the `native_assert` internal run

`fsp` is `native_assert`'s stack pointer at entry; the prologue subtracts 80,
so the callee frame is `[fsp-80, fsp)` and the two nested callees
(`value_truthy`/`value_null`) run with `sp = fsp-80`. The truthy arg buffer is
`fsp+16 … fsp+40` (24 bytes); the frame spills live in `[fsp-80, fsp)`. The
`sret` buffer (`.null` return target) is 24 bytes. All writes must be disjoint
from the three code regions:
* `native_assert` `[0x80002df4, 0x80002ed4)`
* `value_truthy`  `[0x8000282c, 0x8000285c)`
* `value_null`    `[0x800027ec, 0x800027f8)`
and `sret` must be disjoint from the frame + truthy buffer (so the null write
does not clobber the reloaded spills). -/
structure NativeAssertRegion (fsp sret : BitVec 64) : Prop where
  -- native_assert's frame lives in writable RAM above HTIF, 8-aligned base
  fsp_align : fsp.toNat % 8 = 0
  fsp_lo : 0x80000000 + 80 ≤ fsp.toNat
  fsp_hi : fsp.toNat + 40 ≤ 0x100000000
  fsp_win : tohostAddr + 16 + 80 ≤ fsp.toNat
  -- the frame + truthy buffer window `[fsp-80, fsp+40)` disjoint from all 3 code
  frame_na : fsp.toNat + 40 ≤ 0x80002df4 ∨ 0x80002ed4 ≤ fsp.toNat - 80
  frame_vt : fsp.toNat + 40 ≤ 0x8000282c ∨ 0x8000285c ≤ fsp.toNat - 80
  frame_vn : fsp.toNat + 40 ≤ 0x800027ec ∨ 0x800027f8 ≤ fsp.toNat - 80
  -- the sret buffer facts
  sret_align : sret.toNat % 8 = 0
  sret_lo : 0x80000000 ≤ sret.toNat
  sret_hi : sret.toNat + 24 ≤ 0x100000000
  sret_win : tohostAddr + 16 ≤ sret.toNat
  sret_na : sret.toNat + 24 ≤ 0x80002df4 ∨ 0x80002ed4 ≤ sret.toNat
  sret_vt : sret.toNat + 24 ≤ 0x8000282c ∨ 0x8000285c ≤ sret.toNat
  sret_vn : sret.toNat + 24 ≤ 0x800027ec ∨ 0x800027f8 ≤ sret.toNat
  -- sret disjoint from native_assert's frame + truthy buffer `[fsp-80, fsp+40)`
  sret_frame : sret.toNat + 24 ≤ fsp.toNat - 80 ∨ fsp.toNat + 40 ≤ sret.toNat

/-! ## The three code regions survive the frame / buffer / sret stores -/

/-- `Native_assertLoaded` survives a disjoint 8-byte store. -/
theorem loaded_na_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x80002df4 ∨ 0x80002ed4 ≤ a8) (h : Native_assertLoaded mem) :
    Native_assertLoaded (writeMap8 mem a8 d) := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [native_assertChunk0] at h0 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;>
      (rw [getElem_writeMap8_disjoint mem a8 _ d (by omega)]; simp_all only [])
  · simp only [native_assertChunk1] at h1 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;>
      (rw [getElem_writeMap8_disjoint mem a8 _ d (by omega)]; simp_all only [])
  · simp only [native_assertChunk2] at h2 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;>
      (rw [getElem_writeMap8_disjoint mem a8 _ d (by omega)]; simp_all only [])
  · simp only [native_assertChunk3] at h3 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [getElem_writeMap8_disjoint mem a8 _ d (by omega)]; simp_all only [])

/-- `Native_assertLoaded` survives an agreement on its code region. -/
theorem loaded_na_agreeP (m m' : Mem)
    (ha : ∀ a, (0x80002df4 ≤ a ∧ a < 0x80002ed4) → m[a]? = m'[a]?)
    (h : Native_assertLoaded m) : Native_assertLoaded m' := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [native_assertChunk0] at h0 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;>
      (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [native_assertChunk1] at h1 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;>
      (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [native_assertChunk2] at h2 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_⟩ <;>
      (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [native_assertChunk3] at h3 ⊢
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      (rw [← ha _ (by omega)]; simp_all only [])

/- `loaded_null_agreeP` RELOCATED to `InterpEntry.lean` (wave 47f, `GeomFrom`);
same name/namespace. -/

/-! ## `nativeAssertInternal` — the `native_assert` internal run

From the entry (`0x80002df4`) to the `ret` (`0x80002e74`). The truthy path
(`v.truthy = true`, `argc ∈ {1,2}`) copies `args[0] = v` into the truthy arg
buffer, `value_truthy` returns non-zero, the `beqz` falls through, `value_null`
writes `.null` into the `sret` buffer, and the epilogue restores the frame and
returns. Console output unchanged; `.null` produced at `sret`. -/

/-- Precondition: at `native_assert`'s entry, with the ABI arguments staged and
the three code regions loaded, `args[0]` a `ValueRepr` of a truthy `v`, and the
region facts. `argc ∈ {1,2}` (as `argcM1 = argc - 1 ∈ {0,1}`, gating the arity
`bltu`). -/
def naEntry (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (v : Value)
    (fsp sret retAddr argsBase argc interp scratch : BitVec 64)
    (s0v s1v s2v : BitVec 64) (m0 : Mem) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧
  Native_assertLoaded c.σ.mem ∧ Value_truthyLoaded c.σ.mem ∧ Value_nullLoaded c.σ.mem ∧
  c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80002df4#64) ∧
  c.σ.regs.get? Register.x10 = some sret ∧
  c.σ.regs.get? Register.x11 = some interp ∧
  c.σ.regs.get? Register.x12 = some argc ∧
  c.σ.regs.get? Register.x13 = some argsBase ∧
  c.σ.regs.get? Register.x14 = some scratch ∧
  c.σ.regs.get? Register.x1 = some retAddr ∧
  c.σ.regs.get? Register.x2 = some fsp ∧
  c.σ.regs.get? Register.x8 = some s0v ∧
  c.σ.regs.get? Register.x9 = some s1v ∧
  c.σ.regs.get? Register.x18 = some s2v ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧ c.tick < 2 ∧
  -- args[0] holds `v`; truthy premise; arity premise
  ValueRepr m0 N φc argsBase.toNat v ∧ v.truthy = true ∧
  (argc = 1#64 ∨ argc = 2#64) ∧
  -- the args[0] Value-array window `[argsBase, argsBase+24)` is disjoint from
  -- native_assert's frame + truthy buffer `[fsp-80, fsp+40)` (it lives in the
  -- CALLER's frame / the arena, above native_assert's frame), so the 4 frame
  -- spills do not clobber it before it is loaded.
  (argsBase.toNat + 24 ≤ fsp.toNat - 80 ∨ fsp.toNat + 40 ≤ argsBase.toNat) ∧
  argsBase.toNat + 24 ≤ 0x100000000 ∧ tohostAddr + 8 ≤ argsBase.toNat ∧ argsBase.toNat % 8 = 0 ∧
  -- the args[0] Value is fully materialised (all 24 bytes present)
  (∀ j : Nat, j < 24 → ∃ b, m0[argsBase.toNat + j]? = some b) ∧
  -- the args-base payload pointer (str/native name) lives disjoint from the whole
  -- native_assert frame + buffer window `[fsp-80, fsp+40)` (it is in the arena).
  (∀ (p : Nat) (s : String),
    read64 m0 (argsBase.toNat + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < fsp.toNat - 80 ∨ fsp.toNat + 40 ≤ p + k)) ∧
  NativeAssertRegion fsp sret ∧
  (BitVec.update (retAddr + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 ∧
  c.σ.sailOutput = out0 ∧
  (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R)

/-- Postcondition: at the `ret` target (`retAddr`, bit-0-cleared), the `sret`
buffer holds `.null` (`ValueRepr … sret .null`), the console output is
unchanged, and the callee-saved registers + `sp` are restored. -/
def naExit (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat)
    (fsp sret retAddr : BitVec 64) (m0 : Mem) (out0 : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (BitVec.update (retAddr + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
  ValueRepr c.σ.mem N φc sret.toNat .null ∧
  c.σ.sailOutput = out0 ∧
  -- memory outside native_assert's frame + sret is framed to m0 (nothing else is
  -- touched: the frame spills, the truthy buffer, and the sret write are all inside
  -- `[fsp-80, fsp+40) ∪ [sret, sret+24)`).
  (∀ a : Nat, (a < fsp.toNat - 80 ∨ fsp.toNat + 40 ≤ a) → (a < sret.toNat ∨ sret.toNat + 24 ≤ a) →
    c.σ.mem[a]? = m0[a]?) ∧
  (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
  c.σ.regs.get? Register.x2 = some fsp ∧
  -- the FULL ABI callee-saved frame (wave-42 amendment, observation
  -- `naexit-lacks-abi-frame-clause`): the epilogue reloads `ra/s0/s1/s2` from
  -- their spills and re-adjusts `sp`; no other callee-saved register is
  -- written anywhere in the run (including the two callee sub-runs).
  (∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R)

/-- Named destructurer (R7): the ABI callee-saved frame clause of `naExit`. -/
theorem naExit_abiFrame {g : (R : Register) → Option (RegisterType R)}
    {N : NativeAddrs} {φc : Addr → Nat} {fsp sret retAddr : BitVec 64}
    {m0 : Mem} {out0 : Array String} {c : Config}
    (h : naExit g N φc fsp sret retAddr m0 out0 c) :
    ∀ R : Register, AbiPreservedNoise R → c.σ.regs.get? R = g R := by
  obtain ⟨_, _, _, _, _, _, _, _, hframe⟩ := h; exact hframe

/-- `AbiPreserved` enumerated: a callee-saved register is one of the fifteen
`sp/gp/tp/s0–s11`. Lets a whole-run frame clause split the machine-written
callee-saveds (tracked values) from the never-written rest (`StepFrameOut`). -/
theorem abiPreserved_enum (R : Register) (h : AbiPreserved R = true) :
    R = .x2 ∨ R = .x3 ∨ R = .x4 ∨ R = .x8 ∨ R = .x9 ∨ R = .x18 ∨ R = .x19 ∨
    R = .x20 ∨ R = .x21 ∨ R = .x22 ∨ R = .x23 ∨ R = .x24 ∨ R = .x25 ∨
    R = .x26 ∨ R = .x27 := by
  revert h; cases R <;> decide

/-- Addressing lemma: `fsp + sext imm` for the small positive offsets used by the
buffer stores, as `fsp.toNat + off`, no wrap (using `fsp + 40 ≤ 2^32`). -/
theorem na_off_pos (fsp : BitVec 64) (imm : BitVec 12) (off : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = BitVec.ofNat 64 off)
    (hoff : off ≤ 40) (hhi : fsp.toNat + 40 ≤ 0x100000000) :
    (fsp + sign_extend (m := 64) imm).toNat = fsp.toNat + off := by
  rw [himm, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by have := fsp.isLt; omega), Nat.mod_eq_of_lt (by omega)]

/-- Addressing lemma for the negative frame offsets: `sp + sext imm` where
`sp = fsp - 80` and `imm` (positive, in `[0,72]`) lands at `fsp - 80 + imm`. -/
theorem na_off_frame (fsp : BitVec 64) (imm : BitVec 12) (off : Nat)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = BitVec.ofNat 64 off)
    (hoff : off ≤ 72) (hlo : 80 ≤ fsp.toNat) (hhi : fsp.toNat + 40 ≤ 0x100000000) :
    ((fsp - 80#64) + sign_extend (m := 64) imm).toNat = fsp.toNat - 80 + off := by
  have hsub : (fsp - 80#64).toNat = fsp.toNat - 80 := by
    rw [BitVec.toNat_sub]; have h80 : (80#64 : BitVec 64).toNat = 80 := by decide
    rw [h80]; have := fsp.isLt; omega
  rw [himm, BitVec.toNat_add, hsub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]

/-- **The `native_assert` internal run (truthy path).** From `naEntry` to
`naExit`: the truthy `args[0]` is copied to the buffer, `value_truthy` returns
non-zero, `value_null` writes `.null` into `sret`, and the frame is restored. -/
theorem nativeAssertInternal
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (φc : Addr → Nat) (v : Value)
    (fsp sret retAddr argsBase argc interp scratch : BitVec 64)
    (s0v s1v s2v : BitVec 64) (m0 : Mem) (out0 : Array String) :
    Triple
      (naEntry g N φc v fsp sret retAddr argsBase argc interp scratch s0v s1v s2v m0 out0)
      (naExit g N φc fsp sret retAddr m0 out0) := by
  intro c hpre
  obtain ⟨hG, hNA, hVT, hVN, hmem, hpc, ha0, ha1, ha2, ha3, ha4, hra, hsp, hs0r, hs1r, hs2r,
    ⟨vmi, hmi⟩, htick, hvRepr, htruthy, hargc, hargsFrame, hargsHi, hargsWin, hargsAlign,
    hargsPresent, hpayDisj, hRG, hrettgt, hout, hframe⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- frame base arithmetic
  have hfsp80 : 80 ≤ fsp.toNat := by have := hRG.fsp_lo; omega
  have hspNat : (fsp - 80#64).toNat = fsp.toNat - 80 := by
    rw [BitVec.toNat_sub]; have h80 : (80#64 : BitVec 64).toNat = 80 := by decide
    rw [h80]; have := fsp.isLt; omega
  -- offset addresses for the frame spills and buffer stores
  have haddr56 : ((fsp - 80#64) + sign_extend (m := 64) (0x038#12)).toNat = fsp.toNat - 80 + 56 :=
    na_off_frame fsp (0x038#12) 56 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr48 : ((fsp - 80#64) + sign_extend (m := 64) (0x030#12)).toNat = fsp.toNat - 80 + 48 :=
    na_off_frame fsp (0x030#12) 48 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr72 : ((fsp - 80#64) + sign_extend (m := 64) (0x048#12)).toNat = fsp.toNat - 80 + 72 :=
    na_off_frame fsp (0x048#12) 72 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr64 : ((fsp - 80#64) + sign_extend (m := 64) (0x040#12)).toNat = fsp.toNat - 80 + 64 :=
    na_off_frame fsp (0x040#12) 64 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr16 : ((fsp - 80#64) + sign_extend (m := 64) (0x010#12)).toNat = fsp.toNat - 80 + 16 :=
    na_off_frame fsp (0x010#12) 16 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr24 : ((fsp - 80#64) + sign_extend (m := 64) (0x018#12)).toNat = fsp.toNat - 80 + 24 :=
    na_off_frame fsp (0x018#12) 24 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr32 : ((fsp - 80#64) + sign_extend (m := 64) (0x020#12)).toNat = fsp.toNat - 80 + 32 :=
    na_off_frame fsp (0x020#12) 32 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr8 : ((fsp - 80#64) + sign_extend (m := 64) (0x008#12)).toNat = fsp.toNat - 80 + 8 :=
    na_off_frame fsp (0x008#12) 8 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  have haddr0 : ((fsp - 80#64) + sign_extend (m := 64) (0x000#12)).toNat = fsp.toNat - 80 + 0 :=
    na_off_frame fsp (0x000#12) 0 (by apply BitVec.eq_of_toNat_eq; decide) (by omega) hfsp80 hRG.fsp_hi
  -- named window bounds
  have hfspWin : tohostAddr + 16 + 80 ≤ fsp.toNat := hRG.fsp_win
  ------------------------------------------------------------------------
  -- Prologue: 0x80002df4 addi sp,sp,-80 ; 4 spills.
  ------------------------------------------------------------------------
  -- 0x80002df4: addi sp,sp,-80 → x2 := fsp-80
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_80002df4_na c.σ c.tick c.steps (0x80002df4#64) vmi fsp hG hpc hmi hsp hNA rfl htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80002df8#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x80002df4#64) 4 = (0x80002df8#64 : BitVec 64) from by decide] at this
  have hsp1 : σ1.regs.get? Register.x2 = some (fsp - 80#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (fsp + sign_extend (m := 64) (0xfb0#12) : BitVec 64) = fsp - 80#64 from by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_sub, BitVec.toNat_add]
      have : (sign_extend (m := 64) (0xfb0#12) : BitVec 64).toNat = 0xffffffffffffffb0 := by decide
      rw [this]; have h80 : (80#64 : BitVec 64).toNat = 80 := by decide
      rw [h80]; have := fsp.isLt; omega] at this
  have hx1_1 : σ1.regs.get? Register.x1 = some retAddr := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have hx8_1 : σ1.regs.get? Register.x8 = some s0v := obs_alu_other' hobs1 Register.x8 (by decide) hs0r
  have hx9_1 : σ1.regs.get? Register.x9 = some s1v := obs_alu_other' hobs1 Register.x9 (by decide) hs1r
  have hx18_1 : σ1.regs.get? Register.x18 = some s2v := obs_alu_other' hobs1 Register.x18 (by decide) hs2r
  have hx10_1 : σ1.regs.get? Register.x10 = some sret := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hx11_1 : σ1.regs.get? Register.x11 = some interp := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hx12_1 : σ1.regs.get? Register.x12 = some argc := obs_alu_other' hobs1 Register.x12 (by decide) ha2
  have hx13_1 : σ1.regs.get? Register.x13 = some argsBase := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have hx14_1 : σ1.regs.get? Register.x14 = some scratch := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  have hNA1 : Native_assertLoaded σ1.mem := by rw [hmem1e]; exact hNA
  -- code-region disjointness for all frame/buffer stores (window [fsp-80, fsp+40))
  have hcodeNA : ∀ o : Nat, o < 80 → (fsp.toNat - 80 + o) + 8 ≤ 0x80002df4 ∨ 0x80002ed4 ≤ (fsp.toNat - 80 + o) := by
    intro o ho; rcases hRG.frame_na with h | h
    · left; omega
    · right; omega
  -- spill store memory tower
  let ms1 : Mem := writeMap8 c.σ.mem (fsp.toNat - 80 + 56) (sdData_val s1v)
  let ms2 : Mem := writeMap8 ms1 (fsp.toNat - 80 + 48) (sdData_val s2v)
  let ms3 : Mem := writeMap8 ms2 (fsp.toNat - 80 + 72) (sdData_val retAddr)
  let ms4 : Mem := writeMap8 ms3 (fsp.toNat - 80 + 64) (sdData_val s0v)
  -- 0x80002df8: sd s1,56(sp) → ms1
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80002df8_na σ1 i1 (c.steps + 1) (0x80002df8#64) vmi1 (fsp - 80#64) s1v
      hG1 hpc1 hmi1 hsp1 hx9_1 hNA1 rfl
      (naStore_safe4 fsp.toNat _ 56 haddr56 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 56 haddr56 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 56 haddr56 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 56 haddr56 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = ms1 := by rw [hmem2, mem_afterNextPC, haddr56, hmem1e]
  have hpc2 : σ2.regs.get? Register.PC = some (0x80002dfc#64) := by
    have := obs_store_pc_val hobs2
    rwa [show BitVec.addInt (0x80002df8#64) 4 = (0x80002dfc#64 : BitVec 64) from by decide] at this
  have hsp2 := obs_store_other_val' hobs2 Register.x2 (by decide) hsp1
  have hx1_2 := obs_store_other_val' hobs2 Register.x1 (by decide) hx1_1
  have hx8_2 := obs_store_other_val' hobs2 Register.x8 (by decide) hx8_1
  have hx18_2 := obs_store_other_val' hobs2 Register.x18 (by decide) hx18_1
  have hx10_2 := obs_store_other_val' hobs2 Register.x10 (by decide) hx10_1
  have hx11_2 := obs_store_other_val' hobs2 Register.x11 (by decide) hx11_1
  have hx12_2 := obs_store_other_val' hobs2 Register.x12 (by decide) hx12_1
  have hx13_2 := obs_store_other_val' hobs2 Register.x13 (by decide) hx13_1
  have hx14_2 := obs_store_other_val' hobs2 Register.x14 (by decide) hx14_1
  obtain ⟨vmi2, hmi2⟩ := obs_store_minstret_val hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_store]; exact hout1
  have hNA2 : Native_assertLoaded σ2.mem := by
    rw [hmem2e]; exact loaded_na_writeMap8 c.σ.mem _ _ (hcodeNA 56 (by omega)) hNA
  -- 0x80002dfc: sd s2,48(sp) → ms2
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80002dfc_na σ2 i2 (c.steps + 1 + 1) (0x80002dfc#64) vmi2 (fsp - 80#64) s2v
      hG2 hpc2 hmi2 hsp2 hx18_2 hNA2 rfl
      (naStore_safe4 fsp.toNat _ 48 haddr48 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 48 haddr48 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 48 haddr48 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 48 haddr48 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = ms2 := by rw [hmem3, mem_afterNextPC, haddr48, hmem2e]
  have hpc3 : σ3.regs.get? Register.PC = some (0x80002e00#64) := by
    have := obs_store_pc_val hobs3
    rwa [show BitVec.addInt (0x80002dfc#64) 4 = (0x80002e00#64 : BitVec 64) from by decide] at this
  have hsp3 := obs_store_other_val' hobs3 Register.x2 (by decide) hsp2
  have hx1_3 := obs_store_other_val' hobs3 Register.x1 (by decide) hx1_2
  have hx8_3 := obs_store_other_val' hobs3 Register.x8 (by decide) hx8_2
  have hx10_3 := obs_store_other_val' hobs3 Register.x10 (by decide) hx10_2
  have hx11_3 := obs_store_other_val' hobs3 Register.x11 (by decide) hx11_2
  have hx12_3 := obs_store_other_val' hobs3 Register.x12 (by decide) hx12_2
  have hx13_3 := obs_store_other_val' hobs3 Register.x13 (by decide) hx13_2
  have hx14_3 := obs_store_other_val' hobs3 Register.x14 (by decide) hx14_2
  obtain ⟨vmi3, hmi3⟩ := obs_store_minstret_val hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_store]; exact hout2
  have hNA3 : Native_assertLoaded σ3.mem := by
    rw [hmem3e]; exact loaded_na_writeMap8 ms1 _ _ (hcodeNA 48 (by omega)) (hmem2e ▸ hNA2)
  -- 0x80002e00: sd ra,72(sp) → ms3
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80002e00_na σ3 i3 (c.steps + 1 + 1 + 1) (0x80002e00#64) vmi3 (fsp - 80#64) retAddr
      hG3 hpc3 hmi3 hsp3 hx1_3 hNA3 rfl
      (naStore_safe4 fsp.toNat _ 72 haddr72 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 72 haddr72 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 72 haddr72 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 72 haddr72 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = ms3 := by rw [hmem4, mem_afterNextPC, haddr72, hmem3e]
  have hpc4 : σ4.regs.get? Register.PC = some (0x80002e04#64) := by
    have := obs_store_pc_val hobs4
    rwa [show BitVec.addInt (0x80002e00#64) 4 = (0x80002e04#64 : BitVec 64) from by decide] at this
  have hsp4 := obs_store_other_val' hobs4 Register.x2 (by decide) hsp3
  have hx8_4 := obs_store_other_val' hobs4 Register.x8 (by decide) hx8_3
  have hx10_4 := obs_store_other_val' hobs4 Register.x10 (by decide) hx10_3
  have hx11_4 := obs_store_other_val' hobs4 Register.x11 (by decide) hx11_3
  have hx12_4 := obs_store_other_val' hobs4 Register.x12 (by decide) hx12_3
  have hx13_4 := obs_store_other_val' hobs4 Register.x13 (by decide) hx13_3
  have hx14_4 := obs_store_other_val' hobs4 Register.x14 (by decide) hx14_3
  obtain ⟨vmi4, hmi4⟩ := obs_store_minstret_val hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_store]; exact hout3
  have hNA4 : Native_assertLoaded σ4.mem := by
    rw [hmem4e]; exact loaded_na_writeMap8 ms2 _ _ (hcodeNA 72 (by omega)) (hmem3e ▸ hNA3)
  -- 0x80002e04: sd s0,64(sp) → ms4
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_80002e04_na σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80002e04#64) vmi4 (fsp - 80#64) s0v
      hG4 hpc4 hmi4 hsp4 hx8_4 hNA4 rfl
      (naStore_safe4 fsp.toNat _ 64 haddr64 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 64 haddr64 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 64 haddr64 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 64 haddr64 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = ms4 := by rw [hmem5, mem_afterNextPC, haddr64, hmem4e]
  have hpc5 : σ5.regs.get? Register.PC = some (0x80002e08#64) := by
    have := obs_store_pc_val hobs5
    rwa [show BitVec.addInt (0x80002e04#64) 4 = (0x80002e08#64 : BitVec 64) from by decide] at this
  have hsp5 := obs_store_other_val' hobs5 Register.x2 (by decide) hsp4
  have hx10_5 := obs_store_other_val' hobs5 Register.x10 (by decide) hx10_4
  have hx11_5 := obs_store_other_val' hobs5 Register.x11 (by decide) hx11_4
  have hx12_5 := obs_store_other_val' hobs5 Register.x12 (by decide) hx12_4
  have hx13_5 := obs_store_other_val' hobs5 Register.x13 (by decide) hx13_4
  have hx14_5 := obs_store_other_val' hobs5 Register.x14 (by decide) hx14_4
  obtain ⟨vmi5, hmi5⟩ := obs_store_minstret_val hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_store]; exact hout4
  have hNA5 : Native_assertLoaded σ5.mem := by
    rw [hmem5e]; exact loaded_na_writeMap8 ms3 _ _ (hcodeNA 64 (by omega)) (hmem4e ▸ hNA4)
  ------------------------------------------------------------------------
  -- Setup ALUs 0x80002e08 … e14, arity branch e18 (NOT taken).
  ------------------------------------------------------------------------
  -- 0x80002e08: addiw a6,a2,-1 → x16 := sext32(argc-1)
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80002e08_na σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80002e08#64) vmi5 argc
      hG5 hpc5 hmi5 hx12_5 hNA5 rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6'
  have hmem6e : σ6.mem = ms4 := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80002e0c#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80002e08#64) 4 = (0x80002e0c#64 : BitVec 64) from by decide] at this
  have hx16_6 : σ6.regs.get? Register.x16 = some (sign_extend (m := 64) (Sail.BitVec.extractLsb (argc + sign_extend (m := 64) (0xfff#12)) 31 0)) :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp6 := obs_alu_other' hobs6 Register.x2 (by decide) hsp5
  have hx10_6 := obs_alu_other' hobs6 Register.x10 (by decide) hx10_5
  have hx11_6 := obs_alu_other' hobs6 Register.x11 (by decide) hx11_5
  have hx13_6 := obs_alu_other' hobs6 Register.x13 (by decide) hx13_5
  have hx14_6 := obs_alu_other' hobs6 Register.x14 (by decide) hx14_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact hout5
  have hNA6 : Native_assertLoaded σ6.mem := by rw [hmem6e]; exact hmem5e ▸ hNA5
  -- 0x80002e0c: li a5,1 → x15 := 1
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80002e0c_na σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e0c#64) vmi6 hG6 hpc6 hmi6 hNA6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7'
  have hmem7e : σ7.mem = ms4 := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80002e10#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80002e0c#64) 4 = (0x80002e10#64 : BitVec 64) from by decide] at this
  have hx15_7 : σ7.regs.get? Register.x15 = some (1#64) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((0#64 : BitVec 64) + sign_extend (m := 64) (0x001#12)) = 1#64 from by apply BitVec.eq_of_toNat_eq; decide] at this
  have hx16_7 := obs_alu_other' hobs7 Register.x16 (by decide) hx16_6
  have hsp7 := obs_alu_other' hobs7 Register.x2 (by decide) hsp6
  have hx10_7 := obs_alu_other' hobs7 Register.x10 (by decide) hx10_6
  have hx11_7 := obs_alu_other' hobs7 Register.x11 (by decide) hx11_6
  have hx13_7 := obs_alu_other' hobs7 Register.x13 (by decide) hx13_6
  have hx14_7 := obs_alu_other' hobs7 Register.x14 (by decide) hx14_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_alu]; exact hout6
  have hNA7 : Native_assertLoaded σ7.mem := by rw [hmem7e]; exact hmem6e ▸ hNA6
  -- 0x80002e10: mv s1,a1 → x9 := interp
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80002e10_na σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e10#64) vmi7 interp
      hG7 hpc7 hmi7 hx11_7 hNA7 rfl hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = ms4 := by rw [hmem8]; exact hmem7e
  have hpc8 : σ8.regs.get? Register.PC = some (0x80002e14#64) := by
    have := obs_alu_pc hobs8
    rwa [show BitVec.addInt (0x80002e10#64) 4 = (0x80002e14#64 : BitVec 64) from by decide] at this
  have hsp8 := obs_alu_other' hobs8 Register.x2 (by decide) hsp7
  have hx15_8 := obs_alu_other' hobs8 Register.x15 (by decide) hx15_7
  have hx16_8 := obs_alu_other' hobs8 Register.x16 (by decide) hx16_7
  have hx10_8 := obs_alu_other' hobs8 Register.x10 (by decide) hx10_7
  have hx13_8 := obs_alu_other' hobs8 Register.x13 (by decide) hx13_7
  have hx14_8 := obs_alu_other' hobs8 Register.x14 (by decide) hx14_7
  obtain ⟨vmi8, hmi8⟩ := obs_alu_minstret hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_alu]; exact hout7
  have hNA8 : Native_assertLoaded σ8.mem := by rw [hmem8e]; exact hmem7e ▸ hNA7
  -- 0x80002e14: mv s2,a4 → x18 := scratch
  obtain ⟨σ9, i9, hs9', hi9, hG9, hmem9, hobs9⟩ :=
    site_80002e14_na σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e14#64) vmi8 scratch
      hG8 hpc8 hmi8 hx14_8 hNA8 rfl hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9'
  have hmem9e : σ9.mem = ms4 := by rw [hmem9]; exact hmem8e
  have hpc9 : σ9.regs.get? Register.PC = some (0x80002e18#64) := by
    have := obs_alu_pc hobs9
    rwa [show BitVec.addInt (0x80002e14#64) 4 = (0x80002e18#64 : BitVec 64) from by decide] at this
  have hsp9 := obs_alu_other' hobs9 Register.x2 (by decide) hsp8
  have hx15_9 := obs_alu_other' hobs9 Register.x15 (by decide) hx15_8
  have hx16_9 := obs_alu_other' hobs9 Register.x16 (by decide) hx16_8
  have hx10_9 := obs_alu_other' hobs9 Register.x10 (by decide) hx10_8
  have hx13_9 := obs_alu_other' hobs9 Register.x13 (by decide) hx13_8
  obtain ⟨vmi9, hmi9⟩ := obs_alu_minstret hobs9
  have hout9 : σ9.sailOutput = out0 := by rw [hobs9.out, sailOutput_sigmaPost_alu]; exact hout8
  have hNA9 : Native_assertLoaded σ9.mem := by rw [hmem9e]; exact hmem8e ▸ hNA8
  -- arity premise: sext32(argc-1) with argc ∈ {1,2}; `1 <u (argc-1) = false`
  have harity : zopz0zI_u (1#64) (sign_extend (m := 64) (Sail.BitVec.extractLsb (argc + sign_extend (m := 64) (0xfff#12)) 31 0)) = false := by
    rcases hargc with rfl | rfl <;> decide
  -- 0x80002e18: bltu a5,a6 (NOT taken) → 0x80002e1c
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80002e18_nottaken_na σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e18#64) vmi9
      (1#64) (sign_extend (m := 64) (Sail.BitVec.extractLsb (argc + sign_extend (m := 64) (0xfff#12)) 31 0))
      hG9 hpc9 hmi9 hx15_9 hx16_9 hNA9 rfl harity hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10'
  have hmem10e : σ10.mem = ms4 := by rw [hmem10]; exact hmem9e
  have hpc10 : σ10.regs.get? Register.PC = some (0x80002e1c#64) := by
    have := obs_branch_nottaken_pc hobs10
    rwa [show BitVec.addInt (0x80002e18#64) 4 = (0x80002e1c#64 : BitVec 64) from by decide] at this
  have hsp10 := obs_branch_nottaken_other' hobs10 Register.x2 (by decide) hsp9
  have hx10_10 := obs_branch_nottaken_other' hobs10 Register.x10 (by decide) hx10_9
  have hx13_10 := obs_branch_nottaken_other' hobs10 Register.x13 (by decide) hx13_9
  obtain ⟨vmi10, hmi10⟩ := obs_branch_nottaken_minstret hobs10
  have hout10 : σ10.sailOutput = out0 := by rw [hobs10.out, sailOutput_sigmaPost_branch_nottaken]; exact hout9
  have hNA10 : Native_assertLoaded σ10.mem := by rw [hmem10e]; exact hmem9e ▸ hNA9
  ------------------------------------------------------------------------
  -- args[0] loads e1c/e20/e24 (from argsBase in ms4 = m0 outside frame), mv s0,
  -- addi a0=buf, 2 spills, 3 buffer copy stores.
  ------------------------------------------------------------------------
  -- ms4 agrees with m0 on the argsBase window (frame writes are disjoint)
  have hms4_args : ∀ a : Nat, (argsBase.toNat ≤ a ∧ a < argsBase.toNat + 24) → ms4[a]? = m0[a]? := by
    intro a ha
    show (writeMap8 ms3 (fsp.toNat-80+64) (sdData_val s0v))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms3 (fsp.toNat-80+64) a (sdData_val s0v) (by rcases hargsFrame with h|h <;> omega)]
    show (writeMap8 ms2 (fsp.toNat-80+72) (sdData_val retAddr))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms2 (fsp.toNat-80+72) a (sdData_val retAddr) (by rcases hargsFrame with h|h <;> omega)]
    show (writeMap8 ms1 (fsp.toNat-80+48) (sdData_val s2v))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms1 (fsp.toNat-80+48) a (sdData_val s2v) (by rcases hargsFrame with h|h <;> omega)]
    show (writeMap8 c.σ.mem (fsp.toNat-80+56) (sdData_val s1v))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (fsp.toNat-80+56) a (sdData_val s1v) (by rcases hargsFrame with h|h <;> omega)]
    rw [hmem]
  -- byte witnesses for the 24 argsBase bytes in ms4
  have hab : ∀ j : Nat, j < 24 → ∃ b, ms4[argsBase.toNat + j]? = some b := by
    intro j hj; obtain ⟨b, hb⟩ := hargsPresent j hj
    exact ⟨b, (hms4_args (argsBase.toNat + j) (by omega)).trans hb⟩
  obtain ⟨ab0, hab0⟩ := hab 0 (by omega); obtain ⟨ab1, hab1⟩ := hab 1 (by omega)
  obtain ⟨ab2, hab2⟩ := hab 2 (by omega); obtain ⟨ab3, hab3⟩ := hab 3 (by omega)
  obtain ⟨ab4, hab4⟩ := hab 4 (by omega); obtain ⟨ab5, hab5⟩ := hab 5 (by omega)
  obtain ⟨ab6, hab6⟩ := hab 6 (by omega); obtain ⟨ab7, hab7⟩ := hab 7 (by omega)
  obtain ⟨ab8, hab8⟩ := hab 8 (by omega); obtain ⟨ab9, hab9⟩ := hab 9 (by omega)
  obtain ⟨ab10, hab10⟩ := hab 10 (by omega); obtain ⟨ab11, hab11⟩ := hab 11 (by omega)
  obtain ⟨ab12, hab12⟩ := hab 12 (by omega); obtain ⟨ab13, hab13⟩ := hab 13 (by omega)
  obtain ⟨ab14, hab14⟩ := hab 14 (by omega); obtain ⟨ab15, hab15⟩ := hab 15 (by omega)
  obtain ⟨ab16, hab16⟩ := hab 16 (by omega); obtain ⟨ab17, hab17⟩ := hab 17 (by omega)
  obtain ⟨ab18, hab18⟩ := hab 18 (by omega); obtain ⟨ab19, hab19⟩ := hab 19 (by omega)
  obtain ⟨ab20, hab20⟩ := hab 20 (by omega); obtain ⟨ab21, hab21⟩ := hab 21 (by omega)
  obtain ⟨ab22, hab22⟩ := hab 22 (by omega); obtain ⟨ab23, hab23⟩ := hab 23 (by omega)
  have hargsAddr0 : (argsBase + sign_extend (m := 64) (0x000#12)).toNat = argsBase.toNat := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]
  have hargsAddr8 : (argsBase + sign_extend (m := 64) (0x008#12)).toNat = argsBase.toNat + 8 := by
    rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have hargsAddr16 : (argsBase + sign_extend (m := 64) (0x010#12)).toNat = argsBase.toNat + 16 := by
    rw [show (sign_extend (m := 64) (0x010#12) : BitVec 64) = 16#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  -- reassembled load values
  let LV0 : BitVec 64 := sign_extend (m := 64) ((((((((ab7.append ab6).append ab5).append ab4).append ab3).append ab2).append ab1).append ab0) : BitVec (8*8))
  let LV1 : BitVec 64 := sign_extend (m := 64) ((((((((ab15.append ab14).append ab13).append ab12).append ab11).append ab10).append ab9).append ab8) : BitVec (8*8))
  let LV2 : BitVec 64 := sign_extend (m := 64) ((((((((ab23.append ab22).append ab21).append ab20).append ab19).append ab18).append ab17).append ab16) : BitVec (8*8))
  -- 0x80002e1c: ld a1,0(a3) → x11 := LV0
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80002e1c_na σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e1c#64) vmi10 argsBase
      ab0 ab1 ab2 ab3 ab4 ab5 ab6 ab7 hG10 hpc10 hmi10 hx13_10 hNA10 rfl
      (by rw [hargsAddr0]; omega) (by rw [hargsAddr0]; omega)
      (by rw [hargsAddr0, htoh]; right; omega) (by rw [hargsAddr0]; omega)
      (by rw [hargsAddr0, hmem10e]; exact hab0) (by rw [hargsAddr0, hmem10e]; exact hab1)
      (by rw [hargsAddr0, hmem10e]; exact hab2) (by rw [hargsAddr0, hmem10e]; exact hab3)
      (by rw [hargsAddr0, hmem10e]; exact hab4) (by rw [hargsAddr0, hmem10e]; exact hab5)
      (by rw [hargsAddr0, hmem10e]; exact hab6) (by rw [hargsAddr0, hmem10e]; exact hab7) hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11'
  have hmem11e : σ11.mem = ms4 := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x80002e20#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x80002e1c#64) 4 = (0x80002e20#64 : BitVec 64) from by decide] at this
  have hx11_11 : σ11.regs.get? Register.x11 = some LV0 := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp11 := obs_alu_other' hobs11 Register.x2 (by decide) hsp10
  have hx10_11 := obs_alu_other' hobs11 Register.x10 (by decide) hx10_10
  have hx13_11 := obs_alu_other' hobs11 Register.x13 (by decide) hx13_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hout11 : σ11.sailOutput = out0 := by rw [hobs11.out, sailOutput_sigmaPost_alu]; exact hout10
  have hNA11 : Native_assertLoaded σ11.mem := by rw [hmem11e]; exact hmem10e ▸ hNA10
  -- 0x80002e20: ld a4,8(a3) → x14 := LV1
  obtain ⟨σ12, i12, hs12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80002e20_na σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e20#64) vmi11 argsBase
      ab8 ab9 ab10 ab11 ab12 ab13 ab14 ab15 hG11 hpc11 hmi11 hx13_11 hNA11 rfl
      (by rw [hargsAddr8]; omega) (by rw [hargsAddr8]; omega)
      (by rw [hargsAddr8, htoh]; right; omega) (by rw [hargsAddr8]; omega)
      (by rw [hargsAddr8, hmem11e]; exact hab8) (by rw [hargsAddr8, hmem11e]; exact hab9)
      (by rw [hargsAddr8, hmem11e]; exact hab10) (by rw [hargsAddr8, hmem11e]; exact hab11)
      (by rw [hargsAddr8, hmem11e]; exact hab12) (by rw [hargsAddr8, hmem11e]; exact hab13)
      (by rw [hargsAddr8, hmem11e]; exact hab14) (by rw [hargsAddr8, hmem11e]; exact hab15) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs12'
  have hmem12e : σ12.mem = ms4 := by rw [hmem12]; exact hmem11e
  have hpc12 : σ12.regs.get? Register.PC = some (0x80002e24#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80002e20#64) 4 = (0x80002e24#64 : BitVec 64) from by decide] at this
  have hx14_12 : σ12.regs.get? Register.x14 = some LV1 := obs_alu_rd hobs12 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp12 := obs_alu_other' hobs12 Register.x2 (by decide) hsp11
  have hx10_12 := obs_alu_other' hobs12 Register.x10 (by decide) hx10_11
  have hx11_12 := obs_alu_other' hobs12 Register.x11 (by decide) hx11_11
  have hx13_12 := obs_alu_other' hobs12 Register.x13 (by decide) hx13_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hout12 : σ12.sailOutput = out0 := by rw [hobs12.out, sailOutput_sigmaPost_alu]; exact hout11
  have hNA12 : Native_assertLoaded σ12.mem := by rw [hmem12e]; exact hmem11e ▸ hNA11
  -- 0x80002e24: ld a5,16(a3) → x15 := LV2
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_80002e24_na σ12 i12 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e24#64) vmi12 argsBase
      ab16 ab17 ab18 ab19 ab20 ab21 ab22 ab23 hG12 hpc12 hmi12 hx13_12 hNA12 rfl
      (by rw [hargsAddr16]; omega) (by rw [hargsAddr16]; omega)
      (by rw [hargsAddr16, htoh]; right; omega) (by rw [hargsAddr16]; omega)
      (by rw [hargsAddr16, hmem12e]; exact hab16) (by rw [hargsAddr16, hmem12e]; exact hab17)
      (by rw [hargsAddr16, hmem12e]; exact hab18) (by rw [hargsAddr16, hmem12e]; exact hab19)
      (by rw [hargsAddr16, hmem12e]; exact hab20) (by rw [hargsAddr16, hmem12e]; exact hab21)
      (by rw [hargsAddr16, hmem12e]; exact hab22) (by rw [hargsAddr16, hmem12e]; exact hab23) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs13'
  have hmem13e : σ13.mem = ms4 := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x80002e28#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80002e24#64) 4 = (0x80002e28#64 : BitVec 64) from by decide] at this
  have hx15_13 : σ13.regs.get? Register.x15 = some LV2 := obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp13 := obs_alu_other' hobs13 Register.x2 (by decide) hsp12
  have hx10_13 := obs_alu_other' hobs13 Register.x10 (by decide) hx10_12
  have hx11_13 := obs_alu_other' hobs13 Register.x11 (by decide) hx11_12
  have hx14_13 := obs_alu_other' hobs13 Register.x14 (by decide) hx14_12
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hout13 : σ13.sailOutput = out0 := by rw [hobs13.out, sailOutput_sigmaPost_alu]; exact hout12
  have hNA13 : Native_assertLoaded σ13.mem := by rw [hmem13e]; exact hmem12e ▸ hNA12
  ------------------------------------------------------------------------
  -- mv s0 (e28), addi a0=buf (e2c), spill a2/a3 (e30/e34), copy stores e38/e3c/e40.
  ------------------------------------------------------------------------
  -- 0x80002e28: mv s0,a0 → x8 := sret
  obtain ⟨σ14, i14, hs14', hi14, hG14, hmem14, hobs14⟩ :=
    site_80002e28_na σ13 i13 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e28#64) vmi13 sret
      hG13 hpc13 hmi13 hx10_13 hNA13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs14'
  have hmem14e : σ14.mem = ms4 := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x80002e2c#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x80002e28#64) 4 = (0x80002e2c#64 : BitVec 64) from by decide] at this
  have hx8_14 : σ14.regs.get? Register.x8 = some sret := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have hsp14 := obs_alu_other' hobs14 Register.x2 (by decide) hsp13
  have hx11_14 := obs_alu_other' hobs14 Register.x11 (by decide) hx11_13
  have hx14_14 := obs_alu_other' hobs14 Register.x14 (by decide) hx14_13
  have hx15_14 := obs_alu_other' hobs14 Register.x15 (by decide) hx15_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hout14 : σ14.sailOutput = out0 := by rw [hobs14.out, sailOutput_sigmaPost_alu]; exact hout13
  have hNA14 : Native_assertLoaded σ14.mem := by rw [hmem14e]; exact hmem13e ▸ hNA13
  -- 0x80002e2c: addi a0,sp,16 → x10 := (fsp-80)+16 = fsp-64 (buffer)
  obtain ⟨σ15, i15, hs15', hi15, hG15, hmem15, hobs15⟩ :=
    site_80002e2c_na σ14 i14 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e2c#64) vmi14 (fsp - 80#64)
      hG14 hpc14 hmi14 hsp14 hNA14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs15'
  have hmem15e : σ15.mem = ms4 := by rw [hmem15]; exact hmem14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x80002e30#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x80002e2c#64) 4 = (0x80002e30#64 : BitVec 64) from by decide] at this
  have hx10_15 : σ15.regs.get? Register.x10 = some ((fsp - 80#64) + sign_extend (m := 64) (0x010#12)) :=
    obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hsp15 := obs_alu_other' hobs15 Register.x2 (by decide) hsp14
  have hx8_15 := obs_alu_other' hobs15 Register.x8 (by decide) hx8_14
  have hx11_15 := obs_alu_other' hobs15 Register.x11 (by decide) hx11_14
  have hx14_15 := obs_alu_other' hobs15 Register.x14 (by decide) hx14_14
  have hx15_15 := obs_alu_other' hobs15 Register.x15 (by decide) hx15_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hout15 : σ15.sailOutput = out0 := by rw [hobs15.out, sailOutput_sigmaPost_alu]; exact hout14
  have hNA15 : Native_assertLoaded σ15.mem := by rw [hmem15e]; exact hmem14e ▸ hNA14
  -- buffer memory tower (spills to fsp-72/fsp-80 + 3 copy stores to fsp-64/-56/-48)
  let mb1 : Mem := writeMap8 ms4 (fsp.toNat - 80 + 8) (sdData_val argc)
  let mb2 : Mem := writeMap8 mb1 (fsp.toNat - 80 + 0) (sdData_val argsBase)
  let mb3 : Mem := writeMap8 mb2 (fsp.toNat - 80 + 16) (sdData_val LV0)
  let mb4 : Mem := writeMap8 mb3 (fsp.toNat - 80 + 24) (sdData_val LV1)
  let mb5 : Mem := writeMap8 mb4 (fsp.toNat - 80 + 32) (sdData_val LV2)
  -- x12 = argc survived e08…e2c (those ALUs write x16/x15/x9/x18/x11/x14/x8/x10 only)
  have hx12_6 := obs_alu_other' hobs6 Register.x12 (by decide) hx12_5
  have hx12_7 := obs_alu_other' hobs7 Register.x12 (by decide) hx12_6
  have hx12_8 := obs_alu_other' hobs8 Register.x12 (by decide) hx12_7
  have hx12_9 := obs_alu_other' hobs9 Register.x12 (by decide) hx12_8
  have hx12_10 := obs_branch_nottaken_other' hobs10 Register.x12 (by decide) hx12_9
  have hx12_11 := obs_alu_other' hobs11 Register.x12 (by decide) hx12_10
  have hx12_12 := obs_alu_other' hobs12 Register.x12 (by decide) hx12_11
  have hx12_13 := obs_alu_other' hobs13 Register.x12 (by decide) hx12_12
  have hx12_14 := obs_alu_other' hobs14 Register.x12 (by decide) hx12_13
  have hx12_15 := obs_alu_other' hobs15 Register.x12 (by decide) hx12_14
  -- 0x80002e30: sd a2,8(sp) → mb1 (spill argc)
  obtain ⟨σ16, i16, hs16', hi16, hG16, hmem16, hobs16⟩ :=
    site_80002e30_na σ15 i15 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e30#64) vmi15 (fsp - 80#64) argc
      hG15 hpc15 hmi15 hsp15 hx12_15 hNA15 rfl
      (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi15
  have hstep16 : Step ⟨σ15, i15, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs16'
  have hmem16e : σ16.mem = mb1 := by rw [hmem16, mem_afterNextPC, haddr8, hmem15e]
  have hpc16 : σ16.regs.get? Register.PC = some (0x80002e34#64) := by
    have := obs_store_pc_val hobs16
    rwa [show BitVec.addInt (0x80002e30#64) 4 = (0x80002e34#64 : BitVec 64) from by decide] at this
  have hsp16 := obs_store_other_val' hobs16 Register.x2 (by decide) hsp15
  have hx8_16 := obs_store_other_val' hobs16 Register.x8 (by decide) hx8_15
  have hx10_16 := obs_store_other_val' hobs16 Register.x10 (by decide) hx10_15
  have hx11_16 := obs_store_other_val' hobs16 Register.x11 (by decide) hx11_15
  have hx14_16 := obs_store_other_val' hobs16 Register.x14 (by decide) hx14_15
  have hx15_16 := obs_store_other_val' hobs16 Register.x15 (by decide) hx15_15
  obtain ⟨vmi16, hmi16⟩ := obs_store_minstret_val hobs16
  have hout16 : σ16.sailOutput = out0 := by rw [hobs16.out, sailOutput_sigmaPost_store]; exact hout15
  have hNA16 : Native_assertLoaded σ16.mem := by
    rw [hmem16e]; exact loaded_na_writeMap8 ms4 _ _ (hcodeNA 8 (by omega)) (hmem15e ▸ hNA15)
  -- x13 = argsBase survived e24…e30
  have hx13_13 := obs_alu_other' hobs13 Register.x13 (by decide) hx13_12
  have hx13_14 := obs_alu_other' hobs14 Register.x13 (by decide) hx13_13
  have hx13_15 := obs_alu_other' hobs15 Register.x13 (by decide) hx13_14
  have hx13_16 := obs_store_other_val' hobs16 Register.x13 (by decide) hx13_15
  -- 0x80002e34: sd a3,0(sp) → mb2 (spill args base)
  obtain ⟨σ17, i17, hs17', hi17, hG17, hmem17, hobs17⟩ :=
    site_80002e34_na σ16 i16 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e34#64) vmi16 (fsp - 80#64) argsBase
      hG16 hpc16 hmi16 hsp16 hx13_16 hNA16 rfl
      (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi16
  have hstep17 : Step ⟨σ16, i16, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs17'
  have hmem17e : σ17.mem = mb2 := by rw [hmem17, mem_afterNextPC, haddr0, hmem16e]
  have hpc17 : σ17.regs.get? Register.PC = some (0x80002e38#64) := by
    have := obs_store_pc_val hobs17
    rwa [show BitVec.addInt (0x80002e34#64) 4 = (0x80002e38#64 : BitVec 64) from by decide] at this
  have hsp17 := obs_store_other_val' hobs17 Register.x2 (by decide) hsp16
  have hx8_17 := obs_store_other_val' hobs17 Register.x8 (by decide) hx8_16
  have hx10_17 := obs_store_other_val' hobs17 Register.x10 (by decide) hx10_16
  have hx11_17 := obs_store_other_val' hobs17 Register.x11 (by decide) hx11_16
  have hx14_17 := obs_store_other_val' hobs17 Register.x14 (by decide) hx14_16
  have hx15_17 := obs_store_other_val' hobs17 Register.x15 (by decide) hx15_16
  obtain ⟨vmi17, hmi17⟩ := obs_store_minstret_val hobs17
  have hout17 : σ17.sailOutput = out0 := by rw [hobs17.out, sailOutput_sigmaPost_store]; exact hout16
  have hNA17 : Native_assertLoaded σ17.mem := by
    rw [hmem17e]; exact loaded_na_writeMap8 mb1 _ _ (hcodeNA 0 (by omega)) (hmem16e ▸ hNA16)
  -- 0x80002e38: sd a1,16(sp) → mb3 (buffer word0)
  obtain ⟨σ18, i18, hs18', hi18, hG18, hmem18, hobs18⟩ :=
    site_80002e38_na σ17 i17 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e38#64) vmi17 (fsp - 80#64) LV0
      hG17 hpc17 hmi17 hsp17 hx11_17 hNA17 rfl
      (naStore_safe4 fsp.toNat _ 16 haddr16 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 16 haddr16 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 16 haddr16 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 16 haddr16 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi17
  have hstep18 : Step ⟨σ17, i17, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ18, i18, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs18'
  have hmem18e : σ18.mem = mb3 := by rw [hmem18, mem_afterNextPC, haddr16, hmem17e]
  have hpc18 : σ18.regs.get? Register.PC = some (0x80002e3c#64) := by
    have := obs_store_pc_val hobs18
    rwa [show BitVec.addInt (0x80002e38#64) 4 = (0x80002e3c#64 : BitVec 64) from by decide] at this
  have hsp18 := obs_store_other_val' hobs18 Register.x2 (by decide) hsp17
  have hx8_18 := obs_store_other_val' hobs18 Register.x8 (by decide) hx8_17
  have hx14_18 := obs_store_other_val' hobs18 Register.x14 (by decide) hx14_17
  have hx15_18 := obs_store_other_val' hobs18 Register.x15 (by decide) hx15_17
  obtain ⟨vmi18, hmi18⟩ := obs_store_minstret_val hobs18
  have hout18 : σ18.sailOutput = out0 := by rw [hobs18.out, sailOutput_sigmaPost_store]; exact hout17
  have hNA18 : Native_assertLoaded σ18.mem := by
    rw [hmem18e]; exact loaded_na_writeMap8 mb2 _ _ (hcodeNA 16 (by omega)) (hmem17e ▸ hNA17)
  -- 0x80002e3c: sd a4,24(sp) → mb4 (buffer word1)
  obtain ⟨σ19, i19, hs19', hi19, hG19, hmem19, hobs19⟩ :=
    site_80002e3c_na σ18 i18 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e3c#64) vmi18 (fsp - 80#64) LV1
      hG18 hpc18 hmi18 hsp18 hx14_18 hNA18 rfl
      (naStore_safe4 fsp.toNat _ 24 haddr24 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 24 haddr24 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 24 haddr24 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 24 haddr24 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi18
  have hstep19 : Step ⟨σ18, i18, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs19'
  have hmem19e : σ19.mem = mb4 := by rw [hmem19, mem_afterNextPC, haddr24, hmem18e]
  have hpc19 : σ19.regs.get? Register.PC = some (0x80002e40#64) := by
    have := obs_store_pc_val hobs19
    rwa [show BitVec.addInt (0x80002e3c#64) 4 = (0x80002e40#64 : BitVec 64) from by decide] at this
  have hsp19 := obs_store_other_val' hobs19 Register.x2 (by decide) hsp18
  have hx8_19 := obs_store_other_val' hobs19 Register.x8 (by decide) hx8_18
  have hx15_19 := obs_store_other_val' hobs19 Register.x15 (by decide) hx15_18
  obtain ⟨vmi19, hmi19⟩ := obs_store_minstret_val hobs19
  have hout19 : σ19.sailOutput = out0 := by rw [hobs19.out, sailOutput_sigmaPost_store]; exact hout18
  have hNA19 : Native_assertLoaded σ19.mem := by
    rw [hmem19e]; exact loaded_na_writeMap8 mb3 _ _ (hcodeNA 24 (by omega)) (hmem18e ▸ hNA18)
  -- 0x80002e40: sd a5,32(sp) → mb5 (buffer word2)
  obtain ⟨σ20, i20, hs20', hi20, hG20, hmem20, hobs20⟩ :=
    site_80002e40_na σ19 i19 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e40#64) vmi19 (fsp - 80#64) LV2
      hG19 hpc19 hmi19 hsp19 hx15_19 hNA19 rfl
      (naStore_safe4 fsp.toNat _ 32 haddr32 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 32 haddr32 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (naStore_safe4 fsp.toNat _ 32 haddr32 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.1
      (naStore_safe4 fsp.toNat _ 32 haddr32 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2 hi19
  have hstep20 : Step ⟨σ19, i19, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs20'
  have hmem20e : σ20.mem = mb5 := by rw [hmem20, mem_afterNextPC, haddr32, hmem19e]
  have hpc20 : σ20.regs.get? Register.PC = some (0x80002e44#64) := by
    have := obs_store_pc_val hobs20
    rwa [show BitVec.addInt (0x80002e40#64) 4 = (0x80002e44#64 : BitVec 64) from by decide] at this
  have hsp20 := obs_store_other_val' hobs20 Register.x2 (by decide) hsp19
  have hx8_20 := obs_store_other_val' hobs20 Register.x8 (by decide) hx8_19
  obtain ⟨vmi20, hmi20⟩ := obs_store_minstret_val hobs20
  have hout20 : σ20.sailOutput = out0 := by rw [hobs20.out, sailOutput_sigmaPost_store]; exact hout19
  have hNA20 : Native_assertLoaded σ20.mem := by
    rw [hmem20e]; exact loaded_na_writeMap8 mb4 _ _ (hcodeNA 32 (by omega)) (hmem19e ▸ hNA19)
  -- a0 (buffer) at σ20 = fsp-64
  have hbufNat : ((fsp - 80#64) + sign_extend (m := 64) (0x010#12)).toNat = fsp.toNat - 80 + 16 := haddr16
  have hx10_18 := obs_store_other_val' hobs18 Register.x10 (by decide) hx10_17
  have hx10_19 := obs_store_other_val' hobs19 Register.x10 (by decide) hx10_18
  have hx10_20 := obs_store_other_val' hobs20 Register.x10 (by decide) hx10_19
  have hbuftag : ((fsp - 80#64) + sign_extend (m := 64) (0x010#12)) = (fsp - 64#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [haddr16, BitVec.toNat_sub]
    have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
    rw [h64]; have := fsp.isLt; omega
  have hbuf64Nat : (fsp - 64#64 : BitVec 64).toNat = fsp.toNat - 64 := by
    rw [BitVec.toNat_sub]; have h64 : (64#64 : BitVec 64).toNat = 64 := by decide
    rw [h64]; have := fsp.isLt; omega
  have hx10_20' : σ20.regs.get? Register.x10 = some (fsp - 64#64) := by rw [hx10_20, hbuftag]
  ------------------------------------------------------------------------
  -- The buffer window [fsp-64, fsp-40) in mb5 copies argsBase[0..24) byte-for-byte.
  ------------------------------------------------------------------------
  -- mb5 outside the buffer window = mb2 (the two spill stores below fsp-64
  -- and everything before), and equals m0 outside [fsp-80, fsp+40).
  obtain ⟨eL00, eL01, eL02, eL03, eL04, eL05, eL06, eL07⟩ := sdData_sext_bytes ab0 ab1 ab2 ab3 ab4 ab5 ab6 ab7
  obtain ⟨eL10, eL11, eL12, eL13, eL14, eL15, eL16, eL17⟩ := sdData_sext_bytes ab8 ab9 ab10 ab11 ab12 ab13 ab14 ab15
  obtain ⟨eL20, eL21, eL22, eL23, eL24, eL25, eL26, eL27⟩ := sdData_sext_bytes ab16 ab17 ab18 ab19 ab20 ab21 ab22 ab23
  -- m0 versions of the argsBase byte facts (= ms4 facts, args window frame-disjoint)
  have habm0 : ∀ j : Nat, (hj : j < 24) → m0[argsBase.toNat + j]? = ms4[argsBase.toNat + j]? :=
    fun j hj => (hms4_args (argsBase.toNat + j) (by omega)).symm
  have hm00 := (habm0 0 (by decide)).trans hab0
  have hm01 := (habm0 1 (by decide)).trans hab1; have hm02 := (habm0 2 (by decide)).trans hab2
  have hm03 := (habm0 3 (by decide)).trans hab3; have hm04 := (habm0 4 (by decide)).trans hab4
  have hm05 := (habm0 5 (by decide)).trans hab5; have hm06 := (habm0 6 (by decide)).trans hab6
  have hm07 := (habm0 7 (by decide)).trans hab7; have hm08 := (habm0 8 (by decide)).trans hab8
  have hm09 := (habm0 9 (by decide)).trans hab9; have hm010 := (habm0 10 (by decide)).trans hab10
  have hm011 := (habm0 11 (by decide)).trans hab11; have hm012 := (habm0 12 (by decide)).trans hab12
  have hm013 := (habm0 13 (by decide)).trans hab13; have hm014 := (habm0 14 (by decide)).trans hab14
  have hm015 := (habm0 15 (by decide)).trans hab15; have hm016 := (habm0 16 (by decide)).trans hab16
  have hm017 := (habm0 17 (by decide)).trans hab17; have hm018 := (habm0 18 (by decide)).trans hab18
  have hm019 := (habm0 19 (by decide)).trans hab19; have hm020 := (habm0 20 (by decide)).trans hab20
  have hm021 := (habm0 21 (by decide)).trans hab21; have hm022 := (habm0 22 (by decide)).trans hab22
  have hm023 := (habm0 23 (by omega)).trans hab23
  -- window LV0 (bytes 0..7 at fsp-64): reads through the two later buffer stores.
  have hWL0 : ∀ o : Nat, o < 8 →
      mb5[fsp.toNat - 80 + 16 + o]? = (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[fsp.toNat - 80 + 16 + o]? := by
    intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 16 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 16 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  have hWL1 : ∀ o : Nat, o < 8 →
      mb5[fsp.toNat - 80 + 24 + o]? = (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[fsp.toNat - 80 + 24 + o]? := by
    intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 24 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  -- the 24 buffer bytes match argsBase's 24 bytes (mb5[fsp-64+j] = argsBase[j] byte).
  have hbufcopy : ∀ j, j < 24 → mb5[(fsp.toNat - 64) + j]? = m0[argsBase.toNat + j]? := by
    intro j hj
    have hrw : ∀ o, fsp.toNat - 64 + o = fsp.toNat - 80 + 16 + o := by intro o; omega
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
      with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · rw [hrw 0, show fsp.toNat-80+16+0 = fsp.toNat-80+16 from by omega, hWL0 0 (by omega),
        show fsp.toNat-80+16 = fsp.toNat-80+16+0 from by omega, getElem_writeMap8_0, eL00,
        show argsBase.toNat+0 = argsBase.toNat from by omega]; exact hm00.symm
    · rw [hrw 1, hWL0 1 (by omega), getElem_writeMap8_1, eL01]; exact hm01.symm
    · rw [hrw 2, hWL0 2 (by omega), getElem_writeMap8_2, eL02]; exact hm02.symm
    · rw [hrw 3, hWL0 3 (by omega), getElem_writeMap8_3, eL03]; exact hm03.symm
    · rw [hrw 4, hWL0 4 (by omega), getElem_writeMap8_4, eL04]; exact hm04.symm
    · rw [hrw 5, hWL0 5 (by omega), getElem_writeMap8_5, eL05]; exact hm05.symm
    · rw [hrw 6, hWL0 6 (by omega), getElem_writeMap8_6, eL06]; exact hm06.symm
    · rw [hrw 7, hWL0 7 (by omega), getElem_writeMap8_7, eL07]; exact hm07.symm
    · rw [reidxNat fsp.toNat 64 8 80 24 80 hfsp80 (by decide) (by decide) (by decide), hWL1 0 (by omega),
        show fsp.toNat-80+24+0 = fsp.toNat-80+24 from by omega, getElem_writeMap8_0, eL10,
        show argsBase.toNat+8 = argsBase.toNat+8 from rfl]; exact hm08.symm
    · rw [reidxNat fsp.toNat 64 9 80 25 80 hfsp80 (by decide) (by decide) (by decide), hWL1 1 (by omega), getElem_writeMap8_1, eL11]; exact hm09.symm
    · rw [reidxNat fsp.toNat 64 10 80 26 80 hfsp80 (by decide) (by decide) (by decide), hWL1 2 (by omega), getElem_writeMap8_2, eL12]; exact hm010.symm
    · rw [reidxNat fsp.toNat 64 11 80 27 80 hfsp80 (by decide) (by decide) (by decide), hWL1 3 (by omega), getElem_writeMap8_3, eL13]; exact hm011.symm
    · rw [reidxNat fsp.toNat 64 12 80 28 80 hfsp80 (by decide) (by decide) (by decide), hWL1 4 (by omega), getElem_writeMap8_4, eL14]; exact hm012.symm
    · rw [reidxNat fsp.toNat 64 13 80 29 80 hfsp80 (by decide) (by decide) (by decide), hWL1 5 (by omega), getElem_writeMap8_5, eL15]; exact hm013.symm
    · rw [reidxNat fsp.toNat 64 14 80 30 80 hfsp80 (by decide) (by decide) (by decide), hWL1 6 (by omega), getElem_writeMap8_6, eL16]; exact hm014.symm
    · rw [reidxNat fsp.toNat 64 15 80 31 80 hfsp80 (by decide) (by decide) (by decide), hWL1 7 (by omega), getElem_writeMap8_7, eL17]; exact hm015.symm
    · rw [reidxNat fsp.toNat 64 16 80 32 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_0, eL20]; exact hm016.symm
    · rw [reidxNat fsp.toNat 64 17 80 33 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_1, eL21]; exact hm017.symm
    · rw [reidxNat fsp.toNat 64 18 80 34 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_2, eL22]; exact hm018.symm
    · rw [reidxNat fsp.toNat 64 19 80 35 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_3, eL23]; exact hm019.symm
    · rw [reidxNat fsp.toNat 64 20 80 36 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_4, eL24]; exact hm020.symm
    · rw [reidxNat fsp.toNat 64 21 80 37 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_5, eL25]; exact hm021.symm
    · rw [reidxNat fsp.toNat 64 22 80 38 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_6, eL26]; exact hm022.symm
    · rw [reidxNat fsp.toNat 64 23 80 39 80 hfsp80 (by decide) (by decide) (by decide), getElem_writeMap8_7, eL27]; exact hm023.symm
  -- mb5 equals m0 outside the whole frame+buffer window [fsp-80, fsp+40)
  -- (every one of the 9 writes lands inside that window).
  have hbufout : ∀ a, (a < fsp.toNat - 80 ∨ fsp.toNat + 40 ≤ a) → mb5[a]? = m0[a]? := by
    intro a ha
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) a (sdData_val LV2) (winStore_disjoint fsp.toNat a 32 ha hfsp80 (by decide))]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) a (sdData_val LV1) (winStore_disjoint fsp.toNat a 24 ha hfsp80 (by decide))]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) a (sdData_val LV0) (winStore_disjoint fsp.toNat a 16 ha hfsp80 (by decide))]
    show (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint mb1 (fsp.toNat-80+0) a (sdData_val argsBase) (winStore_disjoint fsp.toNat a 0 ha hfsp80 (by decide))]
    show (writeMap8 ms4 (fsp.toNat-80+8) (sdData_val argc))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms4 (fsp.toNat-80+8) a (sdData_val argc) (winStore_disjoint fsp.toNat a 8 ha hfsp80 (by decide))]
    show (writeMap8 ms3 (fsp.toNat-80+64) (sdData_val s0v))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms3 (fsp.toNat-80+64) a (sdData_val s0v) (winStore_disjoint fsp.toNat a 64 ha hfsp80 (by decide))]
    show (writeMap8 ms2 (fsp.toNat-80+72) (sdData_val retAddr))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms2 (fsp.toNat-80+72) a (sdData_val retAddr) (winStore_disjoint fsp.toNat a 72 ha hfsp80 (by decide))]
    show (writeMap8 ms1 (fsp.toNat-80+48) (sdData_val s2v))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint ms1 (fsp.toNat-80+48) a (sdData_val s2v) (winStore_disjoint fsp.toNat a 48 ha hfsp80 (by decide))]
    show (writeMap8 c.σ.mem (fsp.toNat-80+56) (sdData_val s1v))[a]? = m0[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (fsp.toNat-80+56) a (sdData_val s1v) (winStore_disjoint fsp.toNat a 56 ha hfsp80 (by decide)), hmem]
  -- payload AgreeP: the arena string (disjoint from the frame+buffer window) is preserved
  have hbufpay : ∀ (p : Nat) (s : String), read64 m0 (argsBase.toNat + 8) = some p →
      AgreeP (fun a => ∃ k, k ≤ s.length ∧ a = p + k) m0 mb5 := by
    intro p s hp a ha
    obtain ⟨k, hk, rfl⟩ := ha
    exact (hbufout (p + k) (hpayDisj p s hp k hk)).symm
  have hbufRepr : ValueRepr mb5 N φc (fsp.toNat - 64) v :=
    valueRepr_copy (srcAddr := argsBase.toNat) (dstAddr := fsp.toNat - 64)
      hbufcopy hbufpay (hmem ▸ hvRepr)
  have hbufRepr' : ValueRepr mb5 N φc (fsp - 64#64).toNat v := by rw [hbuf64Nat]; exact hbufRepr
  ------------------------------------------------------------------------
  -- 0x80002e44: jal value_truthy → PC := value_truthy, ra := 0x80002e48
  ------------------------------------------------------------------------
  -- code regions loaded in mb5 (via agreement on the code, disjoint from window)
  have hVT_mb5 : Value_truthyLoaded mb5 :=
    loaded_truthy_agreeP c.σ.mem mb5 (fun a ha => hmem ▸ (hbufout a (by rcases hRG.frame_vt with h|h <;> omega)).symm) hVT
  have hVN_mb5 : Value_nullLoaded mb5 :=
    loaded_null_agreeP c.σ.mem mb5 (fun a ha => hmem ▸ (hbufout a (by rcases hRG.frame_vn with h|h <;> omega)).symm) hVN
  -- 0x80002e44: jal value_truthy
  obtain ⟨σ21, i21, hs21', hi21, hG21, hmem21, hobs21⟩ :=
    site_80002e44_na σ20 i20 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e44#64) vmi20
      hG20 hpc20 hmi20 hNA20 rfl hi20
  have hstep21 : Step ⟨σ20, i20, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ21, i21, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs21'
  have hmem21e : σ21.mem = mb5 := by rw [hmem21]; exact hmem20e
  have hpc21 : σ21.regs.get? Register.PC = some (0x8000282c#64) := by
    have := obs_jal_pc hobs21
    rwa [show ((0x80002e44#64 : BitVec 64) + sign_extend (m := 64) (0x1ff9e8#21)) = 0x8000282c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink21 : σ21.regs.get? Register.x1 = some (0x80002e48#64) := by
    have := obs_jal_rd hobs21 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002e44#64 : BitVec 64) 4 = (0x80002e48#64:BitVec 64) from by decide] at this
  have hx10_21 : σ21.regs.get? Register.x10 = some (fsp - 64#64) := by
    rw [obs_jal_other' hobs21 Register.x10 (by decide) hx10_20, hbuftag]
  have hx8_21 : σ21.regs.get? Register.x8 = some sret := obs_jal_other' hobs21 Register.x8 (by decide) hx8_20
  have hsp21 : σ21.regs.get? Register.x2 = some (fsp - 80#64) := obs_jal_other' hobs21 Register.x2 (by decide) hsp20
  obtain ⟨vmi21, hmi21⟩ := obs_jal_minstret hobs21
  have hout21 : σ21.sailOutput = out0 := by rw [hobs21.out, sailOutput_sigmaPost_jal]; exact hout20
  -- TruthyRegion for the buffer (fsp-64)
  have hTruthyReg : TruthyRegion (fsp - 64#64) :=
    ⟨by rw [hbuf64Nat]; have := hRG.fsp_align; omega, by rw [hbuf64Nat]; have := hRG.fsp_lo; omega,
     by rw [hbuf64Nat]; have := hRG.fsp_hi; omega, by rw [hbuf64Nat]; have := hRG.fsp_win; omega⟩
  have hrettgt_t : (BitVec.update ((0x80002e48#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  ------------------------------------------------------------------------
  -- value_truthy callee (value_truthy_spec), buf = fsp-64, ra = 0x80002e48
  ------------------------------------------------------------------------
  obtain ⟨cT, hsT, hGT, hpcT, ha0T, hraT, ⟨vmiT, hmiT⟩, htickT, hmemT, houtT, hframeT⟩ :=
    value_truthy_spec (fun R => σ21.regs.get? R) (fsp - 64#64) (0x80002e48#64) N φc v mb5 out0
      ⟨σ21, i21, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG21, hmem21e ▸ hVT_mb5, hmem21e, hpc21, hx10_21, hlink21, ⟨vmi21, hmi21⟩, hi21,
        hmem21e ▸ hbufRepr', hTruthyReg, hrettgt_t, hout21, fun R _ => rfl⟩
  have hmemT' : cT.σ.mem = mb5 := hmemT
  have hpcT' : cT.σ.regs.get? Register.PC = some (0x80002e48#64) := by
    rw [hpcT, show (BitVec.update ((0x80002e48#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x80002e48#64 from by apply BitVec.eq_of_toNat_eq; decide]
  -- value_truthy returns a0 = cond v.truthy 1 0 = 1 (since v.truthy = true)
  have ha0T' : cT.σ.regs.get? Register.x10 = some (1#64) := by
    rw [ha0T, htruthy]; rfl
  have hs0_T : cT.σ.regs.get? Register.x8 = some sret := by
    rw [hframeT Register.x8 (by decide)]; exact hx8_21
  have hsp_T : cT.σ.regs.get? Register.x2 = some (fsp - 80#64) := by
    rw [hframeT Register.x2 (by decide)]; exact hsp21
  have hNA_T : Native_assertLoaded cT.σ.mem := by
    rw [hmemT']; exact loaded_na_agreeP c.σ.mem mb5 (fun a ha => hmem ▸ (hbufout a (by rcases hRG.frame_na with h|h <;> omega)).symm) hNA
  have hVN_T : Value_nullLoaded cT.σ.mem := by rw [hmemT']; exact hVN_mb5
  ------------------------------------------------------------------------
  -- reloads e48/e4c (dead argsBase/argc), beqz e50 (NOT taken), mv a0 e54.
  ------------------------------------------------------------------------
  -- presence of the two reload words in mb5 (they read through disjoint later stores)
  -- mb5 at the two dead-reload words reads through the disjoint later stores to
  -- the spill store, so those bytes are present.
  have hmb5_lo : ∀ o : Nat, o < 8 → mb5[fsp.toNat - 80 + 0 + o]? = (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[fsp.toNat - 80 + 0 + o]? := by
    intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 0 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 0 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[_]? = _
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) _ (sdData_val LV0) (slotStore_disjoint fsp.toNat 0 o 16 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  have hmb5_hi : ∀ o : Nat, o < 8 → mb5[fsp.toNat - 80 + 8 + o]? = (writeMap8 ms4 (fsp.toNat-80+8) (sdData_val argc))[fsp.toNat - 80 + 8 + o]? := by
    intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 8 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 8 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[_]? = _
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) _ (sdData_val LV0) (slotStore_disjoint fsp.toNat 8 o 16 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[_]? = _
    rw [getElem_writeMap8_disjoint mb1 (fsp.toNat-80+0) _ (sdData_val argsBase) (slotStore_disjoint fsp.toNat 8 o 0 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  have hpres_lo : ∀ o : Nat, o < 8 → ∃ b, mb5[fsp.toNat - 80 + 0 + o]? = some b := by
    intro o ho
    rcases (show o=0∨o=1∨o=2∨o=3∨o=4∨o=5∨o=6∨o=7 from by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨_, (hmb5_lo 0 (by omega)).trans (by rw [show fsp.toNat-80+0+0 = fsp.toNat-80+0 from rfl, getElem_writeMap8_0])⟩
    · exact ⟨_, (hmb5_lo 1 (by omega)).trans (by rw [getElem_writeMap8_1])⟩
    · exact ⟨_, (hmb5_lo 2 (by omega)).trans (by rw [getElem_writeMap8_2])⟩
    · exact ⟨_, (hmb5_lo 3 (by omega)).trans (by rw [getElem_writeMap8_3])⟩
    · exact ⟨_, (hmb5_lo 4 (by omega)).trans (by rw [getElem_writeMap8_4])⟩
    · exact ⟨_, (hmb5_lo 5 (by omega)).trans (by rw [getElem_writeMap8_5])⟩
    · exact ⟨_, (hmb5_lo 6 (by omega)).trans (by rw [getElem_writeMap8_6])⟩
    · exact ⟨_, (hmb5_lo 7 (by omega)).trans (by rw [getElem_writeMap8_7])⟩
  have hpres_hi : ∀ o : Nat, o < 8 → ∃ b, mb5[fsp.toNat - 80 + 8 + o]? = some b := by
    intro o ho
    rcases (show o=0∨o=1∨o=2∨o=3∨o=4∨o=5∨o=6∨o=7 from by omega) with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact ⟨_, (hmb5_hi 0 (by omega)).trans (by rw [show fsp.toNat-80+8+0 = fsp.toNat-80+8 from rfl, getElem_writeMap8_0])⟩
    · exact ⟨_, (hmb5_hi 1 (by omega)).trans (by rw [getElem_writeMap8_1])⟩
    · exact ⟨_, (hmb5_hi 2 (by omega)).trans (by rw [getElem_writeMap8_2])⟩
    · exact ⟨_, (hmb5_hi 3 (by omega)).trans (by rw [getElem_writeMap8_3])⟩
    · exact ⟨_, (hmb5_hi 4 (by omega)).trans (by rw [getElem_writeMap8_4])⟩
    · exact ⟨_, (hmb5_hi 5 (by omega)).trans (by rw [getElem_writeMap8_5])⟩
    · exact ⟨_, (hmb5_hi 6 (by omega)).trans (by rw [getElem_writeMap8_6])⟩
    · exact ⟨_, (hmb5_hi 7 (by omega)).trans (by rw [getElem_writeMap8_7])⟩
  obtain ⟨rl0, hrl0⟩ := hpres_lo 0 (by omega); obtain ⟨rl1, hrl1⟩ := hpres_lo 1 (by omega)
  obtain ⟨rl2, hrl2⟩ := hpres_lo 2 (by omega); obtain ⟨rl3, hrl3⟩ := hpres_lo 3 (by omega)
  obtain ⟨rl4, hrl4⟩ := hpres_lo 4 (by omega); obtain ⟨rl5, hrl5⟩ := hpres_lo 5 (by omega)
  obtain ⟨rl6, hrl6⟩ := hpres_lo 6 (by omega); obtain ⟨rl7, hrl7⟩ := hpres_lo 7 (by omega)
  obtain ⟨rh0, hrh0⟩ := hpres_hi 0 (by omega); obtain ⟨rh1, hrh1⟩ := hpres_hi 1 (by omega)
  obtain ⟨rh2, hrh2⟩ := hpres_hi 2 (by omega); obtain ⟨rh3, hrh3⟩ := hpres_hi 3 (by omega)
  obtain ⟨rh4, hrh4⟩ := hpres_hi 4 (by omega); obtain ⟨rh5, hrh5⟩ := hpres_hi 5 (by omega)
  obtain ⟨rh6, hrh6⟩ := hpres_hi 6 (by omega); obtain ⟨rh7, hrh7⟩ := hpres_hi 7 (by omega)
  -- 0x80002e48: ld a3,0(sp) → x13 (dead)
  obtain ⟨σ22, i22, hs22', hi22, hG22, hmem22, hobs22⟩ :=
    site_80002e48_na cT.σ cT.tick cT.steps (0x80002e48#64) vmiT (fsp - 80#64)
      rl0 rl1 rl2 rl3 rl4 rl5 rl6 rl7 hGT hpcT' hmiT hsp_T (hmemT' ▸ hNA_T) rfl
      (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (by rw [haddr0, htoh]; right; omega) (naStore_safe4 fsp.toNat _ 0 haddr0 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2
      (by rw [haddr0, hmemT']; exact hrl0) (by rw [haddr0, hmemT']; exact hrl1)
      (by rw [haddr0, hmemT']; exact hrl2) (by rw [haddr0, hmemT']; exact hrl3)
      (by rw [haddr0, hmemT']; exact hrl4) (by rw [haddr0, hmemT']; exact hrl5)
      (by rw [haddr0, hmemT']; exact hrl6) (by rw [haddr0, hmemT']; exact hrl7) htickT
  have hstep22 : Step cT ⟨σ22, i22, cT.steps + 1⟩ := by cases cT; exact hs22'
  have hmem22e : σ22.mem = mb5 := by rw [hmem22]; exact hmemT'
  have hpc22 : σ22.regs.get? Register.PC = some (0x80002e4c#64) := by
    have := obs_alu_pc hobs22
    rwa [show BitVec.addInt (0x80002e48#64) 4 = (0x80002e4c#64 : BitVec 64) from by decide] at this
  have ha0_22 : σ22.regs.get? Register.x10 = some (1#64) := obs_alu_other' hobs22 Register.x10 (by decide) ha0T'
  have hs0_22 : σ22.regs.get? Register.x8 = some sret := obs_alu_other' hobs22 Register.x8 (by decide) hs0_T
  have hsp_22 : σ22.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs22 Register.x2 (by decide) hsp_T
  obtain ⟨vmi22, hmi22⟩ := obs_alu_minstret hobs22
  have hout22 : σ22.sailOutput = out0 := by rw [hobs22.out, sailOutput_sigmaPost_alu]; exact houtT
  have hNA22 : Native_assertLoaded σ22.mem := by rw [hmem22e]; exact hmemT' ▸ hNA_T
  have hVN22 : Value_nullLoaded σ22.mem := by rw [hmem22e]; exact hVN_mb5
  -- 0x80002e4c: ld a2,8(sp) → x12 (dead)
  obtain ⟨σ23, i23, hs23', hi23, hG23, hmem23, hobs23⟩ :=
    site_80002e4c_na σ22 i22 (cT.steps + 1) (0x80002e4c#64) vmi22 (fsp - 80#64)
      rh0 rh1 rh2 rh3 rh4 rh5 rh6 rh7 hG22 hpc22 hmi22 hsp_22 hNA22 rfl
      (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).1 (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.1
      (by rw [haddr8, htoh]; right; omega) (naStore_safe4 fsp.toNat _ 8 haddr8 (by decide) (by decide) hRG.fsp_align hRG.fsp_lo hRG.fsp_hi hRG.fsp_win).2.2.2
      (by rw [haddr8, hmem22e]; exact hrh0) (by rw [haddr8, hmem22e]; exact hrh1)
      (by rw [haddr8, hmem22e]; exact hrh2) (by rw [haddr8, hmem22e]; exact hrh3)
      (by rw [haddr8, hmem22e]; exact hrh4) (by rw [haddr8, hmem22e]; exact hrh5)
      (by rw [haddr8, hmem22e]; exact hrh6) (by rw [haddr8, hmem22e]; exact hrh7) hi22
  have hstep23 : Step ⟨σ22, i22, cT.steps + 1⟩ ⟨σ23, i23, cT.steps + 1 + 1⟩ := hs23'
  have hmem23e : σ23.mem = mb5 := by rw [hmem23]; exact hmem22e
  have hpc23 : σ23.regs.get? Register.PC = some (0x80002e50#64) := by
    have := obs_alu_pc hobs23
    rwa [show BitVec.addInt (0x80002e4c#64) 4 = (0x80002e50#64 : BitVec 64) from by decide] at this
  have ha0_23 : σ23.regs.get? Register.x10 = some (1#64) := obs_alu_other' hobs23 Register.x10 (by decide) ha0_22
  have hs0_23 : σ23.regs.get? Register.x8 = some sret := obs_alu_other' hobs23 Register.x8 (by decide) hs0_22
  have hsp_23 : σ23.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs23 Register.x2 (by decide) hsp_22
  obtain ⟨vmi23, hmi23⟩ := obs_alu_minstret hobs23
  have hout23 : σ23.sailOutput = out0 := by rw [hobs23.out, sailOutput_sigmaPost_alu]; exact hout22
  have hNA23 : Native_assertLoaded σ23.mem := by rw [hmem23e]; exact hmem22e ▸ hNA22
  have hVN23 : Value_nullLoaded σ23.mem := by rw [hmem23e]; exact hVN_mb5
  -- 0x80002e50: beqz a0 (a0=1≠0, NOT taken) → 0x80002e54
  obtain ⟨σ24, i24, hs24', hi24, hG24, hmem24, hobs24⟩ :=
    site_80002e50_nottaken_na σ23 i23 (cT.steps + 1 + 1) (0x80002e50#64) vmi23 (1#64)
      hG23 hpc23 hmi23 ha0_23 hNA23 rfl (by decide) hi23
  have hstep24 : Step ⟨σ23, i23, cT.steps + 1 + 1⟩ ⟨σ24, i24, cT.steps + 1 + 1 + 1⟩ := hs24'
  have hmem24e : σ24.mem = mb5 := by rw [hmem24]; exact hmem23e
  have hpc24 : σ24.regs.get? Register.PC = some (0x80002e54#64) := by
    have := obs_branch_nottaken_pc hobs24
    rwa [show BitVec.addInt (0x80002e50#64) 4 = (0x80002e54#64 : BitVec 64) from by decide] at this
  have hs0_24 : σ24.regs.get? Register.x8 = some sret := obs_branch_nottaken_other' hobs24 Register.x8 (by decide) hs0_23
  have hsp_24 : σ24.regs.get? Register.x2 = some (fsp - 80#64) := obs_branch_nottaken_other' hobs24 Register.x2 (by decide) hsp_23
  obtain ⟨vmi24, hmi24⟩ := obs_branch_nottaken_minstret hobs24
  have hout24 : σ24.sailOutput = out0 := by rw [hobs24.out, sailOutput_sigmaPost_branch_nottaken]; exact hout23
  have hNA24 : Native_assertLoaded σ24.mem := by rw [hmem24e]; exact hmem23e ▸ hNA23
  have hVN24 : Value_nullLoaded σ24.mem := by rw [hmem24e]; exact hVN_mb5
  -- 0x80002e54: mv a0,s0 → x10 := sret
  obtain ⟨σ25, i25, hs25', hi25, hG25, hmem25, hobs25⟩ :=
    site_80002e54_na σ24 i24 (cT.steps + 1 + 1 + 1) (0x80002e54#64) vmi24 sret
      hG24 hpc24 hmi24 hs0_24 hNA24 rfl hi24
  have hstep25 : Step ⟨σ24, i24, cT.steps + 1 + 1 + 1⟩ ⟨σ25, i25, cT.steps + 1 + 1 + 1 + 1⟩ := hs25'
  have hmem25e : σ25.mem = mb5 := by rw [hmem25]; exact hmem24e
  have hpc25 : σ25.regs.get? Register.PC = some (0x80002e58#64) := by
    have := obs_alu_pc hobs25
    rwa [show BitVec.addInt (0x80002e54#64) 4 = (0x80002e58#64 : BitVec 64) from by decide] at this
  have ha0_25 : σ25.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs25 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]] at this
  have hs0_25 : σ25.regs.get? Register.x8 = some sret := obs_alu_other' hobs25 Register.x8 (by decide) hs0_24
  have hsp_25 : σ25.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs25 Register.x2 (by decide) hsp_24
  obtain ⟨vmi25, hmi25⟩ := obs_alu_minstret hobs25
  have hout25 : σ25.sailOutput = out0 := by rw [hobs25.out, sailOutput_sigmaPost_alu]; exact hout24
  have hNA25 : Native_assertLoaded σ25.mem := by rw [hmem25e]; exact hmem24e ▸ hNA24
  have hVN25 : Value_nullLoaded σ25.mem := by rw [hmem25e]; exact hVN_mb5
  ------------------------------------------------------------------------
  -- 0x80002e58: jal value_null → PC := value_null, ra := 0x80002e5c
  ------------------------------------------------------------------------
  obtain ⟨σ26, i26, hs26', hi26, hG26, hmem26, hobs26⟩ :=
    site_80002e58_na σ25 i25 (cT.steps + 1 + 1 + 1 + 1) (0x80002e58#64) vmi25 hG25 hpc25 hmi25 hNA25 rfl hi25
  have hstep26 : Step ⟨σ25, i25, cT.steps + 1 + 1 + 1 + 1⟩ ⟨σ26, i26, cT.steps + 1 + 1 + 1 + 1 + 1⟩ := hs26'
  have hmem26e : σ26.mem = mb5 := by rw [hmem26]; exact hmem25e
  have hpc26 : σ26.regs.get? Register.PC = some (0x800027ec#64) := by
    have := obs_jal_pc hobs26
    rwa [show ((0x80002e58#64 : BitVec 64) + sign_extend (m := 64) (0x1ff994#21)) = 0x800027ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink26 : σ26.regs.get? Register.x1 = some (0x80002e5c#64) := by
    have := obs_jal_rd hobs26 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80002e58#64 : BitVec 64) 4 = (0x80002e5c#64:BitVec 64) from by decide] at this
  have ha0_26 : σ26.regs.get? Register.x10 = some sret := obs_jal_other' hobs26 Register.x10 (by decide) ha0_25
  have hs0_26 : σ26.regs.get? Register.x8 = some sret := obs_jal_other' hobs26 Register.x8 (by decide) hs0_25
  have hsp_26 : σ26.regs.get? Register.x2 = some (fsp - 80#64) := obs_jal_other' hobs26 Register.x2 (by decide) hsp_25
  obtain ⟨vmi26, hmi26⟩ := obs_jal_minstret hobs26
  have hout26 : σ26.sailOutput = out0 := by rw [hobs26.out, sailOutput_sigmaPost_jal]; exact hout25
  have hNullReg : NullRegion sret :=
    ⟨hRG.sret_align, hRG.sret_lo, hRG.sret_hi, hRG.sret_win, hRG.sret_vn⟩
  have hrettgt_n : (BitVec.update ((0x80002e5c#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  ------------------------------------------------------------------------
  -- value_null callee (value_null_spec), buf = sret, ra = 0x80002e5c
  ------------------------------------------------------------------------
  obtain ⟨cN, hsN, hGN, hpcN, ha0N, hraN, ⟨vmiN, hmiN⟩, htickN, hvalNull, houtN, hmemframeN, hframeN, _hpresN⟩ :=
    value_null_spec_full (fun R => σ26.regs.get? R) sret (0x80002e5c#64) N φc mb5 out0
      ⟨σ26, i26, cT.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG26, hmem26e ▸ hVN_mb5, hmem26e, hpc26, ha0_26, hlink26, ⟨vmi26, hmi26⟩, hi26,
        hNullReg, hrettgt_n, hout26, fun R _ => rfl⟩
  have hpcN' : cN.σ.regs.get? Register.PC = some (0x80002e5c#64) := by
    rw [hpcN, show (BitVec.update ((0x80002e5c#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x80002e5c#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hs0_N : cN.σ.regs.get? Register.x8 = some sret := by
    rw [hframeN Register.x8 (by decide)]; exact hs0_26
  have hsp_N : cN.σ.regs.get? Register.x2 = some (fsp - 80#64) := by
    rw [hframeN Register.x2 (by decide)]; exact hsp_26
  ------------------------------------------------------------------------
  -- The four frame spills survive into cN.σ.mem: read64 = the stored value.
  -- In mb5 each spill reads through the disjoint later stores to its writeMap8.
  ------------------------------------------------------------------------
  have hsdid : ∀ w : BitVec 64, (sdData_val w).toNat = w.toNat := fun w => by rw [sdData_val_id]
  -- read64 mb5 at each spill slot (reading through disjoint later writes)
  have hread_spill : ∀ (off : Nat) (w : BitVec 64) (M : Mem),
      -- mb5 agrees with the writeMap8 store on [fsp-80+off, +8)
      (∀ o, o < 8 → mb5[fsp.toNat - 80 + off + o]? = (writeMap8 M (fsp.toNat-80+off) (sdData_val w))[fsp.toNat - 80 + off + o]?) →
      read64 mb5 (fsp.toNat - 80 + off) = some w.toNat := by
    intro off w M hag
    have hAg : AgreeP (fun k => fsp.toNat-80+off ≤ k ∧ k < fsp.toNat-80+off+8)
        (writeMap8 M (fsp.toNat-80+off) (sdData_val w)) mb5 := by
      intro k hk
      have : k = fsp.toNat-80+off + (k - (fsp.toNat-80+off)) := by omega
      rw [this]; exact (hag (k - (fsp.toNat-80+off)) (by omega)).symm
    rw [← read64_agreeP hAg (fun j hj => ⟨by omega, by omega⟩)]
    rw [read64_writeMap8, sdData_val_id]
  -- ra@fsp-8 (= fsp-80+72), s0@fsp-16 (=+64), s1@fsp-24 (=+56), s2@fsp-32 (=+48)
  have hraM : read64 mb5 (fsp.toNat - 80 + 72) = some retAddr.toNat := by
    apply hread_spill 72 retAddr ms2; intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 72 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 72 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[_]? = _
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) _ (sdData_val LV0) (slotStore_disjoint fsp.toNat 72 o 16 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[_]? = _
    rw [getElem_writeMap8_disjoint mb1 (fsp.toNat-80+0) _ (sdData_val argsBase) (slotStore_disjoint fsp.toNat 72 o 0 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms4 (fsp.toNat-80+8) (sdData_val argc))[_]? = _
    rw [getElem_writeMap8_disjoint ms4 (fsp.toNat-80+8) _ (sdData_val argc) (slotStore_disjoint fsp.toNat 72 o 8 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms3 (fsp.toNat-80+64) (sdData_val s0v))[_]? = _
    rw [getElem_writeMap8_disjoint ms3 (fsp.toNat-80+64) _ (sdData_val s0v) (slotStore_disjoint fsp.toNat 72 o 64 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  have hs0M : read64 mb5 (fsp.toNat - 80 + 64) = some s0v.toNat := by
    apply hread_spill 64 s0v ms3; intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 64 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 64 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[_]? = _
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) _ (sdData_val LV0) (slotStore_disjoint fsp.toNat 64 o 16 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[_]? = _
    rw [getElem_writeMap8_disjoint mb1 (fsp.toNat-80+0) _ (sdData_val argsBase) (slotStore_disjoint fsp.toNat 64 o 0 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms4 (fsp.toNat-80+8) (sdData_val argc))[_]? = _
    rw [getElem_writeMap8_disjoint ms4 (fsp.toNat-80+8) _ (sdData_val argc) (slotStore_disjoint fsp.toNat 64 o 8 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  have hs1M : read64 mb5 (fsp.toNat - 80 + 56) = some s1v.toNat := by
    apply hread_spill 56 s1v c.σ.mem; intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 56 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 56 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[_]? = _
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) _ (sdData_val LV0) (slotStore_disjoint fsp.toNat 56 o 16 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[_]? = _
    rw [getElem_writeMap8_disjoint mb1 (fsp.toNat-80+0) _ (sdData_val argsBase) (slotStore_disjoint fsp.toNat 56 o 0 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms4 (fsp.toNat-80+8) (sdData_val argc))[_]? = _
    rw [getElem_writeMap8_disjoint ms4 (fsp.toNat-80+8) _ (sdData_val argc) (slotStore_disjoint fsp.toNat 56 o 8 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms3 (fsp.toNat-80+64) (sdData_val s0v))[_]? = _
    rw [getElem_writeMap8_disjoint ms3 (fsp.toNat-80+64) _ (sdData_val s0v) (slotStore_disjoint fsp.toNat 56 o 64 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms2 (fsp.toNat-80+72) (sdData_val retAddr))[_]? = _
    rw [getElem_writeMap8_disjoint ms2 (fsp.toNat-80+72) _ (sdData_val retAddr) (slotStore_disjoint fsp.toNat 56 o 72 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms1 (fsp.toNat-80+48) (sdData_val s2v))[_]? = _
    rw [getElem_writeMap8_disjoint ms1 (fsp.toNat-80+48) _ (sdData_val s2v) (slotStore_disjoint fsp.toNat 56 o 48 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  have hs2M : read64 mb5 (fsp.toNat - 80 + 48) = some s2v.toNat := by
    apply hread_spill 48 s2v ms1; intro o ho
    show (writeMap8 mb4 (fsp.toNat-80+32) (sdData_val LV2))[_]? = _
    rw [getElem_writeMap8_disjoint mb4 (fsp.toNat-80+32) _ (sdData_val LV2) (slotStore_disjoint fsp.toNat 48 o 32 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb3 (fsp.toNat-80+24) (sdData_val LV1))[_]? = _
    rw [getElem_writeMap8_disjoint mb3 (fsp.toNat-80+24) _ (sdData_val LV1) (slotStore_disjoint fsp.toNat 48 o 24 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb2 (fsp.toNat-80+16) (sdData_val LV0))[_]? = _
    rw [getElem_writeMap8_disjoint mb2 (fsp.toNat-80+16) _ (sdData_val LV0) (slotStore_disjoint fsp.toNat 48 o 16 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 mb1 (fsp.toNat-80+0) (sdData_val argsBase))[_]? = _
    rw [getElem_writeMap8_disjoint mb1 (fsp.toNat-80+0) _ (sdData_val argsBase) (slotStore_disjoint fsp.toNat 48 o 0 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms4 (fsp.toNat-80+8) (sdData_val argc))[_]? = _
    rw [getElem_writeMap8_disjoint ms4 (fsp.toNat-80+8) _ (sdData_val argc) (slotStore_disjoint fsp.toNat 48 o 8 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms3 (fsp.toNat-80+64) (sdData_val s0v))[_]? = _
    rw [getElem_writeMap8_disjoint ms3 (fsp.toNat-80+64) _ (sdData_val s0v) (slotStore_disjoint fsp.toNat 48 o 64 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
    show (writeMap8 ms2 (fsp.toNat-80+72) (sdData_val retAddr))[_]? = _
    rw [getElem_writeMap8_disjoint ms2 (fsp.toNat-80+72) _ (sdData_val retAddr) (slotStore_disjoint fsp.toNat 48 o 72 ho (by decide) (by decide) (by decide) (by decide) (by decide) hfsp80)]
  -- cN.σ.mem = mb5 outside [sret, sret+24) (value_null carve-out); the four spills
  -- live in [fsp-80, fsp), disjoint via sret_frame.
  have hcN_spill : ∀ k : Nat, (fsp.toNat - 80 ≤ k ∧ k < fsp.toNat) → cN.σ.mem[k]? = mb5[k]? := by
    intro k hk
    exact (hmemframeN k (by rcases hRG.sret_frame with h|h <;> omega)).symm
  have hraN' : read64 cN.σ.mem (fsp.toNat - 80 + 72) = some retAddr.toNat := by
    rw [read64_agreeP (P := fun a => fsp.toNat-80 ≤ a ∧ a < fsp.toNat) (m := cN.σ.mem) (m' := mb5)
      (fun k hk => hcN_spill k hk) (fun j hj => ⟨by omega, by omega⟩)]; exact hraM
  have hs0N' : read64 cN.σ.mem (fsp.toNat - 80 + 64) = some s0v.toNat := by
    rw [read64_agreeP (P := fun a => fsp.toNat-80 ≤ a ∧ a < fsp.toNat) (m := cN.σ.mem) (m' := mb5)
      (fun k hk => hcN_spill k hk) (fun j hj => ⟨by omega, by omega⟩)]; exact hs0M
  have hs1N' : read64 cN.σ.mem (fsp.toNat - 80 + 56) = some s1v.toNat := by
    rw [read64_agreeP (P := fun a => fsp.toNat-80 ≤ a ∧ a < fsp.toNat) (m := cN.σ.mem) (m' := mb5)
      (fun k hk => hcN_spill k hk) (fun j hj => ⟨by omega, by omega⟩)]; exact hs1M
  have hs2N' : read64 cN.σ.mem (fsp.toNat - 80 + 48) = some s2v.toNat := by
    rw [read64_agreeP (P := fun a => fsp.toNat-80 ≤ a ∧ a < fsp.toNat) (m := cN.σ.mem) (m' := mb5)
      (fun k hk => hcN_spill k hk) (fun j hj => ⟨by omega, by omega⟩)]; exact hs2M
  -- byte decompositions of the four reloads
  obtain ⟨rb0, rb1, rb2, rb3, rb4, rb5, rb6, rb7, hrb0, hrb1, hrb2, hrb3, hrb4, hrb5, hrb6, hrb7, hrbrec⟩ :=
    read64_bytes cN.σ.mem (fsp.toNat - 80 + 72) retAddr.toNat hraN'
  obtain ⟨sb0, sb1, sb2, sb3, sb4, sb5, sb6, sb7, hsb0, hsb1, hsb2, hsb3, hsb4, hsb5, hsb6, hsb7, hsbrec⟩ :=
    read64_bytes cN.σ.mem (fsp.toNat - 80 + 64) s0v.toNat hs0N'
  obtain ⟨tb0, tb1, tb2, tb3, tb4, tb5, tb6, tb7, htb0, htb1, htb2, htb3, htb4, htb5, htb6, htb7, htbrec⟩ :=
    read64_bytes cN.σ.mem (fsp.toNat - 80 + 56) s1v.toNat hs1N'
  obtain ⟨ub0, ub1, ub2, ub3, ub4, ub5, ub6, ub7, hub0, hub1, hub2, hub3, hub4, hub5, hub6, hub7, hubrec⟩ :=
    read64_bytes cN.σ.mem (fsp.toNat - 80 + 48) s2v.toNat hs2N'
  -- the reload-value = original (sext of a full word whose toNat = orig.toNat)
  have hreload_eq : ∀ (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) (w : BitVec 64),
      (b0.toNat + 256 * (b1.toNat + 256 * (b2.toNat + 256 * (b3.toNat + 256 *
        (b4.toNat + 256 * (b5.toNat + 256 * (b6.toNat + 256 * b7.toNat)))))) = w.toNat) →
      (sign_extend (m := 64) ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0) : BitVec (8*8)) : BitVec 64) = w := by
    intro b0 b1 b2 b3 b4 b5 b6 b7 w hrec
    rw [sext_full]; apply BitVec.eq_of_toNat_eq; rw [word8_toNat_recon]; exact hrec
  ------------------------------------------------------------------------
  -- Epilogue: reload ra/s0/s1/s2, addi sp,+80, ret.
  ------------------------------------------------------------------------
  have hNA_mb5 : Native_assertLoaded mb5 := hmem20e ▸ hNA20
  have hNA_N : Native_assertLoaded cN.σ.mem :=
    loaded_na_agreeP mb5 cN.σ.mem (fun a ha => hmemframeN a (by rcases hRG.sret_na with h|h <;> omega)) hNA_mb5
  -- addressing for the epilogue reloads (fsp-80 + 72/64/56/48)
  have hep72 : ((fsp - 80#64) + sign_extend (m := 64) (0x048#12)).toNat = fsp.toNat - 80 + 72 := haddr72
  have hep64 : ((fsp - 80#64) + sign_extend (m := 64) (0x040#12)).toNat = fsp.toNat - 80 + 64 := haddr64
  have hep56 : ((fsp - 80#64) + sign_extend (m := 64) (0x038#12)).toNat = fsp.toNat - 80 + 56 := haddr56
  have hep48 : ((fsp - 80#64) + sign_extend (m := 64) (0x030#12)).toNat = fsp.toNat - 80 + 48 := haddr48
  -- 0x80002e5c: ld ra,72(sp) → x1 := retAddr
  obtain ⟨σ27, i27, hs27', hi27, hG27, hmem27, hobs27⟩ :=
    site_80002e5c_na cN.σ cN.tick cN.steps (0x80002e5c#64) vmiN (fsp - 80#64)
      rb0 rb1 rb2 rb3 rb4 rb5 rb6 rb7 hGN hpcN' hmiN hsp_N hNA_N rfl
      (by rw [hep72]; omega) (by rw [hep72]; have := hRG.fsp_hi; omega)
      (by rw [hep72, htoh]; right; omega) (by rw [hep72]; have := hRG.fsp_align; omega)
      (by rw [hep72]; exact hrb0) (by rw [hep72]; exact hrb1) (by rw [hep72]; exact hrb2) (by rw [hep72]; exact hrb3)
      (by rw [hep72]; exact hrb4) (by rw [hep72]; exact hrb5) (by rw [hep72]; exact hrb6) (by rw [hep72]; exact hrb7) htickN
  have hstep27 : Step cN ⟨σ27, i27, cN.steps + 1⟩ := by cases cN; exact hs27'
  have hmem27e : σ27.mem = cN.σ.mem := hmem27
  have hpc27 : σ27.regs.get? Register.PC = some (0x80002e60#64) := by
    have := obs_alu_pc hobs27
    rwa [show BitVec.addInt (0x80002e5c#64) 4 = (0x80002e60#64 : BitVec 64) from by decide] at this
  have hx1_27 : σ27.regs.get? Register.x1 = some retAddr := by
    have := obs_alu_rd hobs27 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hreload_eq rb0 rb1 rb2 rb3 rb4 rb5 rb6 rb7 retAddr hrbrec] at this
  have hs0_27 : σ27.regs.get? Register.x8 = some sret := obs_alu_other' hobs27 Register.x8 (by decide) hs0_N
  have hsp_27 : σ27.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs27 Register.x2 (by decide) hsp_N
  obtain ⟨vmi27, hmi27⟩ := obs_alu_minstret hobs27
  have hout27 : σ27.sailOutput = out0 := by rw [hobs27.out, sailOutput_sigmaPost_alu]; exact houtN
  have hNA27 : Native_assertLoaded σ27.mem := by rw [hmem27e]; exact hNA_N
  -- 0x80002e60: mv a0,s0 → x10 := sret (dead for exit)
  obtain ⟨σ28, i28, hs28', hi28, hG28, hmem28, hobs28⟩ :=
    site_80002e60_na σ27 i27 (cN.steps + 1) (0x80002e60#64) vmi27 sret hG27 hpc27 hmi27 hs0_27 hNA27 rfl hi27
  have hstep28 : Step ⟨σ27, i27, cN.steps + 1⟩ ⟨σ28, i28, cN.steps + 1 + 1⟩ := hs28'
  have hmem28e : σ28.mem = cN.σ.mem := by rw [hmem28]; exact hmem27e
  have hpc28 : σ28.regs.get? Register.PC = some (0x80002e64#64) := by
    have := obs_alu_pc hobs28
    rwa [show BitVec.addInt (0x80002e60#64) 4 = (0x80002e64#64 : BitVec 64) from by decide] at this
  have hx1_28 : σ28.regs.get? Register.x1 = some retAddr := obs_alu_other' hobs28 Register.x1 (by decide) hx1_27
  have hsp_28 : σ28.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs28 Register.x2 (by decide) hsp_27
  obtain ⟨vmi28, hmi28⟩ := obs_alu_minstret hobs28
  have hout28 : σ28.sailOutput = out0 := by rw [hobs28.out, sailOutput_sigmaPost_alu]; exact hout27
  have hNA28 : Native_assertLoaded σ28.mem := by rw [hmem28e]; exact hmem27e ▸ hNA27
  -- 0x80002e64: ld s0,64(sp) → x8 (dead)
  obtain ⟨σ29, i29, hs29', hi29, hG29, hmem29, hobs29⟩ :=
    site_80002e64_na σ28 i28 (cN.steps + 1 + 1) (0x80002e64#64) vmi28 (fsp - 80#64)
      sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 hG28 hpc28 hmi28 hsp_28 hNA28 rfl
      (by rw [hep64]; omega) (by rw [hep64]; have := hRG.fsp_hi; omega)
      (by rw [hep64, htoh]; right; omega) (by rw [hep64]; have := hRG.fsp_align; omega)
      (by rw [hep64, hmem28e]; exact hsb0) (by rw [hep64, hmem28e]; exact hsb1) (by rw [hep64, hmem28e]; exact hsb2) (by rw [hep64, hmem28e]; exact hsb3)
      (by rw [hep64, hmem28e]; exact hsb4) (by rw [hep64, hmem28e]; exact hsb5) (by rw [hep64, hmem28e]; exact hsb6) (by rw [hep64, hmem28e]; exact hsb7) hi28
  have hstep29 : Step ⟨σ28, i28, cN.steps + 1 + 1⟩ ⟨σ29, i29, cN.steps + 1 + 1 + 1⟩ := hs29'
  have hmem29e : σ29.mem = cN.σ.mem := by rw [hmem29]; exact hmem28e
  have hpc29 : σ29.regs.get? Register.PC = some (0x80002e68#64) := by
    have := obs_alu_pc hobs29
    rwa [show BitVec.addInt (0x80002e64#64) 4 = (0x80002e68#64 : BitVec 64) from by decide] at this
  have hx1_29 : σ29.regs.get? Register.x1 = some retAddr := obs_alu_other' hobs29 Register.x1 (by decide) hx1_28
  have hx8_29 : σ29.regs.get? Register.x8 = some s0v := by
    have := obs_alu_rd hobs29 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hreload_eq sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 s0v hsbrec] at this
  have hsp_29 : σ29.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs29 Register.x2 (by decide) hsp_28
  obtain ⟨vmi29, hmi29⟩ := obs_alu_minstret hobs29
  have hout29 : σ29.sailOutput = out0 := by rw [hobs29.out, sailOutput_sigmaPost_alu]; exact hout28
  have hNA29 : Native_assertLoaded σ29.mem := by rw [hmem29e]; exact hmem28e ▸ hNA28
  -- 0x80002e68: ld s1,56(sp) → x9 (dead)
  obtain ⟨σ30, i30, hs30', hi30, hG30, hmem30, hobs30⟩ :=
    site_80002e68_na σ29 i29 (cN.steps + 1 + 1 + 1) (0x80002e68#64) vmi29 (fsp - 80#64)
      tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 hG29 hpc29 hmi29 hsp_29 hNA29 rfl
      (by rw [hep56]; omega) (by rw [hep56]; have := hRG.fsp_hi; omega)
      (by rw [hep56, htoh]; right; omega) (by rw [hep56]; have := hRG.fsp_align; omega)
      (by rw [hep56, hmem29e]; exact htb0) (by rw [hep56, hmem29e]; exact htb1) (by rw [hep56, hmem29e]; exact htb2) (by rw [hep56, hmem29e]; exact htb3)
      (by rw [hep56, hmem29e]; exact htb4) (by rw [hep56, hmem29e]; exact htb5) (by rw [hep56, hmem29e]; exact htb6) (by rw [hep56, hmem29e]; exact htb7) hi29
  have hstep30 : Step ⟨σ29, i29, cN.steps + 1 + 1 + 1⟩ ⟨σ30, i30, cN.steps + 1 + 1 + 1 + 1⟩ := hs30'
  have hmem30e : σ30.mem = cN.σ.mem := by rw [hmem30]; exact hmem29e
  have hpc30 : σ30.regs.get? Register.PC = some (0x80002e6c#64) := by
    have := obs_alu_pc hobs30
    rwa [show BitVec.addInt (0x80002e68#64) 4 = (0x80002e6c#64 : BitVec 64) from by decide] at this
  have hx1_30 : σ30.regs.get? Register.x1 = some retAddr := obs_alu_other' hobs30 Register.x1 (by decide) hx1_29
  have hx9_30 : σ30.regs.get? Register.x9 = some s1v := by
    have := obs_alu_rd hobs30 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hreload_eq tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 s1v htbrec] at this
  have hx8_30 : σ30.regs.get? Register.x8 = some s0v := obs_alu_other' hobs30 Register.x8 (by decide) hx8_29
  have hsp_30 : σ30.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs30 Register.x2 (by decide) hsp_29
  obtain ⟨vmi30, hmi30⟩ := obs_alu_minstret hobs30
  have hout30 : σ30.sailOutput = out0 := by rw [hobs30.out, sailOutput_sigmaPost_alu]; exact hout29
  have hNA30 : Native_assertLoaded σ30.mem := by rw [hmem30e]; exact hmem29e ▸ hNA29
  -- 0x80002e6c: ld s2,48(sp) → x18 (dead)
  obtain ⟨σ31, i31, hs31', hi31, hG31, hmem31, hobs31⟩ :=
    site_80002e6c_na σ30 i30 (cN.steps + 1 + 1 + 1 + 1) (0x80002e6c#64) vmi30 (fsp - 80#64)
      ub0 ub1 ub2 ub3 ub4 ub5 ub6 ub7 hG30 hpc30 hmi30 hsp_30 hNA30 rfl
      (by rw [hep48]; omega) (by rw [hep48]; have := hRG.fsp_hi; omega)
      (by rw [hep48, htoh]; right; omega) (by rw [hep48]; have := hRG.fsp_align; omega)
      (by rw [hep48, hmem30e]; exact hub0) (by rw [hep48, hmem30e]; exact hub1) (by rw [hep48, hmem30e]; exact hub2) (by rw [hep48, hmem30e]; exact hub3)
      (by rw [hep48, hmem30e]; exact hub4) (by rw [hep48, hmem30e]; exact hub5) (by rw [hep48, hmem30e]; exact hub6) (by rw [hep48, hmem30e]; exact hub7) hi30
  have hstep31 : Step ⟨σ30, i30, cN.steps + 1 + 1 + 1 + 1⟩ ⟨σ31, i31, cN.steps + 1 + 1 + 1 + 1 + 1⟩ := hs31'
  have hmem31e : σ31.mem = cN.σ.mem := by rw [hmem31]; exact hmem30e
  have hpc31 : σ31.regs.get? Register.PC = some (0x80002e70#64) := by
    have := obs_alu_pc hobs31
    rwa [show BitVec.addInt (0x80002e6c#64) 4 = (0x80002e70#64 : BitVec 64) from by decide] at this
  have hx1_31 : σ31.regs.get? Register.x1 = some retAddr := obs_alu_other' hobs31 Register.x1 (by decide) hx1_30
  have hx18_31 : σ31.regs.get? Register.x18 = some s2v := by
    have := obs_alu_rd hobs31 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hreload_eq ub0 ub1 ub2 ub3 ub4 ub5 ub6 ub7 s2v hubrec] at this
  have hx8_31 : σ31.regs.get? Register.x8 = some s0v := obs_alu_other' hobs31 Register.x8 (by decide) hx8_30
  have hx9_31 : σ31.regs.get? Register.x9 = some s1v := obs_alu_other' hobs31 Register.x9 (by decide) hx9_30
  have hsp_31 : σ31.regs.get? Register.x2 = some (fsp - 80#64) := obs_alu_other' hobs31 Register.x2 (by decide) hsp_30
  obtain ⟨vmi31, hmi31⟩ := obs_alu_minstret hobs31
  have hout31 : σ31.sailOutput = out0 := by rw [hobs31.out, sailOutput_sigmaPost_alu]; exact hout30
  have hNA31 : Native_assertLoaded σ31.mem := by rw [hmem31e]; exact hmem30e ▸ hNA30
  -- 0x80002e70: addi sp,sp,80 → x2 := (fsp-80)+80 = fsp
  obtain ⟨σ32, i32, hs32', hi32, hG32, hmem32, hobs32⟩ :=
    site_80002e70_na σ31 i31 (cN.steps + 1 + 1 + 1 + 1 + 1) (0x80002e70#64) vmi31 (fsp - 80#64)
      hG31 hpc31 hmi31 hsp_31 hNA31 rfl hi31
  have hstep32 : Step ⟨σ31, i31, cN.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ32, i32, cN.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs32'
  have hmem32e : σ32.mem = cN.σ.mem := by rw [hmem32]; exact hmem31e
  have hpc32 : σ32.regs.get? Register.PC = some (0x80002e74#64) := by
    have := obs_alu_pc hobs32
    rwa [show BitVec.addInt (0x80002e70#64) 4 = (0x80002e74#64 : BitVec 64) from by decide] at this
  have hsp_32 : σ32.regs.get? Register.x2 = some fsp := by
    have := obs_alu_rd hobs32 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show ((fsp - 80#64) + sign_extend (m := 64) (0x050#12) : BitVec 64) = fsp from by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hspNat, show (sign_extend (m := 64) (0x050#12) : BitVec 64).toNat = 80 from by decide]
      have := hRG.fsp_hi; have := fsp.isLt; omega] at this
  have hx1_32 : σ32.regs.get? Register.x1 = some retAddr := obs_alu_other' hobs32 Register.x1 (by decide) hx1_31
  have hx8_32 : σ32.regs.get? Register.x8 = some s0v := obs_alu_other' hobs32 Register.x8 (by decide) hx8_31
  have hx9_32 : σ32.regs.get? Register.x9 = some s1v := obs_alu_other' hobs32 Register.x9 (by decide) hx9_31
  have hx18_32 : σ32.regs.get? Register.x18 = some s2v := obs_alu_other' hobs32 Register.x18 (by decide) hx18_31
  obtain ⟨vmi32, hmi32⟩ := obs_alu_minstret hobs32
  have hout32 : σ32.sailOutput = out0 := by rw [hobs32.out, sailOutput_sigmaPost_alu]; exact hout31
  have hNA32 : Native_assertLoaded σ32.mem := by rw [hmem32e]; exact hmem31e ▸ hNA31
  -- 0x80002e74: ret → PC := retAddr (bit-0-cleared)
  obtain ⟨σ33, i33, hs33', hi33, hG33, hmem33, hobs33⟩ :=
    site_80002e74_na σ32 i32 (cN.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80002e74#64) vmi32 retAddr
      hG32 hpc32 hmi32 hx1_32 hNA32 rfl hrettgt hi32
  have hstep33 : Step ⟨σ32, i32, cN.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ33, i33, cN.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs33'
  have hmem33e : σ33.mem = cN.σ.mem := hmem33.trans hmem32e
  have hpc_fin : σ33.regs.get? Register.PC = some (BitVec.update (retAddr + sign_extend (m := 64) (0x000#12)) 0 0#1) := by
    have := obs_jr_pc hobs33
    exact this
  have hsp_fin : σ33.regs.get? Register.x2 = some fsp := obs_jr_other' hobs33 Register.x2 (by decide) hsp_32
  have hx8_fin : σ33.regs.get? Register.x8 = some s0v := obs_jr_other' hobs33 Register.x8 (by decide) hx8_32
  have hx9_fin : σ33.regs.get? Register.x9 = some s1v := obs_jr_other' hobs33 Register.x9 (by decide) hx9_32
  have hx18_fin : σ33.regs.get? Register.x18 = some s2v := obs_jr_other' hobs33 Register.x18 (by decide) hx18_32
  obtain ⟨vmi33, hmi33⟩ := obs_jr_minstret hobs33
  have hout_fin : σ33.sailOutput = out0 := by rw [hobs33.out, sailOutput_sigmaPost_jump_x0]; exact hout32
  ------------------------------------------------------------------------
  -- Whole-run register frame: one `StepFrameOut` per site, the two callee
  -- sub-runs wrapped from their `NotWrittenT`/`NotWrittenV` frame clauses.
  ------------------------------------------------------------------------
  have sfoT : StepFrameOut ([Register.x10, Register.x14, Register.x15] ++ noiseRegs) σ21 cT.σ :=
    ⟨houtT.trans hout21.symm, fun R hav =>
      hframeT R ⟨hav _ (by decide), hav _ (by decide), hav _ (by decide),
        hav _ (by decide), hav _ (by decide), hav _ (by decide), hav _ (by decide),
        hav _ (by decide), hav _ (by decide), hav _ (by decide)⟩⟩
  have sfoN : StepFrameOut ([Register.x11, Register.x15] ++ noiseRegs) σ26 cN.σ :=
    ⟨houtN.trans hout26.symm, fun R hav =>
      hframeN R ⟨hav _ (by decide), hav _ (by decide), hav _ (by decide),
        hav _ (by decide), hav _ (by decide), hav _ (by decide), hav _ (by decide),
        hav _ (by decide), hav _ (by decide)⟩⟩
  have sfoAll :=
    ((((((((((((((((((((((((((((((((((StepFrameOut.of_alu hobs1).trans
      (StepFrameOut.of_store hobs2)).trans (StepFrameOut.of_store hobs3)).trans
      (StepFrameOut.of_store hobs4)).trans (StepFrameOut.of_store hobs5)).trans
      (StepFrameOut.of_alu hobs6)).trans (StepFrameOut.of_alu hobs7)).trans
      (StepFrameOut.of_alu hobs8)).trans (StepFrameOut.of_alu hobs9)).trans
      (StepFrameOut.of_branch_nottaken hobs10)).trans (StepFrameOut.of_alu hobs11)).trans
      (StepFrameOut.of_alu hobs12)).trans (StepFrameOut.of_alu hobs13)).trans
      (StepFrameOut.of_alu hobs14)).trans (StepFrameOut.of_alu hobs15)).trans
      (StepFrameOut.of_store hobs16)).trans (StepFrameOut.of_store hobs17)).trans
      (StepFrameOut.of_store hobs18)).trans (StepFrameOut.of_store hobs19)).trans
      (StepFrameOut.of_store hobs20)).trans (StepFrameOut.of_jal hobs21)).trans
      sfoT).trans (StepFrameOut.of_alu hobs22)).trans (StepFrameOut.of_alu hobs23)).trans
      (StepFrameOut.of_branch_nottaken hobs24)).trans (StepFrameOut.of_alu hobs25)).trans
      (StepFrameOut.of_jal hobs26)).trans sfoN).trans (StepFrameOut.of_alu hobs27)).trans
      (StepFrameOut.of_alu hobs28)).trans (StepFrameOut.of_alu hobs29)).trans
      (StepFrameOut.of_alu hobs30)).trans (StepFrameOut.of_alu hobs31)).trans
      (StepFrameOut.of_alu hobs32)).trans (StepFrameOut.of_jr hobs33)
  ------------------------------------------------------------------------
  -- Assemble the whole run and the naExit postcondition.
  ------------------------------------------------------------------------
  refine ⟨⟨σ33, i33, cN.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, ?_, ?_⟩
  · -- the full Steps chain
    exact (((((((((((((((((((((((((((((((((((Steps.single hstep1).trans (Steps.single hstep2)).trans (Steps.single hstep3)).trans (Steps.single hstep4)).trans (Steps.single hstep5)).trans (Steps.single hstep6)).trans (Steps.single hstep7)).trans (Steps.single hstep8)).trans (Steps.single hstep9)).trans (Steps.single hstep10)).trans (Steps.single hstep11)).trans (Steps.single hstep12)).trans (Steps.single hstep13)).trans (Steps.single hstep14)).trans (Steps.single hstep15)).trans (Steps.single hstep16)).trans (Steps.single hstep17)).trans (Steps.single hstep18)).trans (Steps.single hstep19)).trans (Steps.single hstep20)).trans (Steps.single hstep21)).trans hsT).trans (Steps.single hstep22)).trans (Steps.single hstep23)).trans (Steps.single hstep24)).trans (Steps.single hstep25)).trans (Steps.single hstep26)).trans hsN).trans (Steps.single hstep27)).trans (Steps.single hstep28)).trans (Steps.single hstep29)).trans (Steps.single hstep30)).trans (Steps.single hstep31)).trans (Steps.single hstep32)).trans (Steps.single hstep33))
  · -- naExit
    refine ⟨hG33, hi33, hpc_fin, ?_, hout_fin, ?_, ⟨_, hmi33⟩, hsp_fin, ?_⟩
    · -- ValueRepr sret .null (from value_null, survives the pure-register epilogue)
      rw [hmem33e]; exact hvalNull
    · -- memory framed outside [fsp-80, fsp+40) ∪ [sret, sret+24):
      -- cN.σ.mem = mb5 outside sret window (value_null memFrame), and
      -- mb5 = m0 outside [fsp-80, fsp+40) (hbufout).
      intro a hframe_a hsret_a
      rw [hmem33e, ← hmemframeN a (by rcases hsret_a with h|h <;> omega)]
      exact hbufout a hframe_a
    · -- the ABI callee-saved frame: `ra/s0/s1/s2` reload their spills, `sp`
      -- is re-adjusted, and no other callee-saved register is written
      -- anywhere in the run (whole-run `StepFrameOut`).
      intro R hR
      obtain ⟨hab, _, _, _, _, _, _, _⟩ := hR
      rcases abiPreserved_enum R hab with
        rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hsp_fin.trans ((hframe _ (by decide)).symm.trans hsp).symm
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact hx8_fin.trans ((hframe _ (by decide)).symm.trans hs0r).symm
      · exact hx9_fin.trans ((hframe _ (by decide)).symm.trans hs1r).symm
      · exact hx18_fin.trans ((hframe _ (by decide)).symm.trans hs2r).symm
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))
      · exact (sfoAll.frame _ (by decide)).trans (hframe _ (by decide))

end Vsa.Sim
