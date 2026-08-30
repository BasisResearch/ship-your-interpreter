import Vsa.Sim.EvalIntSim
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.ReprSurvival
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — shared, case-INDEPENDENT `eval_expr` prologue/epilogue lemmas

The `EvalE.int` simulation Triple (`evalIntSim`, `EvalIntSim4.lean`) is a
composition `blockA_ee ≫ blockC_ee ≫ blockD_ee`. Of these, `blockA_ee` (the
prologue + jump-table dispatch) and `blockD_ee` (the shared epilogue: four `ld`
restores + `mv a0,s1` + `addi sp,sp,1088` + `ret`) do NOT inspect the produced
`Value` or the `.int`-specific callee `value_int` — they are shared across every
sibling `EvalE` leaf case (`null`/`bool`/`str`/`var`).

This file extracts the **epilogue** in its case-independent form:

* **`PreEpilogueV`** — the machine state at the shared epilogue entry
  `0x800033ec`, parameterized over an arbitrary produced `Value v` (the sret
  buffer holds `ValueRepr … v` — the epilogue never reads the buffer contents,
  it only threads them into `EvalExit.result`). `EvalIntSim3.lean`'s
  `PreEpilogue … n` is the instance `PreEpilogueV … (.int n)`.
* **`blockD_v`** — the epilogue Triple `PreEpilogueV … v → EvalExit … v`, the
  seven-instruction restore/return sequence. Value-agnostic: `EvalIntSim4.lean`'s
  `blockD_ee` is `blockD_v` at `v := .int n`.
* The four `ld`-restore address offsets (`epi_off438/430/420/428`) and the
  sd-then-ld `spill_roundtrip_ee` bridge — all value-independent, reusable by
  every leaf case's epilogue.

A future `null`/`bool`/`str`/`var` case instantiates `blockD_v` at its own `v`
(e.g. `.null`, `.bool b`, `.str s`) once its own `blockC_*` arm reaches
`PreEpilogueV … v`; only the arm (block C, the payload load + which `value_*`
callee runs) is case-specific.

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

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Address arithmetic for the frame + spill windows (value-independent) -/

/-- `addi sp,sp,-1088`: `sp + sext 0xbc0 = sp - 1088`. -/
theorem sp_sub1088 (sp : BitVec 64) :
    (sp + sign_extend (m := 64) (0xbc0#12)) = sp - 1088#64 := by
  have hs : (sign_extend (m := 64) (0xbc0#12) : BitVec 64) = -(1088#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have hn : (-(1088#64) : BitVec 64).toNat = 2^64 - 1088 := by decide
  have h : (1088#64 : BitVec 64).toNat = 1088 := by decide
  rw [hn, h]; have := sp.isLt; omega

/-- `addi sp,sp,1088`: `(sp - 1088) + sext 0x440 = sp`. -/
theorem sp_add1088 (sp : BitVec 64) :
    (sp - 1088#64) + sign_extend (m := 64) (0x440#12) = sp := by
  have hs : (sign_extend (m := 64) (0x440#12) : BitVec 64) = 1088#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_sub]
  have h : (1088#64 : BitVec 64).toNat = 1088 := by decide
  rw [h]; have := sp.isLt; omega

/-- A spill store `sd rs2, off(sp')` where `sp' = sp - 1088` and `off ∈ {1056,1064,1072,1080}`
targets `sp - (1088 - off)`; as a `.toNat` this is `sp.toNat - (1088 - off)` when
`1088 ≤ sp.toNat`. We give the four concrete offsets. -/
theorem spill_addr (sp : BitVec 64) (off : BitVec 12) (k : Nat)
    (hoff : (sign_extend (m := 64) off : BitVec 64).toNat = 1088 - k)
    (hk : k ≤ 1088) (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) off).toNat = sp.toNat - k := by
  rw [BitVec.toNat_add, BitVec.toNat_sub, hoff]
  have h : (1088#64 : BitVec 64).toNat = 1088 := by decide
  rw [h]; have := sp.isLt; omega

/-! ## The spill roundtrip — the sd-then-ld bridge (value-independent)

If `mem` reads back `v.toNat` at address `a` (i.e. an 8-byte `sd`-spill of `v`
survives at `a`), then the eight individual bytes `bi = mem[a+i]?` are `some`,
and the little-endian sign-extended reassembly the epilogue `ld` produces
(`sign_extend (b7 ++ … ++ b0)`) equals `v`. Consumed by the four `ld` restore
sites (`site_800033ec/f0/fc/f4_ee`). -/
theorem spill_roundtrip_ee (mem : Mem) (a : Nat) (v : BitVec 64)
    (hread : read64 mem a = some v.toNat) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8,
      mem[a]? = some b0 ∧ mem[a + 1]? = some b1 ∧ mem[a + 2]? = some b2 ∧
      mem[a + 3]? = some b3 ∧ mem[a + 4]? = some b4 ∧ mem[a + 5]? = some b5 ∧
      mem[a + 6]? = some b6 ∧ mem[a + 7]? = some b7 ∧
      (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8 * 8))) = v := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, hrec⟩ :=
    read64_bytes mem a v.toNat hread
  refine ⟨b0, b1, b2, b3, b4, b5, b6, b7, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, ?_⟩
  rw [sext_full]
  apply BitVec.eq_of_toNat_eq
  rw [word8_toNat_recon, hrec]

/-! ### Offsets: the four `ld` restore addresses as `sp - k`. -/
theorem epi_off438 (sp : BitVec 64) (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) (0x438#12)).toNat = sp.toNat - 8 :=
  spill_addr sp (0x438#12) 8 (by decide) (by omega) hsp
theorem epi_off430 (sp : BitVec 64) (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) (0x430#12)).toNat = sp.toNat - 16 :=
  spill_addr sp (0x430#12) 16 (by decide) (by omega) hsp
theorem epi_off420 (sp : BitVec 64) (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) (0x420#12)).toNat = sp.toNat - 32 :=
  spill_addr sp (0x420#12) 32 (by decide) (by omega) hsp
theorem epi_off428 (sp : BitVec 64) (hsp : 1088 ≤ sp.toNat) :
    ((sp - 1088#64) + sign_extend (m := 64) (0x428#12)).toNat = sp.toNat - 24 :=
  spill_addr sp (0x428#12) 24 (by decide) (by omega) hsp

/-! ## `KindSlotPinned` — the per-kind jump-table slot pin (dispatch coupling)

The `EX_*` dispatch reads a 4-byte offset from the `.rodata` jump table at
`jumpTableBase = 0x80019f58`, slot `k` living at `jumpTableBase + 4*k`, then jumps
to `jumpTableBase + (Int32)offset`. `KindSlotPinned k armPC m` says: the four
bytes of slot `k` in `m` are `t0..t3`, and their sign-extended little-endian
reassembly plus the table base equals the arm's landing PC `armPC`. This is the
case-INDEPENDENT generalization of `IntSlotPinned` (`InterpEntry.lean`), which is
exactly `KindSlotPinned 0 0x80003408` up to the target-arithmetic fact
(`int_slot_kindPinned`). A `null`/`bool`/`str`/`var` case supplies its own
`KindSlotPinned k armPC` for its tag `k` and arm `armPC`. -/
def KindSlotPinned (k : Nat) (armPC : BitVec 64) (m : Mem) : Prop :=
  ∃ t0 t1 t2 t3 : BitVec 8,
    m[(jumpTableBase + 4 * k + 0 : Nat)]? = some t0 ∧
    m[(jumpTableBase + 4 * k + 1 : Nat)]? = some t1 ∧
    m[(jumpTableBase + 4 * k + 2 : Nat)]? = some t2 ∧
    m[(jumpTableBase + 4 * k + 3 : Nat)]? = some t3 ∧
    (sign_extend (m := 64) ((((t3.append t2).append t1).append t0) : BitVec (8 * 4))
      + BitVec.ofNat 64 jumpTableBase) = armPC

/-- The `EX_INT` (tag 0) instance: `IntSlotPinned` (slot bytes `b0 94 fe ff` at
`0x80019f58`, offset `0xfffe94b0`) gives `KindSlotPinned 0 0x80003408` — the arm
`0x80003408 = 0x80019f58 + (Int32)0xfffe94b0`. Discharges the int slot pin from the
existing `IntSlotPinned` fact carried by `EvalEntry.int_slot`. -/
theorem int_slot_kindPinned {m : Mem} (h : IntSlotPinned m) :
    KindSlotPinned 0 (0x80003408#64) m := by
  obtain ⟨p0, p1, p2, p3⟩ := h
  refine ⟨0xb0#8, 0x94#8, 0xfe#8, 0xff#8, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [jumpTableBase, Nat.mul_zero, Nat.add_zero] using p0
  · simpa [jumpTableBase, Nat.mul_zero] using p1
  · simpa [jumpTableBase, Nat.mul_zero] using p2
  · simpa [jumpTableBase, Nat.mul_zero] using p3
  · apply BitVec.eq_of_toNat_eq; simp only [jumpTableBase]; decide

/-! ## `ArmEntryK` — the machine state at a leaf arm's entry PC (dispatch target)

The case-INDEPENDENT half of the prologue + jump-table dispatch (`blockA_ee`,
`EvalIntSim2.lean`) lands at the per-case arm PC. `ArmEntryK` collects the machine
facts true there, generalized over exactly the three case-specific couplings of
the dispatch:

* **`armPC : BitVec 64`** — the jump-table landing PC (the arm's first
  instruction). For `.int` this is `0x80003408` (the `ld a1,8(a2); jal value_int`
  arm); each `EX_*` kind's slot points to its own arm.
* **`calleeLoaded : Mem → Prop`** — the "this arm's callee is loaded" predicate,
  carried through the spills alongside `Eval_exprLoaded`. For `.int` this is
  `Value_intLoaded`; `null`/`bool`/`str` use `Value_nullLoaded`/… .
* **`e : Expr`** — the evaluated expression (`ExprRepr ment aExpr.toNat e`). For
  the `.int` case `e = .int n`.

Everything else — the four spilled callee-saved slots, the lowered `sp`, the
`store_survives`/`StoreRepr`/`memFrame`/frame facts, and all the geometric
region facts — is identical across every leaf case. `EvalIntSim2.lean`'s
`ArmEntry … n` is the instance `ArmEntryK … (0x80003408) Value_intLoaded (.int n)`.

A future `null`/`bool`/`str`/`var` case reuses `blockA_ee`'s prologue+dispatch to
reach `ArmEntryK` at its own `armPC`/`calleeLoaded`/`e`, then runs only its own
arm (block C) to `PreEpilogueV … v`, closing with the shared `blockD_v`. -/
def ArmEntryK
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (armPC : BitVec 64) (calleeLoaded : Mem → Prop) (e : Expr)
    (sp r sret aExpr aEnv : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 ment : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some armPC ∧
  c.σ.regs.get? Register.x10 = some sret ∧           -- a0 = sret (preserved)
  c.σ.regs.get? Register.x9 = some sret ∧             -- s1 = sret
  c.σ.regs.get? Register.x12 = some aExpr ∧           -- a2 = Expr node
  c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧   -- sp lowered
  c.σ.regs.get? Register.x1 = some r ∧               -- ra still = r (spilled too)
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  c.σ.sailOutput = out0 ∧
  c.σ.mem = ment ∧ Eval_exprLoaded ment ∧ calleeLoaded ment ∧
  ExprRepr ment aExpr.toNat e ∧
  String.join out0.toList = st.out ∧
  aExpr.toNat % 8 = 0 ∧
  0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ aExpr.toNat ∧
  read64 ment (sp.toNat - 8) = some r.toNat ∧    -- [sp-8]   = ra
  read64 ment (sp.toNat - 16) = some v8.toNat ∧  -- [sp-16]  = s0
  read64 ment (sp.toNat - 24) = some v9.toNat ∧  -- [sp-24]  = s1
  read64 ment (sp.toNat - 32) = some v18.toNat ∧ -- [sp-32]  = s2
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) ∧
  g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
  g Register.x2 = some sp ∧
  StoreRepr ment N A φf φc st.store ∧
  (∀ m' : Mem,
    (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
      ment[k]? = m'[k]?) →
    StoreRepr m' N A φf φc st.store) ∧
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x2 == R) = false →
    c.σ.regs.get? R = g R) ∧
  sret.toNat % 8 = 0 ∧
  0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
  tohostAddr + 16 ≤ sret.toNat ∧
  (sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat) ∧
  (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
  (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
  1088 ≤ sp.toNat ∧ sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
  tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
  0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧ SL.lo + 1088 ≤ sp.toNat ∧
  r.toNat % 4 = 0 ∧
  -- ===== recursive-case call-point register facts (the `blockA_k`/`ArmEntryK`
  -- widening: the `mv s0,a2`/`mv s2,a1` prologue moves + the untouched `a1`).
  -- Leaf cases ignore these; recursive arms build the call-point ghost frame
  -- `gpre := c.σ.regs.get?` and read `x11 = interp*` from them. =====
  c.σ.regs.get? Register.x11 = some aEnv ∧   -- a1 = interp* (untouched by dispatch)
  c.σ.regs.get? Register.x8 = some aExpr ∧   -- s0 = Expr node (mv s0,a2 @0x80003180)
  c.σ.regs.get? Register.x18 = some aEnv     -- s2 = interp* (mv s2,a1 @0x80003184)

/-! ## `PreEpilogueV` — the machine state at the shared epilogue `0x800033ec`

Generalizes `EvalIntSim3.lean`'s `PreEpilogue` over the produced `Value v` (the
sret buffer holds `ValueRepr … v`). After a leaf arm's block C: `value_*` has
filled the sret buffer with `ValueRepr v`, `s1 = sret`, `sp = sp-1088`
(all preserved by the callee's `NotWritten*` frame). The four spilled
callee-saved slots `[sp-8], [sp-16], [sp-24], [sp-32]` still hold their entry
values (disjoint from the sret write). `eval_expr` loaded. Output invariant
(`= out0`). -/
def PreEpilogueV
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (m0 mpre : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some (0x800033ec#64) ∧
  c.σ.regs.get? Register.x9 = some sret ∧               -- s1 = sret
  c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧     -- sp lowered
  -- NOTE: x1 (ra) still holds the callee's return link here — the ORIGINAL `r`
  -- lives in the spill slot `[sp-8]` and is restored by block D's
  -- `ld ra,1080(sp)`. So we do NOT claim `x1 = r` at the epilogue entry.
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧
  c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
  c.σ.mem = mpre ∧ Eval_exprLoaded mpre ∧
  -- the sret buffer represents the produced value `v`
  ValueRepr mpre N φc sret.toNat v ∧
  -- store re-represented at `mpre` (survived the spills + sret write)
  StoreRepr mpre N A φf φc st.store ∧
  -- every callee-saved reg not clobbered by the prologue (i.e. NOT s0/s1/s2/sp)
  -- still reads `g R`; s0/s1/s2/sp are restored by the epilogue from the slots.
  (∀ R : Register, AbiPreservedNoise R →
    (Register.x8 == R) = false → (Register.x9 == R) = false →
    (Register.x18 == R) = false → (Register.x2 == R) = false →
    c.σ.regs.get? R = g R) ∧
  -- the four callee-saved spill slots (survived the callee's sret write, which is
  -- disjoint from the stack window) still hold the entry `ra`/`s0`/`s1`/`s2`.
  read64 mpre (sp.toNat - 8) = some r.toNat ∧
  read64 mpre (sp.toNat - 16) = some v8.toNat ∧
  read64 mpre (sp.toNat - 24) = some v9.toNat ∧
  read64 mpre (sp.toNat - 32) = some v18.toNat ∧
  -- the entry values `s0`/`s1`/`s2`/`sp` are exactly the ghost frame's values, so the
  -- epilogue restore re-establishes `EvalExit.frame` (`= g R`).
  g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
  g Register.x2 = some sp ∧
  -- memory frame: `mpre` differs from the entry `m0` only inside the stack window
  -- `[SL.lo, sp)` (the prologue spills), the arena `[A.lo, A.hi)`, or the sret
  -- buffer `[sret, sret+24)` (the callee's write). This is exactly
  -- `EvalExit.memFrame` (the epilogue writes no memory, so the exit memory is `mpre`).
  (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = m0[a]?) ∧
  -- geometric facts the epilogue loads need (stack window in RAM, aligned, above HTIF)
  1088 ≤ sp.toNat ∧
  sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
  tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
  r.toNat % 4 = 0

/-! ## `blockD_v` — the shared epilogue, generalized over the produced `Value`

`PreEpilogueV … v → EvalExit … v`. The seven epilogue instructions never inspect
the sret buffer's contents: `v` is only threaded into `EvalExit.result` (with the
identity `φc` extension) and `EvalExit.store` (identity `φf`/`φc`, `st'.store =
st.store` — true for every leaf case). Value-agnostic body: identical to the
`.int`-specialized `blockD_ee` with `n → v`. -/
theorem blockD_v
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- an arbitrary memory predicate carried across the (memory-pure) epilogue: the
    -- seven epilogue instructions never write memory, so any `Q` holding at the
    -- epilogue-entry memory `mpre` also holds at the exit memory. Leaf cases take
    -- `Q := fun _ => True`; the recursive case threads the `EvalExitD` upgrade
    -- clauses (`MemExtends` + `[SL.lo,SL.hi)`-survival) as `Q`.
    (Q : Mem → Prop) :
    Triple
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c ∧ Q mpre)
      (fun c => EvalExit g N A SL φf φc st v sp r sret m0 c ∧ Q c.σ.mem) := by
  intro c hpre
  obtain ⟨mpre, ⟨hG, htick, hpc, hs1, hsp, ⟨vmi, hmi⟩, hout, houtStr, hmem, hcode, hval, hstore, hframe,
    hslotRa, hslotS0, hslotS1, hslotS2, hgx8, hgx9, hgx18, hgx2, hmemframe,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩, hQ⟩ := hpre
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- restore addresses
  have haRa : ((sp - 1088#64) + sign_extend (m := 64) (0x438#12)).toNat = sp.toNat - 8 := epi_off438 sp hsp1088
  have haS0 : ((sp - 1088#64) + sign_extend (m := 64) (0x430#12)).toNat = sp.toNat - 16 := epi_off430 sp hsp1088
  have haS2 : ((sp - 1088#64) + sign_extend (m := 64) (0x420#12)).toNat = sp.toNat - 32 := epi_off420 sp hsp1088
  have haS1 : ((sp - 1088#64) + sign_extend (m := 64) (0x428#12)).toNat = sp.toNat - 24 := epi_off428 sp hsp1088
  -- spill_roundtrip byte facts for each slot
  obtain ⟨ra0, ra1, ra2, ra3, ra4, ra5, ra6, ra7, hra0, hra1, hra2, hra3, hra4, hra5, hra6, hra7, hraSext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 8) r hslotRa
  obtain ⟨s00, s01, s02, s03, s04, s05, s06, s07, hs00, hs01, hs02, hs03, hs04, hs05, hs06, hs07, hs0Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 16) v8 hslotS0
  obtain ⟨s20, s21, s22, s23, s24, s25, s26, s27, hs20, hs21, hs22, hs23, hs24, hs25, hs26, hs27, hs2Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 32) v18 hslotS2
  obtain ⟨s10, s11, s12, s13, s14, s15, s16, s17, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs1Sext⟩ :=
    spill_roundtrip_ee mpre (sp.toNat - 24) v9 hslotS1
  -- ============ 0x800033ec: ld ra,1080(sp) → x1 := r ============
  obtain ⟨σ1, i1, hstep1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800033ec_ee c.σ c.tick c.steps (0x800033ec#64) vmi (sp-1088#64) ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
      hG hpc hmi hsp (hmem ▸ hcode) rfl
      (by rw [haRa]; omega) (by rw [haRa]; omega) (by rw [haRa, htoh]; right; omega) (by rw [haRa]; omega)
      (by rw [haRa, hmem]; exact hra0) (by rw [haRa, hmem]; exact hra1) (by rw [haRa, hmem]; exact hra2)
      (by rw [haRa, hmem]; exact hra3) (by rw [haRa, hmem]; exact hra4) (by rw [haRa, hmem]; exact hra5)
      (by rw [haRa, hmem]; exact hra6) (by rw [haRa, hmem]; exact hra7) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hstep1'
  have hmem1e : σ1.mem = mpre := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some (0x800033f0#64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x800033ec#64) 4 = (0x800033f0#64:BitVec 64) from by decide] at this
  have hra_1 : σ1.regs.get? Register.x1 = some r := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hraSext] at this
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- ============ 0x800033f0: ld s0,1072(sp) → x8 := v8 ============
  obtain ⟨σ2, i2, hstep2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800033f0_ee σ1 i1 (c.steps + 1) (0x800033f0#64) vmi1 (sp-1088#64) s00 s01 s02 s03 s04 s05 s06 s07
      hG1 hpc1 hmi1 hsp_1 hcode1 rfl
      (by rw [haS0]; omega) (by rw [haS0]; omega) (by rw [haS0, htoh]; right; omega) (by rw [haS0]; omega)
      (by rw [haS0, hmem1e]; exact hs00) (by rw [haS0, hmem1e]; exact hs01) (by rw [haS0, hmem1e]; exact hs02)
      (by rw [haS0, hmem1e]; exact hs03) (by rw [haS0, hmem1e]; exact hs04) (by rw [haS0, hmem1e]; exact hs05)
      (by rw [haS0, hmem1e]; exact hs06) (by rw [haS0, hmem1e]; exact hs07) hi1
  have hstep2 : Step ⟨σ1, i1, c.steps+1⟩ ⟨σ2, i2, c.steps+1+1⟩ := hstep2'
  have hmem2e : σ2.mem = mpre := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800033f4#64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x800033f0#64) 4 = (0x800033f4#64:BitVec 64) from by decide] at this
  have hx8_2 : σ2.regs.get? Register.x8 = some v8 := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs0Sext] at this
  have hra_2 : σ2.regs.get? Register.x1 = some r := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- ============ 0x800033f4: ld s2,1056(sp) → x18 := v18 ============
  obtain ⟨σ3, i3, hstep3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800033f4_ee σ2 i2 (c.steps + 1 + 1) (0x800033f4#64) vmi2 (sp-1088#64) s20 s21 s22 s23 s24 s25 s26 s27
      hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [haS2]; omega) (by rw [haS2]; omega) (by rw [haS2, htoh]; right; omega) (by rw [haS2]; omega)
      (by rw [haS2, hmem2e]; exact hs20) (by rw [haS2, hmem2e]; exact hs21) (by rw [haS2, hmem2e]; exact hs22)
      (by rw [haS2, hmem2e]; exact hs23) (by rw [haS2, hmem2e]; exact hs24) (by rw [haS2, hmem2e]; exact hs25)
      (by rw [haS2, hmem2e]; exact hs26) (by rw [haS2, hmem2e]; exact hs27) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps+1+1⟩ ⟨σ3, i3, c.steps+1+1+1⟩ := hstep3'
  have hmem3e : σ3.mem = mpre := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x800033f8#64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x800033f4#64) 4 = (0x800033f8#64:BitVec 64) from by decide] at this
  have hx18_3 : σ3.regs.get? Register.x18 = some v18 := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs2Sext] at this
  have hra_3 : σ3.regs.get? Register.x1 = some r := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hx8_3 : σ3.regs.get? Register.x8 = some v8 := obs_alu_other' hobs3 Register.x8 (by decide) hx8_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- ============ 0x800033f8: mv a0,s1 → x10 := sret ============
  obtain ⟨σ4, i4, hstep4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800033f8_ee σ3 i3 (c.steps + 1 + 1 + 1) (0x800033f8#64) vmi3 sret hG3 hpc3 hmi3 hs1_3 hcode3 rfl hi3
  have hstep4 : Step ⟨σ3, i3, c.steps+1+1+1⟩ ⟨σ4, i4, c.steps+1+1+1+1⟩ := hstep4'
  have hmem4e : σ4.mem = mpre := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x800033fc#64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x800033f8#64) 4 = (0x800033fc#64:BitVec 64) from by decide] at this
  have ha0_4 : σ4.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by rw [sext_zero, BitVec.add_zero]] at this
  have hra_4 : σ4.regs.get? Register.x1 = some r := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs4 Register.x2 (by decide) hsp_3
  have hx8_4 : σ4.regs.get? Register.x8 = some v8 := obs_alu_other' hobs4 Register.x8 (by decide) hx8_3
  have hx18_4 : σ4.regs.get? Register.x18 = some v18 := obs_alu_other' hobs4 Register.x18 (by decide) hx18_3
  obtain ⟨vmi4, hmi4⟩ := obs_alu_minstret hobs4
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- ============ 0x800033fc: ld s1,1064(sp) → x9 := v9 ============
  obtain ⟨σ5, i5, hstep5', hi5, hG5, hmem5, hobs5⟩ :=
    site_800033fc_ee σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800033fc#64) vmi4 (sp-1088#64) s10 s11 s12 s13 s14 s15 s16 s17
      hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haS1]; omega) (by rw [haS1]; omega) (by rw [haS1, htoh]; right; omega) (by rw [haS1]; omega)
      (by rw [haS1, hmem4e]; exact hs10) (by rw [haS1, hmem4e]; exact hs11) (by rw [haS1, hmem4e]; exact hs12)
      (by rw [haS1, hmem4e]; exact hs13) (by rw [haS1, hmem4e]; exact hs14) (by rw [haS1, hmem4e]; exact hs15)
      (by rw [haS1, hmem4e]; exact hs16) (by rw [haS1, hmem4e]; exact hs17) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps+1+1+1+1⟩ ⟨σ5, i5, c.steps+1+1+1+1+1⟩ := hstep5'
  have hmem5e : σ5.mem = mpre := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003400#64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x800033fc#64) 4 = (0x80003400#64:BitVec 64) from by decide] at this
  have hx9_5 : σ5.regs.get? Register.x9 = some v9 := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [hs1Sext] at this
  have ha0_5 : σ5.regs.get? Register.x10 = some sret := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have hra_5 : σ5.regs.get? Register.x1 = some r := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  have hx8_5 : σ5.regs.get? Register.x8 = some v8 := obs_alu_other' hobs5 Register.x8 (by decide) hx8_4
  have hx18_5 : σ5.regs.get? Register.x18 = some v18 := obs_alu_other' hobs5 Register.x18 (by decide) hx18_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  -- ============ 0x80003400: addi sp,sp,1088 → x2 := sp ============
  obtain ⟨σ6, i6, hstep6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80003400_ee σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80003400#64) vmi5 (sp-1088#64) hG5 hpc5 hmi5 hsp_5 hcode5 rfl hi5
  have hstep6 : Step ⟨σ5, i5, c.steps+1+1+1+1+1⟩ ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ := hstep6'
  have hmem6e : σ6.mem = mpre := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003404#64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80003400#64) 4 = (0x80003404#64:BitVec 64) from by decide] at this
  have hsp_6 : σ6.regs.get? Register.x2 = some sp := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide); rwa [sp_add1088] at this
  have ha0_6 : σ6.regs.get? Register.x10 = some sret := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have hra_6 : σ6.regs.get? Register.x1 = some r := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have hx9_6 : σ6.regs.get? Register.x9 = some v9 := obs_alu_other' hobs6 Register.x9 (by decide) hx9_5
  have hx8_6 : σ6.regs.get? Register.x8 = some v8 := obs_alu_other' hobs6 Register.x8 (by decide) hx8_5
  have hx18_6 : σ6.regs.get? Register.x18 = some v18 := obs_alu_other' hobs6 Register.x18 (by decide) hx18_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  -- ============ 0x80003404: ret → PC := r ============
  have hrettgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r hraAl]; exact hraAl
  obtain ⟨σ7, i7, hstep7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80003404_ee σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003404#64) vmi6 r hG6 hpc6 hmi6 hra_6 hcode6 rfl hrettgt hi6
  have hstep7 : Step ⟨σ6, i6, c.steps+1+1+1+1+1+1⟩ ⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩ := hstep7'
  have hmem7e : σ7.mem = mpre := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1) := obs_jr_pc hobs7
  have ha0_7 : σ7.regs.get? Register.x10 = some sret := obs_jr_other' hobs7 Register.x10 (by decide) ha0_6
  have hra_7 : σ7.regs.get? Register.x1 = some r := obs_jr_other' hobs7 Register.x1 (by decide) hra_6
  have hsp_7 : σ7.regs.get? Register.x2 = some sp := obs_jr_other' hobs7 Register.x2 (by decide) hsp_6
  have hx8_7 : σ7.regs.get? Register.x8 = some v8 := obs_jr_other' hobs7 Register.x8 (by decide) hx8_6
  have hx9_7 : σ7.regs.get? Register.x9 = some v9 := obs_jr_other' hobs7 Register.x9 (by decide) hx9_6
  have hx18_7 : σ7.regs.get? Register.x18 = some v18 := obs_jr_other' hobs7 Register.x18 (by decide) hx18_6
  obtain ⟨vmi7, hmi7⟩ := obs_jr_minstret hobs7
  -- output invariance through the 7 epilogue steps
  have hout7 : σ7.sailOutput = out0 := by
    rw [hobs7.out, sailOutput_sigmaPost_jump_x0, hobs6.out, sailOutput_sigmaPost_alu,
      hobs5.out, sailOutput_sigmaPost_alu, hobs4.out, sailOutput_sigmaPost_alu,
      hobs3.out, sailOutput_sigmaPost_alu, hobs2.out, sailOutput_sigmaPost_alu,
      hobs1.out, sailOutput_sigmaPost_alu]; exact hout
  -- epilogue register frame: callee-saved (excl x8/x9/x18/x2/x1/x10) unchanged.
  -- x1/x10 restored to r/sret; x8/x9/x18/x2 to their g-values; all others = mpre-carried g.
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  have hframe7 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false → (Register.x1 == R) = false →
      σ7.regs.get? R = c.σ.regs.get? R := by
    intro R hR he8 he9 he18 he2 he1
    have hab : AbiPreserved R = true := hR.1
    have h10 : (Register.x10 == R) = false := abi_ne' (by decide) hab
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have a : ∀ {σa σb : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd},
        ReadsLikePost σb (sigmaPost_alu σa pc vm rd v) → (rd == R) = false →
        σb.regs.get? R = σa.regs.get? R := fun ho hrd =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hrd hnpc' hmii')
    have jr : ∀ {σa σb : MState} {pc vm tgt : BitVec 64},
        ReadsLikePost σb (sigmaPost_jump_x0 σa pc vm tgt) →
        σb.regs.get? R = σa.regs.get? R := fun ho =>
      (ho.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    exact (jr hobs7).trans ((a hobs6 he2).trans ((a hobs5 he9).trans ((a hobs4 h10).trans
      ((a hobs3 he18).trans ((a hobs2 he8).trans (a hobs1 he1))))))
  -- assemble EvalExit (paired with the carried memory predicate `Q c.σ.mem`,
  -- transported from `Q mpre` through the memory-pure epilogue via `hmem7e`).
  refine ⟨⟨σ7, i7, c.steps+1+1+1+1+1+1+1⟩, ?_, ⟨hG7, hi7, hpc7, ha0_7, hra_7, hsp_7, ⟨_, hmi7⟩,
    ⟨φc, PhiExtends.refl _ _, ?_⟩, ⟨φf, φc, PhiExtends.refl _ _, PhiExtends.refl _ _, ?_⟩,
    ?_, ?_, ?_⟩, by rw [show σ7.mem = mpre from hmem7e]; exact hQ⟩
  · exact (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
      (Steps.single hstep7))))))
  · rw [hmem7e]; exact hval        -- ValueRepr result
  · rw [hmem7e]; exact hstore      -- StoreRepr store
  · -- OutRepr σ7 st: output is `sailOutput`-based, σ7.sailOutput = out0, and
    -- `String.join out0.toList = st.out`.
    show Vsa.Machine.output σ7 = st.out
    simp only [Vsa.Machine.output]; rw [hout7]; exact houtStr
  · -- EvalExit.frame: every AbiPreservedNoise R = g R at exit
    intro R hR
    by_cases h8 : (Register.x8 == R) = true
    · have : R = Register.x8 := by rw [beq_iff_eq] at h8; exact h8.symm
      subst this; rw [hx8_7]; exact hgx8.symm
    by_cases h9 : (Register.x9 == R) = true
    · have : R = Register.x9 := by rw [beq_iff_eq] at h9; exact h9.symm
      subst this; rw [hx9_7]; exact hgx9.symm
    by_cases h18 : (Register.x18 == R) = true
    · have : R = Register.x18 := by rw [beq_iff_eq] at h18; exact h18.symm
      subst this; rw [hx18_7]; exact hgx18.symm
    by_cases h2 : (Register.x2 == R) = true
    · have : R = Register.x2 := by rw [beq_iff_eq] at h2; exact h2.symm
      subst this; rw [hsp_7]; exact hgx2.symm
    · -- x1 is NOT AbiPreserved, so `(x1 == R) = false` for AbiPreservedNoise R.
      have h1 : (Register.x1 == R) = false := abi_ne' (by decide) hR.1
      rw [hframe7 R hR (by simpa using h8) (by simpa using h9) (by simpa using h18)
        (by simpa using h2) h1]
      exact hframe R hR (by simpa using h8) (by simpa using h9) (by simpa using h18) (by simpa using h2)
  · -- memFrame
    intro a hstk harena; rw [hmem7e]; exact hmemframe a hstk harena

/-- `Eval_exprLoaded` transfers along a memory agreement covering the code region
`[0x80003164, 0x80003fe0)`. Used by `armTail_v` (and block C): the callee's sret
write agrees with the arm-entry memory everywhere outside `[sret, sret+24)`, which
(being disjoint from the text) covers the whole code region. -/
theorem loaded_eval_expr_agreeP (m m' : Mem)
    (ha : ∀ a, (0x80003164 ≤ a ∧ a < 0x80003fe0) → m[a]? = m'[a]?)
    (h : Eval_exprLoaded m) : Eval_exprLoaded m' := by
  obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
    c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38,
    c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eval_exprChunk0] at c0 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk1] at c1 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk2] at c2 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk3] at c3 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk4] at c4 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk5] at c5 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk6] at c6 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk7] at c7 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk8] at c8 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk9] at c9 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk10] at c10 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk11] at c11 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk12] at c12 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk13] at c13 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk14] at c14 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk15] at c15 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk16] at c16 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk17] at c17 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk18] at c18 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk19] at c19 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk20] at c20 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk21] at c21 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk22] at c22 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk23] at c23 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk24] at c24 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk25] at c25 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk26] at c26 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk27] at c27 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk28] at c28 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk29] at c29 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk30] at c30 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk31] at c31 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk32] at c32 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk33] at c33 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk34] at c34 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk35] at c35 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk36] at c36 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk37] at c37 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk38] at c38 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk39] at c39 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk40] at c40 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk41] at c41 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk42] at c42 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk43] at c43 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk44] at c44 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk45] at c45 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk46] at c46 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk47] at c47 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk48] at c48 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk49] at c49 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk50] at c50 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk51] at c51 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk52] at c52 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk53] at c53 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk54] at c54 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk55] at c55 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk56] at c56 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])
  · simp only [eval_exprChunk57] at c57 ⊢; repeat' apply And.intro
    all_goals (rw [← ha _ (by omega)]; simp_all only [])

/-! ## `jal`-observation consumers (local; mirror `DivSites2`'s `obs_jal_*`)

`obs_jal_*` proper live in `DivSites2` (imported later in the `EvalIntSim2`
chain), so `armTail_v` — which sits in this earlier file — recreates the four it
needs directly on `get?_sigmaPost_jal` (`StepJump`) + `readback` (`Muldi3Spec`),
under distinct names to avoid a clash when both files are imported. -/
theorem obs_jalT_pc {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    σ'.regs.get? Register.PC = some (pc + sign_extend (m := 64) imm) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide)
    (by
      show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
        Register.minstret (BitVec.addInt vm 1))).get? Register.PC = _
      rw [Std.ExtDHashMap.get?_insert]
      simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
      rw [Std.ExtDHashMap.get?_insert_self])

theorem obs_jalT_rd {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link))
    (hmc : (Register.mcycle == rd_reg) = false) (hmt : (Register.mtime == rd_reg) = false)
    (hmi : (Register.mip == rd_reg) = false)
    (h1 : (Register.minstret == rd_reg) = false) (h2 : (Register.PC == rd_reg) = false) :
    σ'.regs.get? rd_reg = some link :=
  readback σ' _ hobs rd_reg hmc hmt hmi
    (by
      show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
        Register.minstret (BitVec.addInt vm 1))).get? rd_reg = _
      rw [Std.ExtDHashMap.get?_insert]
      simp only [h1, dif_neg, reduceCtorEq, not_false_eq_true]
      rw [Std.ExtDHashMap.get?_insert]
      simp only [h2, dif_neg, reduceCtorEq, not_false_eq_true]
      show (((afterNextPC (afterPrelude σ) pc).regs.insert Register.nextPC
        (pc + sign_extend (m := 64) imm)).insert rd_reg link).get? rd_reg = _
      rw [Std.ExtDHashMap.get?_insert_self])

theorem obs_jalT_other {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h3 : (rd_reg == R) = false) (h4 : (Register.nextPC == R) = false)
    (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi
    ((get?_sigmaPost_jal σ pc vm imm rd_reg link R h1 h2 h3 h4 h5).trans hσ)

theorem obs_jalT_minstret {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_jal σ pc imm rd_reg link).regs.insert Register.PC (pc + sign_extend (m := 64) imm)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## `armTail_v` — the shared `jal <callee>; j 0x800033ec` arm tail

Every leaf `EvalE` arm, after its (optional) payload load, ends with exactly two
instructions: `jal <value_*>` (the callee that fills the sret buffer) and
`j 0x800033ec` (into the shared epilogue). `armTail_v` captures this tail once,
parameterized over:

* **`armPC`** — the `jal`'s PC (the arm entry, for `null` `0x8000342c`).
* **`calleeEntry`** — the callee's entry PC (`= armPC + sext jalImm`; `value_null`
  is `0x800027ec`).
* **`calleeLoaded`** — the arm-callee code predicate, carried through the tail.
* **`v`** — the produced `Value` (`.null`/`.bool _`/`.str _`/`.int _`).

The `jal`/`j` machine steps are supplied as the two per-arm `stepObs`-form
hypotheses `hjalSite`/`hjSite` (mirroring `site_8000342c_ee`/`site_80003430_ee`);
the callee is supplied as `hcallee`, a config-level behavior implication whose
post is exactly the strengthened `value_*` post (ValueRepr `v`, output preserved,
memory framed outside `[sret,sret+24)`, `NotWrittenV` register frame). This is
callee-agnostic: `int`/`bool`/`str` reuse it with their own `value_*` spec.

Input: the arm-entry state satisfies (the relevant subset of) `ArmEntryK` at
`armPC`, plus the four spill slots / geometry it threads. Output: `PreEpilogueV`
at `v`, ready for `blockD_v`.

The `jal` target is `calleeEntry = armPC + sext jalImm`, its link `armPC + 4`;
the `j` target is `0x800033ec = (armPC+4) + sext jImm`. The `calleeLink` is
`armPC + 4` (a `BitVec 64`). -/
theorem armTail_v
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (v : Value)
    (armPC calleeEntry calleeLink : BitVec 64) (jalImm jImm : BitVec 21) (calleeLoaded : Mem → Prop)
    (sp r sret : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String) (m0 : Mem)
    -- the `jal`/`j` target arithmetic, fixed by the arm (all `decide`-able concretely):
    (hjaltgt : (armPC + sign_extend (m := 64) jalImm) = calleeEntry)
    (hlink : (BitVec.addInt armPC 4) = calleeLink)
    (hlinkAl : calleeLink.toNat % 4 = 0)
    (hjtgt : (calleeLink + sign_extend (m := 64) jImm).toNat % 4 = 0)
    (hepitgt : (calleeLink + sign_extend (m := 64) jImm) = (0x800033ec#64 : BitVec 64))
    -- the two per-arm site steps (mirror `site_8000342c_ee` / `site_80003430_ee`):
    (hjalSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some armPC →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jal σ armPC vmi jalImm Register.x1 (BitVec.addInt armPC 4)))
    (hjSite : ∀ (σ : MState) (i u : Nat) (vmi : BitVec 64),
      GoodState σ → σ.regs.get? Register.PC = some calleeLink →
      σ.regs.get? Register.minstret = some vmi → Eval_exprLoaded σ.mem → i < 2 →
      ∃ (σ' : MState) (i' : Nat),
        Step ⟨σ, i, u⟩ ⟨σ', i', u + 1⟩ ∧ i' < 2 ∧ GoodState σ' ∧ σ'.mem = σ.mem ∧
        ReadsLikePost σ' (sigmaPost_jump_x0 σ calleeLink vmi (calleeLink + sign_extend (m := 64) jImm)))
    -- the callee behavior (strengthened `value_*` post): from `calleeEntry` it
    -- runs to a config landing back at `calleeLink` (bit-0-cleared), fills the
    -- sret buffer with `ValueRepr v`, preserves output, frames memory outside
    -- `[sret,sret+24)`, and preserves the `NotWrittenV` register set.
    (hcallee : ∀ (gc : (R : Register) → Option (RegisterType R)) (c : Config) (mc : Mem),
      GoodState c.σ → calleeLoaded c.σ.mem → c.σ.mem = mc →
      c.σ.regs.get? Register.PC = some calleeEntry →
      c.σ.regs.get? Register.x10 = some sret →
      c.σ.regs.get? Register.x1 = some calleeLink →
      (∃ w, c.σ.regs.get? Register.minstret = some w) → c.tick < 2 →
      c.σ.sailOutput = out0 →
      (∀ R : Register, NotWrittenV R → c.σ.regs.get? R = gc R) →
      ∃ c', Steps c c' ∧ GoodState c'.σ ∧
        c'.σ.regs.get? Register.PC =
          some (BitVec.update (calleeLink + sign_extend (m := 64) (0x000#12)) 0 0#1) ∧
        c'.σ.regs.get? Register.x10 = some sret ∧
        c'.σ.regs.get? Register.x1 = some calleeLink ∧
        (∃ w, c'.σ.regs.get? Register.minstret = some w) ∧ c'.tick < 2 ∧
        ValueRepr c'.σ.mem N φc sret.toNat v ∧
        c'.σ.sailOutput = out0 ∧
        (∀ k : Nat, ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → mc[k]? = c'.σ.mem[k]?) ∧
        (∀ R : Register, NotWrittenV R → c'.σ.regs.get? R = gc R)) :
    Triple
      (fun c => ∃ ment,
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some armPC ∧
        c.σ.regs.get? Register.x10 = some sret ∧           -- a0 = sret (preserved)
        c.σ.regs.get? Register.x9 = some sret ∧             -- s1 = sret
        c.σ.regs.get? Register.x2 = some (sp - 1088#64) ∧   -- sp lowered
        (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
        c.σ.sailOutput = out0 ∧
        c.σ.mem = ment ∧ Eval_exprLoaded ment ∧ calleeLoaded ment ∧
        String.join out0.toList = st.out ∧
        read64 ment (sp.toNat - 8) = some r.toNat ∧
        read64 ment (sp.toNat - 16) = some v8.toNat ∧
        read64 ment (sp.toNat - 24) = some v9.toNat ∧
        read64 ment (sp.toNat - 32) = some v18.toNat ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]?) ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
        g Register.x2 = some sp ∧
        StoreRepr ment N A φf φc st.store ∧
        (∀ m' : Mem,
          (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) →
            ment[k]? = m'[k]?) →
          StoreRepr m' N A φf φc st.store) ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          c.σ.regs.get? R = g R) ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        SL.lo + 1088 ≤ sp.toNat ∧
        1088 ≤ sp.toNat ∧ sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
        tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
        r.toNat % 4 = 0)
      (fun c => ∃ mpre, PreEpilogueV g N A SL φf φc st v sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨ment, hG, htick, hpc, ha0, hs1, hsp, ⟨vmi, hmi⟩, hout, hmem, hcode, hviCode,
    houtStr, hslotRa, hslotS0, hslotS1, hslotS2, hmemframe_m0,
    hgx8, hgx9, hgx18, hgx2, hstore, hstoreSurv, hframe,
    hsretStk, hsretEvalCode, hSLloSp,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩ := hpre
  -- ============ armPC: jal <callee> → PC := calleeEntry, x1 := calleeLink ============
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    hjalSite c.σ c.tick c.steps vmi hG hpc hmi (hmem ▸ hcode) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = ment := by rw [hmem1]; exact hmem
  have hpc1 : σ1.regs.get? Register.PC = some calleeEntry := by
    have := obs_jalT_pc hobs1; rwa [hjaltgt] at this
  have hlink1 : σ1.regs.get? Register.x1 = some calleeLink := by
    have := obs_jalT_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hlink] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some sret := obs_jalT_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_jalT_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp-1088#64) := obs_jalT_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  obtain ⟨vmi1, hmi1⟩ := obs_jalT_minstret hobs1
  have hviCode1 : calleeLoaded σ1.mem := by rw [hmem1e]; exact hviCode
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_jal]; exact hout
  -- ============ callee (value_* strengthened spec) ============
  obtain ⟨c2, hs2, hG2, hpc2, ha0_2, hlink2, ⟨vmi2, hmi2⟩, htick2, hval2, hout2, hmemframe2, hframe2⟩ :=
    hcallee (fun R => σ1.regs.get? R) ⟨σ1, i1, c.steps + 1⟩ ment
      hG1 hviCode1 hmem1e hpc1 ha0_1 hlink1 ⟨vmi1, hmi1⟩ hi1 hout1 (fun R _ => rfl)
  have hstep2 : Steps ⟨σ1, i1, c.steps + 1⟩ c2 := hs2
  have hpc2' : c2.σ.regs.get? Register.PC = some calleeLink := by
    rw [hpc2, ret_tgt calleeLink hlinkAl]
  -- recover callee-preserved regs: s1(x9), sp(x2) via NotWrittenV frame (= σ1 reads)
  have hs1_2 : c2.σ.regs.get? Register.x9 = some sret := by
    rw [hframe2 Register.x9 (by decide)]; exact hs1_1
  have hsp_2 : c2.σ.regs.get? Register.x2 = some (sp-1088#64) := by
    rw [hframe2 Register.x2 (by decide)]; exact hsp_1
  -- memory agreement ment ↔ c2.mem outside the sret buffer
  have hAgree : AgreeP (fun k => ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24)) ment c2.σ.mem :=
    fun k hk => hmemframe2 k hk
  -- spill slots survive the sret write (each 8-byte slot disjoint from [sret,sret+24))
  have hslotRa2 : read64 c2.σ.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotRa
  have hslotS02 : read64 c2.σ.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS0
  have hslotS12 : read64 c2.σ.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS1
  have hslotS22 : read64 c2.σ.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hAgree (fun j hj => by rcases hsretStk with h | h <;> omega)]; exact hslotS2
  -- StoreRepr survives: c2.mem agrees with ment outside window∪sret (⊇ outside sret)
  have hstore2 : StoreRepr c2.σ.mem N A φf φc st.store :=
    hstoreSurv c2.σ.mem (fun k _ hk2 => hmemframe2 k hk2)
  -- Eval_exprLoaded survives (code region disjoint from sret; ment loaded)
  have hcode2 : Eval_exprLoaded c2.σ.mem :=
    loaded_eval_expr_agreeP ment c2.σ.mem
      (fun k hk => hmemframe2 k (by rcases hsretEvalCode with h | h <;> omega)) (hmem ▸ hcode)
  -- ============ calleeLink: j 0x800033ec → PC := 0x800033ec ============
  obtain ⟨c3, i3', hs3, hi3, hG3, hmem3, hobs3⟩ :=
    hjSite c2.σ c2.tick c2.steps vmi2 hG2 hpc2' hmi2 hcode2 htick2
  have hstep3 : Step c2 ⟨c3, i3', c2.steps + 1⟩ := by cases c2; exact hs3
  have hmem3e : c3.mem = c2.σ.mem := hmem3
  have hpc3 : c3.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs3; rwa [hepitgt] at this
  have hs1_3 : c3.regs.get? Register.x9 = some sret := obs_jr_other' hobs3 Register.x9 (by decide) hs1_2
  have hsp_3 : c3.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_jr_minstret hobs3
  have hout3 : c3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_jump_x0]; exact hout2
  -- assemble PreEpilogueV at `v`
  refine ⟨⟨c3, i3', c2.steps + 1⟩, ?_, c3.mem, hG3, hi3, hpc3, hs1_3, hsp_3, ⟨_, hmi3⟩, hout3, houtStr,
    rfl, hmem3e ▸ hcode2, hmem3e ▸ hval2, hmem3e ▸ hstore2,
    ?_,  -- the g-frame at the epilogue
    hmem3e ▸ hslotRa2, hmem3e ▸ hslotS02, hmem3e ▸ hslotS12, hmem3e ▸ hslotS22,
    hgx8, hgx9, hgx18, hgx2, ?_,
    hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩
  · -- the composed run: step1(jal) ; callee steps ; step3(j)
    exact (Steps.single hstep1).trans (hstep2.trans (Steps.single hstep3))
  · -- the epilogue g-frame: callee-saved (excl x8/x9/x18/x2) preserved across the tail.
    intro R hR he8 he9 he18 he2
    have hab : AbiPreserved R = true := hR.1
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    have hx11 : (Register.x11 == R) = false := abi_ne' (by decide)
    have hx15 : (Register.x15 == R) = false := abi_ne' (by decide)
    have hx1 : (Register.x1 == R) = false := abi_ne' (by decide)
    obtain ⟨_, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    -- σ1: jal writes x1
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1 hnpc' hmii')
    -- c2: callee NotWrittenV frame
    have f2 : c2.σ.regs.get? R = σ1.regs.get? R := by
      rw [hframe2 R ⟨hx11, hx15, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩]
    -- c3: j writes PC
    have f3 : c3.regs.get? R = c2.σ.regs.get? R :=
      (hobs3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f3, f2, f1]
    exact hframe R ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ he8 he9 he18 he2
  · -- memFrame: mpre (= c3.mem = c2.mem) vs m0. In sret → left; else compose.
    intro a ha _
    rw [hmem3e]
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · -- outside sret: c2.mem = ment (via memframe2), then ment vs m0 (arm-entry memFrame).
      exact Or.inr ((hmemframe2 a hsr).symm.trans (hmemframe_m0 a ha))

end Vsa.Sim
