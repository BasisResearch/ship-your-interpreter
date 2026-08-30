import Vsa.Sim.StrcpySites
import Vsa.Sim.MemcpySpec
import Vsa.Sim.StrlenSpec
import Vsa.Triple
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcpy` byte-head-path total-correctness spec (`strcpy_bytehead_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/StrcpySites.lean`) into a total-correctness triple for the **byte-head
copy path** of newlib `strcpy` — the path taken when the source/destination
alignment fast-path does not apply (`(dst ||| src) & 7 ≠ 0`).

This mirrors `memcpy`'s byte-copy path (`MemcpySpec.lean`) but the length is
**discovered**, not given: the loop is a bottom-tested do-while whose exit is the
`bnez a4` on the just-loaded byte — it copies `s.length` characters *plus* the NUL
terminator, `s.length + 1` bytes total, into `[dst, dst + s.length]`.

## The byte-head loop (`[0x80006e7c, 0x80006e94)`, back-edge `0x90 → 0x80`)

* `0xe7c`: `mv a5,a0`      — `a5 := dst` (preamble, once)
* `0xe80`: `lbu a4,0(a1)`  — loop head: `a4 := zext (byte at a1 = src+i)`
* `0xe84`: `addi a5,a5,1`  — `a5 := dst + (i+1)`
* `0xe88`: `addi a1,a1,1`  — `a1 := src + (i+1)`
* `0xe8c`: `sb a4,-1(a5)`  — store the byte at `a5-1 = dst+i`
* `0xe90`: `bnez a4,0xe80` — loop back iff the stored byte ≠ 0 (more to copy)
* `0xe94`: `ret`           — the just-stored byte was the NUL (`i = s.length`)

So at loop head `0xe80` iteration `i` (`0 ≤ i ≤ len`): `a0 = dst`, `a1 = src+i`,
`a5 = dst+i`; the copied prefix `[dst, dst+i)` holds the source bytes; and byte
`i` is `bs i` (the string char for `i < len`, `0` at `i = len`). The `bnez` exits
exactly when `bs i = 0`, i.e. `i = len`, after storing the NUL at `dst+len`.

## TRUE dst footprint

The byte-head path writes **exactly `len + 1` bytes** `[dst, dst+len]` — the `len`
characters and the terminating NUL. (The `sb zero,7(a2)` finisher at `0x80006e98`
belongs to the *word-loop* byte tail, NOT this path; the byte-head loop's `sb`
writes the NUL itself as its final iteration.)

## Ghost parameters

`dst` (x10 in), `src` (x11 in), `s : String` (`CString m0 src s`), `r` (x1, return
addr, 4-aligned), `m0` (pinned memory), `bs : Nat → BitVec 8` (the offset→byte
function, `bs k = char k` for `k < len`, `bs len = 0`).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr (CStr CString Mem)
open Vsa.Sim.Code (StrcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `StrcpyLoaded` preserved by a single byte insert outside the code region

The `strcpy` code lives in `[0x80006dc4, 0x80006ea0)`. A byte store outside that
range preserves every code-byte read (each concrete code address differs from the
out-of-range key by `omega`). -/
theorem strcpy_loaded_insert (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : k < 0x80006dc4 ∨ 0x80006ea0 ≤ k) (h : StrcpyLoaded mem) :
    StrcpyLoaded (mem.insert k v) := by
  obtain ⟨c0, c1, c2, c3⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Vsa.Sim.Code.strcpyChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [Vsa.Sim.Code.strcpyChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [Vsa.Sim.Code.strcpyChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [Vsa.Sim.Code.strcpyChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])

/-! ## The string byte-function ghost

`StrBytes m0 src len bs` packages what `CString` gives us about the source bytes,
in the offset→byte form the copy consumes:
* `chars`: byte `k < len` reads `bs k` (nonzero) from `src + k`;
* `nul`: byte `len` reads `bs len = 0` (the NUL) from `src + len`.

`bs len = 0` is recorded separately (`bs_nul`) so the `bnez` exit can fire. -/
structure StrBytes (m0 : Mem) (src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) : Prop where
  chars : ∀ k, k < len → m0[(src.toNat + k)]? = some (bs k) ∧ bs k ≠ 0
  nul : m0[(src.toNat + len)]? = some (bs len)
  bs_nul : bs len = 0

/-- Extract a `StrBytes` witness from a `CString`, taking `bs k := (m0[src+k]?).getD 0`
(the actual memory byte).  The returned `len` is `s.length`.  This is the bridge a
caller uses to obtain the ghost byte function from the `CString` hypothesis. -/
theorem cstring_bytes (m0 : Mem) (src : BitVec 64) (s : String) (h : CString m0 src.toNat s) :
    ∃ (len : Nat) (bs : Nat → BitVec 8), len = s.length ∧ StrBytes m0 src len bs := by
  obtain ⟨cs, hcs, hs⟩ := h
  have hlen : cs.length = s.length := by rw [hs, String.length_ofList]
  refine ⟨cs.length, fun k => (m0[(src.toNat + k)]?).getD 0, hlen, ?_, ?_, ?_⟩
  · -- chars: byte k < len is the (nonzero) char byte
    intro k hk
    obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m0 hcs k hk
    refine ⟨?_, ?_⟩
    · rw [hb]; simp only [Option.getD_some]
    · rw [hb]; simp only [Option.getD_some]; simpa using hbne
  · -- nul: byte at length is 0
    rw [cstr_byte_nul m0 hcs]; simp only [Option.getD_some]
  · -- bs len = 0
    simp only [cstr_byte_nul m0 hcs, Option.getD_some]

/-! ## Region / no-wrap side conditions for the byte-head path

`CpyRegions dst src len` bundles the disjointness / no-wrap facts.  The written
region is `[dst, dst+len]` (`len+1` bytes); the read region is `[src, src+len]`.
Both live in RAM above the HTIF window and disjoint from the `strcpy` code
`[0x80006dc4, 0x80006ea0)`; the two regions are mutually disjoint. -/
structure CpyRegions (dst src : BitVec 64) (len : Nat) : Prop where
  dst_nowrap : dst.toNat + len + 1 < 2^64
  src_nowrap : src.toNat + len + 1 < 2^64
  disjoint : dst.toNat + len + 1 ≤ src.toNat ∨ src.toNat + len + 1 ≤ dst.toNat
  code_disjoint : dst.toNat + len + 1 ≤ 0x80006dc4 ∨ 0x80006ea0 ≤ dst.toNat
  dst_lo : 0x80000000 ≤ dst.toNat
  dst_hi : dst.toNat + len + 1 ≤ 0x100000000
  src_lo : 0x80000000 ≤ src.toNat
  src_hi : src.toNat + len + 1 ≤ 0x100000000
  dst_win : tohostAddr + 16 ≤ dst.toNat
  src_win : tohostAddr + 16 ≤ src.toNat

/-! ## The copied-prefix memory invariant

`CpyInv dst src len bs i m0 mem` describes `mem` at byte-head iteration `i`
(`0 ≤ i ≤ len`):
* `copied`: `[dst, dst+i)` holds the copied bytes `bs`;
* `outside`: every address outside `[dst, dst+len]` still reads `m0`;
* `src_intact`: the source bytes `[src+i, src+len]` still read from `m0` (the
  copy never touches the source: disjoint regions). -/
structure CpyInv (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  copied : ∀ k, k < i → mem[(dst.toNat + k)]? = some (bs k)
  outside : ∀ a, (a < dst.toNat ∨ dst.toNat + len < a) → mem[a]? = m0[a]?
  src_intact : ∀ k, i ≤ k → k ≤ len → mem[(src.toNat + k)]? = m0[(src.toNat + k)]?

/-- **Store preserves the copied-prefix invariant** (disjointness-only form,
shared with the `memmove` byte loop in `SnprintfSpec18`). Storing byte `bs i` at
`dst + i` (`i ≤ len`) re-establishes `CpyInv … (i+1)` for `mem.insert (dst+i) (bs i)`. -/
theorem cpyinv_store' (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hdisj : dst.toNat + len + 1 ≤ src.toNat ∨ src.toNat + len + 1 ≤ dst.toNat) (hi : i ≤ len)
    (hinv : CpyInv dst src len bs i m0 mem) :
    CpyInv dst src len bs (i + 1) m0 (mem.insert (dst.toNat + i) (bs i)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hik : k = i
    · subst hik; simp only [beq_self_eq_true, if_true]
    · have hne : ((dst.toNat + i) == (dst.toNat + k)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
      exact hinv.copied k (by omega)
  · intro a ha
    rw [Std.ExtHashMap.getElem?_insert]
    have hne : ((dst.toNat + i) == a) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv.outside a ha
  · intro k hik hkn
    rw [Std.ExtHashMap.getElem?_insert]
    have hne : ((dst.toNat + i) == (src.toNat + k)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      rcases hdisj with hd | hd <;> omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv.src_intact k (by omega) hkn

/-- `cpyinv_store` with the disjointness taken from `CpyRegions`. -/
theorem cpyinv_store (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hreg : CpyRegions dst src len) (hi : i ≤ len)
    (hinv : CpyInv dst src len bs i m0 mem) :
    CpyInv dst src len bs (i + 1) m0 (mem.insert (dst.toNat + i) (bs i)) :=
  cpyinv_store' dst src len bs i m0 mem hreg.disjoint hi hinv

/-! ## Blanket ghost-frame predicate (`NotWrittenCpy`) + generic per-class helpers

The byte-head path writes GPRs `x15` (`a5`), `x14` (`a4`), `x11` (`a1`).  `x10`
(`a0 = dst`) and `x1` (`ra`) are preserved.  `NotWrittenCpy R` is the disequality
conjunction over `{x11, x14, x15}` and the per-step noise write-set
`{PC, nextPC, minstret, minstret_increment, mcycle, mtime, mip}`.  The STORE writes
only memory (no `rd`), covered by the noise disequalities alone. -/
abbrev NotWrittenCpy (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x14 == R) = false ∧
  (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenCpy.x11 {R : Register} (h : NotWrittenCpy R) : (Register.x11 == R) = false := h.1
theorem NotWrittenCpy.x14 {R : Register} (h : NotWrittenCpy R) : (Register.x14 == R) = false := h.2.1
theorem NotWrittenCpy.x15 {R : Register} (h : NotWrittenCpy R) : (Register.x15 == R) = false := h.2.2.1

theorem frame_alu_cpy {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenCpy R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

theorem frame_store_cpy {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenCpy R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

theorem frame_btaken_cpy {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenCpy R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

theorem frame_bnottaken_cpy {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenCpy R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

theorem frame_jr_cpy {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenCpy R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## Store-byte identity: `stData 1 (zext b) = b` -/

/-- The stored low byte of `a4 = zero_extend b` is `b` (as `BitVec (8*1)`). -/
theorem stData_zext (b : BitVec 8) :
    stData 1 (zero_extend (m := 64) (b : BitVec (8*1))) = (b : BitVec (8*1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [stData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth, Nat.shiftRight_zero]
  have hlt : (b : BitVec 8).toNat < 2^8 := b.isLt
  rw [BitVec.toNat_ofNat]
  generalize hE : ((((1:Nat) : Int) * 8 - 1).toNat - 0 + 1) = E
  have hE8 : E = 8 := by rw [← hE]; decide
  subst hE8
  have hp : (2:Nat)^(8*1) = 2^8 := by decide
  rw [hp, Nat.mod_eq_of_lt (show (b:BitVec 8).toNat < 2^64 from by omega),
      Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt]

/-- `sbAddr (base + ofNat (i+1))` via the site's raw `+ sext 0xfff`: `= base + ofNat i`. -/
theorem sbAddr_succ_raw (base : BitVec 64) (i : Nat) :
    (base + BitVec.ofNat 64 (i + 1)) + sign_extend (m := 64) (0xfff#12) = base + BitVec.ofNat 64 i := by
  have := sbAddr_succ base i
  simpa only [sbAddr] using this

/-! ## The config-level state predicate at the loop head `0x80006e80`

`StCpy g pc i r dst src len m0 bs c` bundles the standing observation at byte-head
iteration `i` (`0 ≤ i ≤ len`): `GoodState`, code loaded, PC, `a0 = dst`,
`a1 = src+i`, `a5 = dst+i`, `x1 = r`, `minstret` defined, `tick < 2`, `CpyRegions`,
`StrBytes`, `i ≤ len`, the copied-prefix invariant `CpyInv … i`, and the blanket
ghost frame.  `a4 = x14` is the scratch loaded byte (not tracked across the head). -/
structure StCpy (g : (R : Register) → Option (RegisterType R)) (pc : BitVec 64) (i : Nat)
    (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 i)
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 i)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpyRegions dst src len
  strbytes : StrBytes m0 src len bs
  ile : i ≤ len
  cpyinv : CpyInv dst src len bs i m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-! ## Pointer/window bounds for iteration `i`

The `lbu` reads at `src + i` (`i ≤ len`, so `src+i` is in RAM/above HTIF); the `sb`
writes at `a5 - 1 = dst + i`.  `ptr_toNat` bridges `.toNat`. -/

theorem cpy_src_bounds (dst src : BitVec 64) (len : Nat) (hreg : CpyRegions dst src len)
    (i : Nat) (hi : i ≤ len) :
    (src + BitVec.ofNat 64 i).toNat = src.toNat + i ∧
    0x80000000 ≤ (src + BitVec.ofNat 64 i).toNat ∧
    (src + BitVec.ofNat 64 i).toNat + 1 ≤ 0x100000000 ∧
    ((src + BitVec.ofNat 64 i).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (src + BitVec.ofNat 64 i).toNat) := by
  have htn : (src + BitVec.ofNat 64 i).toNat = src.toNat + i :=
    ptr_toNat src i (by have := hreg.src_nowrap; omega)
  have hlo := hreg.src_lo; have hhi := hreg.src_hi; have hwin := hreg.src_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, by rw [htn]; omega, by rw [htn]; omega, Or.inr (by rw [htn]; omega)⟩

theorem cpy_dst_bounds (dst src : BitVec 64) (len : Nat) (hreg : CpyRegions dst src len)
    (i : Nat) (hi : i ≤ len) :
    0x80000000 ≤ ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat ∧
    ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat + 1 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat ∧
    ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat = dst.toNat + i := by
  have hsb : ((dst + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12)).toNat = dst.toNat + i := by
    rw [sbAddr_succ_raw dst i]; exact ptr_toNat dst i (by have := hreg.dst_nowrap; omega)
  have hlo := hreg.dst_lo; have hhi := hreg.dst_hi; have hwin := hreg.dst_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by rw [hsb]; omega, by rw [hsb]; omega, by rw [hsb]; omega, hsb⟩

/-! ## State at `0x80006e90` (pre-`bnez`) for iteration `i`

After one loop body (lbu/addi a5/addi a1/sb) for iteration `i ≤ len`: `a1 = src+(i+1)`,
`a5 = dst+(i+1)`, `a4 = zext (bs i)`, and the copied prefix has advanced to `i+1`. -/
structure StCpy90 (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006e90#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (i + 1))
  a4 : c.σ.regs.get? Register.x14 = some (zero_extend (m := 64) ((bs i) : BitVec (8*1)))
  a5 : c.σ.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (i + 1))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpyRegions dst src len
  strbytes : StrBytes m0 src len bs
  ile : i ≤ len
  cpyinv : CpyInv dst src len bs (i + 1) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-- `x + sign_extend (0x000#12) = x` (the `lbu ..,0(a1)` immediate is zero). -/
theorem add_sext0 (x : BitVec 64) : x + sign_extend (m := 64) (0x000#12) = x := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
    apply BitVec.eq_of_toNat_eq; decide]
  exact BitVec.add_zero x

/-- Byte `i ≤ len` of the string reads `bs i` from `m0` (char or NUL). -/
theorem strbytes_byte (m0 : Mem) (src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8)
    (hsb : StrBytes m0 src len bs) (i : Nat) (hi : i ≤ len) :
    m0[(src.toNat + i)]? = some (bs i) := by
  rcases Nat.lt_or_ge i len with h | h
  · exact (hsb.chars i h).1
  · have : i = len := by omega
    subst this; exact hsb.nul

/-! ## One loop body iteration (`0x80006e80 → 0x80006e90`)

Chains `lbu a4 → addi a5 → addi a1 → sb a4,-1(a5)`.  The `lbu` reads `bs i` from
`src+i`; the two `addi`s advance `a5`/`a1`; the `sb` writes `bs i` at `dst+i`
(`sbAddr_succ_raw`), and `cpyinv_store` re-establishes `CpyInv … (i+1)`. -/
theorem iterCpy (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (hi : i ≤ len) :
    Triple (StCpy g (0x80006e80#64) i r dst src len m0 bs) (StCpy90 g i r dst src len m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha5, hra, ⟨vmi, hmi⟩, htick,
    hreg, hstrb, hile, hcinv, hframe⟩ := hSt
  obtain ⟨htn_src, hslo0, hshi0, hshtif0⟩ := cpy_src_bounds dst src len hreg i hi
  obtain ⟨hdlo, hdhi, hdwin, hsbeq⟩ := cpy_dst_bounds dst src len hreg i hi
  rw [← add_sext0 (src + BitVec.ofNat 64 i)] at hslo0 hshi0 hshtif0
  have hslo := hslo0; have hshi := hshi0; have hshtif := hshtif0
  -- the loaded byte b = bs i (src_intact at index i)
  have hbyte : c.σ.mem[(src + BitVec.ofNat 64 i + sign_extend (m := 64) (0x000#12)).toNat]? = some (bs i) := by
    rw [add_sext0, htn_src]
    rw [hcinv.src_intact i (Nat.le_refl i) hi]
    exact strbytes_byte m0 src len bs hstrb i hi
  -- === e80: lbu a4,0(a1) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006e80 c.σ c.tick c.steps (0x80006e80#64) vmi (src + BitVec.ofNat 64 i) (bs i)
      hgood hpc hmi ha1 hloaded rfl hslo hshi hshtif hbyte htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006e84#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006e80#64) 4 = (0x80006e84#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha5_1 := obs_alu_other' hobs1 Register.x15 (by decide) ha5
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha4_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === e84: addi a5,a5,1 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006e84 σ1 i1 (c.steps + 1) (0x80006e84#64) vmi1 (dst + BitVec.ofNat 64 i)
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006e88#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006e84#64) 4 = (0x80006e88#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (dst + BitVec.ofNat 64 (i + 1)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_succ dst i] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === e88: addi a1,a1,1 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006e88 σ2 i2 (c.steps + 1 + 1) (0x80006e88#64) vmi2 (src + BitVec.ofNat 64 i)
      hG2 hpc2 hmi2' ha1_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006e8c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006e88#64) 4 = (0x80006e8c#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha1_3 : σ3.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (i + 1)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_succ src i] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- σ3.mem = c.σ.mem (three regs-only steps)
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  -- === e8c: sb a4,-1(a5) === (a4 = zext (bs i), a5 = dst+(i+1))
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006e8c σ3 i3 (c.steps + 1 + 1 + 1) (0x80006e8c#64) vmi3
      (zero_extend (m := 64) ((bs i) : BitVec (8*1))) (dst + BitVec.ofNat 64 (i + 1))
      hG3 hpc3 hmi3' ha4_3 ha5_3 (by rw [hmem3eq]; exact hloaded) rfl
      hdlo hdhi hdwin hi3
  -- the store's post map, simplified
  have hstore_mem : σ4.mem = c.σ.mem.insert (dst.toNat + i) (bs i) := by
    rw [hmem4, mem_afterNextPC, hmem3eq, stData_zext, hsbeq]
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, ?_⟩
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006e90#64 : BitVec 64) := by
    have := obs_store_pc hobs4
    rwa [show BitVec.addInt (0x80006e8c#64) 4 = (0x80006e90#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_store_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_store_other' hobs4 Register.x11 (by decide) ha1_3
  have ha4_4 := obs_store_other' hobs4 Register.x14 (by decide) ha4_3
  have ha5_4 := obs_store_other' hobs4 Register.x15 (by decide) ha5_3
  have hra_4 := obs_store_other' hobs4 Register.x1 (by decide) hra_3
  refine ⟨hG4,
    by rw [hstore_mem]
       exact strcpy_loaded_insert c.σ.mem (dst.toNat + i) (bs i)
         (by have := hreg.code_disjoint; have := hreg.dst_nowrap; omega) hloaded,
    hpc4, ha0_4, ha1_4, ha4_4, ha5_4, hra_4, obs_store_minstret hobs4, hi4, hreg, hstrb, hi, ?_, ?_⟩
  · rw [hstore_mem]
    exact cpyinv_store dst src len bs i m0 c.σ.mem hreg hi hcinv
  · intro R hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_cpy hobs1 R hR.x14 hR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_cpy hobs2 R hR.x15 hR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_cpy hobs3 R hR.x11 hR
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_cpy hobs4 R hR
    rw [e4, e3, e2, e1]; exact hframe R hR

/-! ## The `bnez a4` at `0x80006e90` (loop back-edge / exit to ret)

`a4 = zext (bs i)`.  Taken iff `bs i ≠ 0` iff `i < len` (loop back to iteration
`i+1`); not-taken iff `bs i = 0` iff `i = len` (fall through to `ret` at `0xe94`
with the full described update `CpyInv … (len+1)`). -/

/-- `zext b ≠ 0` iff `b ≠ 0`. -/
theorem zext_ne_zero_iff (b : BitVec 8) :
    ((zero_extend (m := 64) (b : BitVec (8*1))) != (0#64)) = (b != 0#8) := by
  rcases Decidable.em (b = 0#8) with h | h
  · subst h
    simp only [bne_self_eq_false]
    rw [bne_eq_false_iff_eq]
    apply BitVec.eq_of_toNat_eq
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
    decide
  · rw [show (b != 0#8) = true from by rw [bne_iff_ne]; exact h]
    rw [bne_iff_ne, ne_eq]
    intro heq
    apply h
    apply BitVec.eq_of_toNat_eq
    have : (zero_extend (m := 64) (b : BitVec (8*1))).toNat = b.toNat := by
      simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth]
      exact Nat.mod_eq_of_lt (by have := b.isLt; omega)
    rw [heq] at this; simp only [BitVec.toNat_ofNat] at this ⊢; omega

/-- `bnez a4` taken (`i < len`): `bs i ≠ 0`, loop back to iteration `i+1`. -/
theorem tr_bnez_back (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (hlt : i < len) :
    Triple (StCpy90 g i r dst src len m0 bs) (StCpy g (0x80006e80#64) (i + 1) r dst src len m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha4, ha5, hra, ⟨vmi, hmi⟩, htick,
    hreg, hstrb, hile, hcinv, hframe⟩ := hSt
  have hbne : bs i ≠ 0 := (hstrb.chars i hlt).2
  have hv : ((zero_extend (m := 64) ((bs i) : BitVec (8*1))) != (0#64)) = true := by
    rw [zext_ne_zero_iff]; rw [bne_iff_ne]; exact hbne
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006e90_taken c.σ c.tick c.steps (0x80006e90#64) vmi
      (zero_extend (m := 64) ((bs i) : BitVec (8*1))) hgood hpc hmi ha4 hloaded rfl hv htick
  have hpceq : (0x80006e90#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13) = (0x80006e80#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, ?_,
    obs_btaken_other' hobs Register.x10 (by decide) ha0,
    obs_btaken_other' hobs Register.x11 (by decide) ha1,
    obs_btaken_other' hobs Register.x15 (by decide) ha5,
    obs_btaken_other' hobs Register.x1 (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, hstrb, by omega, by rw [hmem']; exact hcinv,
    fun R hR => (frame_btaken_cpy hobs R hR).trans (hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-! ## The "done" configuration at `0x80006e94` (ret entry)

`a0 = dst` (strcpy returns dst), `x1 = r`, and the full described memory update
`CpyInv … (len+1)` — the copied prefix `[dst, dst+len]` (chars + NUL). -/
structure StCpyDone (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006e94#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpyRegions dst src len
  cpyinv : CpyInv dst src len bs (len + 1) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-- `bnez a4` not-taken (`i = len`): `bs len = 0`, fall through to `ret`. -/
theorem tr_bnez_done (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (heq : i = len) :
    Triple (StCpy90 g i r dst src len m0 bs) (StCpyDone g r dst src len m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha4, ha5, hra, ⟨vmi, hmi⟩, htick,
    hreg, hstrb, hile, hcinv, hframe⟩ := hSt
  have hbz : bs i = 0 := by subst heq; exact hstrb.bs_nul
  have hv : ((zero_extend (m := 64) ((bs i) : BitVec (8*1))) != (0#64)) = false := by
    rw [zext_ne_zero_iff, hbz]; decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006e90_nottaken c.σ c.tick c.steps (0x80006e90#64) vmi
      (zero_extend (m := 64) ((bs i) : BitVec (8*1))) hgood hpc hmi ha4 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006e94#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006e90#64) 4 = (0x80006e94#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, hpc',
    obs_bnottaken_other' hobs Register.x10 (by decide) ha0,
    obs_bnottaken_other' hobs Register.x1 (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, ?_,
    fun R hR => (frame_bnottaken_cpy hobs R hR).trans (hframe R hR)⟩
  · rw [hmem']; rw [heq] at hcinv; exact hcinv

/-! ## Loop invariant, guard, measure

`LoopICpy = AtHeadCpy ∨ StCpyDone`: either at `0xe80` iteration `i ≤ len` (copied
prefix `[dst,dst+i)`), or done at `0xe94` (ret) with the full update.  `LoopBCpy`
= "at `0xe80` with `i < len`".  Measure `LoopMuCpy = 2^64 - a5.toNat`
(`a5 = dst+i`), strictly decreasing as `i` grows (`a5` increments by 1, no wrap). -/

def AtHeadCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  ∃ i, i ≤ len ∧ StCpy g (0x80006e80#64) i r dst src len m0 bs c

def LoopICpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadCpy g r dst src len m0 bs c ∨ StCpyDone g r dst src len m0 bs c

/-- Loop guard: at the head with `i < len` (more chars to copy — strict; the
exiting iteration `i = len` leaves via the `bnez` to `StCpyDone`). -/
def LoopBCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  ∃ i, i < len ∧ StCpy g (0x80006e80#64) i r dst src len m0 bs c

def LoopMuCpy (c : Config) : Nat :=
  2^64 - ((c.σ.regs.get? Register.x15).getD (0#64)).toNat

/-- At loop head iteration `i`, `a5 = dst+i`, so `LoopMuCpy = 2^64 - (dst.toNat+i)`. -/
theorem loopmu_head (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config)
    (hSt : StCpy g (0x80006e80#64) i r dst src len m0 bs c) (hi : i ≤ len) :
    LoopMuCpy c = 2^64 - (dst.toNat + i) := by
  simp only [LoopMuCpy, hSt.a5, Option.getD_some]
  rw [ptr_toNat dst i (by have := hSt.regions.dst_nowrap; omega)]

/-- **Loop body**: one iteration (`iterCpy` then `bnez`) re-establishes `LoopICpy`
strictly decreasing `LoopMuCpy`. -/
theorem loop_body_cpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (k : Nat) :
    Triple (fun c => LoopICpy g r dst src len m0 bs c ∧ LoopBCpy g r dst src len m0 bs c ∧ LoopMuCpy c = k)
           (fun c => LoopICpy g r dst src len m0 bs c ∧ LoopMuCpy c < k) := by
  intro c hc
  obtain ⟨_, ⟨i, hilt, hSt⟩, hmu⟩ := hc
  have hmu_eq : LoopMuCpy c = 2^64 - (dst.toNat + i) := loopmu_head g i r dst src len m0 bs c hSt (Nat.le_of_lt hilt)
  rw [hmu_eq] at hmu
  have hnw := hSt.regions.dst_nowrap
  -- one iteration to 0x90
  obtain ⟨c1, hs1, hSt90⟩ := iterCpy g i r dst src len m0 bs (Nat.le_of_lt hilt) c hSt
  by_cases hdone : i = len
  · exfalso; omega
  · -- loop back: bnez taken → AtHeadCpy (i+1)
    obtain ⟨c2, hs2, hSt2⟩ := tr_bnez_back g i r dst src len m0 bs hilt c1 hSt90
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨i + 1, hilt, hSt2⟩, ?_⟩
    have hmu2 : LoopMuCpy c2 = 2^64 - (dst.toNat + (i + 1)) :=
      loopmu_head g (i+1) r dst src len m0 bs c2 hSt2 hilt
    rw [hmu2, ← hmu]; omega

/-- The loop runs to `StCpyDone` (`0xe94`, full described update). -/
theorem loop_to_done_cpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (LoopICpy g r dst src len m0 bs) (StCpyDone g r dst src len m0 bs) := by
  have hloop := Triple.loop (I := LoopICpy g r dst src len m0 bs) (B := LoopBCpy g r dst src len m0 bs)
    LoopMuCpy (loop_body_cpy g r dst src len m0 bs)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · -- at head; ¬guard means ¬(∃ i<len). But AtHeadCpy gives i ≤ len. Show i = len then run last body.
    obtain ⟨i, hile, hSt⟩ := hHead
    by_cases hlt : i < len
    · exact absurd ⟨i, hlt, hSt⟩ hnB
    · -- i = len: run the final iteration to StCpyDone
      have heq : i = len := by omega
      obtain ⟨c1, hs1, hSt90⟩ := iterCpy g i r dst src len m0 bs hile c hSt
      obtain ⟨c2, hs2, hDone⟩ := tr_bnez_done g i r dst src len m0 bs heq c1 hSt90
      exact ⟨c2, hs1.trans hs2, hDone⟩
  · exact ⟨c, .refl c, hDone⟩

/-! ## `ret` (`0x80006e94 → r`) and the described-update postcondition -/

/-- The described-update postcondition: PC back at `r`, `x10 = dst` (strcpy returns
the destination), `GoodState`, `x1 = r`, and the observational described update —
the `len` chars plus the NUL are present at `[dst, dst+len]` and everything outside
is unchanged from `m0`. -/
def strcpy_bytehead_post (g : (R : Register) → Option (RegisterType R)) (r dst _src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∀ k, k ≤ len → c.σ.mem[(dst.toNat + k)]? = some (bs k)) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + len < a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R)

/-- `ret` transition (`0xe94 → r`): from `StCpyDone` to the postcondition.  Requires
`r` 4-aligned (so `ret`'s bit-0 clear is a no-op). -/
theorem tr_ret_cpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (StCpyDone g r dst src len m0 bs) (strcpy_bytehead_post g r dst src len m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hreg, hcinv, hframe⟩ := hSt
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006e94 c.σ c.tick c.steps (0x80006e94#64) vmi r hgood hpc hmi hra hloaded rfl htgt htick
  have hpc' : σ'.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs, ret_tgt r halign]
  have ha0' := obs_jr_other' hobs Register.x10 (by decide) ha0
  have hra' := obs_jr_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG', hpc', ha0', hra', ?_, ?_, hi',
    fun R hR => (frame_jr_cpy hobs R hR).trans (hframe R hR)⟩
  · intro k hk; rw [hmem']; exact hcinv.copied k (by omega)
  · intro a ha; rw [hmem']; exact hcinv.outside a ha

/-! ## Preamble `mv a5,a0` (`0x80006e7c → 0x80006e80`)

Sets `a5 := dst` (`a0`), establishing `StCpy` at iteration `0` (nothing copied yet,
`mem = m0` outside, source fully intact). -/

/-- Entry to the byte-head path at `0x80006e7c`: pointers in place, regions/strbytes
well-formed, `mem = m0` (fresh — nothing copied). -/
structure PreCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006e7c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpyRegions dst src len
  strbytes : StrBytes m0 src len bs
  memeq : c.σ.mem = m0
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-- Preamble: `mv a5,a0` (`0xe7c → 0xe80`) establishing `AtHeadCpy` at iteration 0. -/
theorem preamble_cpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreCpy g r dst src len m0 bs) (AtHeadCpy g r dst src len m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hstrb, hmemeq, hframe⟩ := hPre
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006e7c c.σ c.tick c.steps (0x80006e7c#64) vmi dst hgood hpc hmi ha0 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006e80#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006e7c#64) 4 = (0x80006e80#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some dst := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [add_sext0 dst] at this
  refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1, 0, Nat.zero_le len, ?_⟩
  refine ⟨hG1, by rw [hmem1]; exact hloaded, hpc1, ha0_1, ?_, ?_, hra_1,
    obs_alu_minstret hobs1, hi1, hreg, hstrb, Nat.zero_le len, ?_,
    fun R hR => (frame_alu_cpy hobs1 R hR.x15 hR).trans (hframe R hR)⟩
  · -- a1 = src = src + ofNat 0
    rwa [show src = src + BitVec.ofNat 64 0 from by
      rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]] at ha1_1
  · -- a5 = dst = dst + ofNat 0
    rwa [show dst = dst + BitVec.ofNat 64 0 from by
      rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]] at ha5_1
  · -- CpyInv at i = 0: nothing copied, mem = m0 outside/source
    rw [hmem1, hmemeq]
    refine ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun a _ => rfl, fun k _ _ => rfl⟩

/-! ## The byte-head-path total-correctness spec (from the byte-head entry `0xe7c`) -/

/-- **Byte-head path**, from the head `0x80006e7c` (`mv a5,a0`): the machine runs
to `r` with `x10 = dst`, `GoodState`, and the memory holding the described update —
the `len` chars + NUL copied into `[dst, dst+len]`, everything else untouched. -/
theorem strcpy_bytehead_from_head (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (PreCpy g r dst src len m0 bs) (strcpy_bytehead_post g r dst src len m0 bs) :=
  ((preamble_cpy g r dst src len m0 bs).seq
    ((fun c hc => loop_to_done_cpy g r dst src len m0 bs c (Or.inl hc)) :
      Triple (AtHeadCpy g r dst src len m0 bs) (StCpyDone g r dst src len m0 bs))).seq
    (tr_ret_cpy g r dst src len m0 bs halign)

/-! ## Entry dispatch (`0x80006dc4 → 0x80006e7c`, misaligned → byte head)

* `0xdc4`: `or a5,a0,a1`   — `a5 := dst ||| src`
* `0xdc8`: `andi a5,a5,7`  — `a5 := (dst ||| src) &&& 7`
* `0xdcc`: `bnez a5,0xe7c` — taken iff `(dst ||| src) &&& 7 ≠ 0` (misaligned)

The byte-head path is the misaligned case: `(dst.toNat ||| src.toNat) % 8 ≠ 0`. -/

/-- `((v10 ||| v11) &&& sext 7) ≠ 0` iff `(v10.toNat ||| v11.toNat) % 8 ≠ 0`. -/
theorem andi7_ne_zero_iff (w : BitVec 64) :
    ((w &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = decide (w.toNat % 8 ≠ 0) := by
  have hmask : (sign_extend (m := 64) (0x007#12) : BitVec 64) = 7#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hmask]
  rcases Decidable.em (w.toNat % 8 = 0) with h | h
  · rw [show decide (w.toNat % 8 ≠ 0) = false from by simp [h]]
    rw [bne_eq_false_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_and, show (7#64 : BitVec 64).toNat = 7 from by decide]
    rw [Nat.and_two_pow_sub_one_eq_mod w.toNat 3]
    simpa using h
  · rw [show decide (w.toNat % 8 ≠ 0) = true from by simp [h]]
    rw [bne_iff_ne, ne_eq]
    intro heq
    apply h
    have := congrArg BitVec.toNat heq
    rw [BitVec.toNat_and, show (7#64 : BitVec 64).toNat = 7 from by decide,
      Nat.and_two_pow_sub_one_eq_mod w.toNat 3] at this
    simpa using this

/-- Entry precondition at `0x80006dc4` (byte-head path): `CString`, misalignment
`(dst ||| src) % 8 ≠ 0`, regions/no-wrap, `mem = m0`. -/
structure PreCpyEntry (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006dc4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpyRegions dst src len
  strbytes : StrBytes m0 src len bs
  memeq : c.σ.mem = m0
  misaligned : (dst.toNat ||| src.toNat) % 8 ≠ 0
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-- Entry dispatch: `0xdc4 → 0xe7c`, establishing `PreCpy` at the byte-head. -/
theorem entry_dispatch_cpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreCpyEntry g r dst src len m0 bs) (PreCpy g r dst src len m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hstrb, hmemeq, hmisa, hframe⟩ := hPre
  -- 0xdc4: or a5,a0,a1
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006dc4 c.σ c.tick c.steps (0x80006dc4#64) vmi dst src hgood hpc hmi ha0 ha1 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006dc8#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006dc4#64) 4 = (0x80006dc8#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- 0xdc8: andi a5,a5,7
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006dc8 σ1 i1 (c.steps + 1) (0x80006dc8#64) vmi1 (dst ||| src)
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006dcc#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006dc8#64) 4 = (0x80006dcc#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- 0xdcc: bnez a5 taken (misaligned)
  have hv : (((dst ||| src) &&& sign_extend (m := 64) (0x007#12)) != (0#64)) = true := by
    rw [andi7_ne_zero_iff]
    rw [BitVec.toNat_or] at *
    simp only [decide_eq_true_eq]; exact hmisa
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006dcc_taken σ2 i2 (c.steps + 1 + 1) (0x80006dcc#64) vmi2
      ((dst ||| src) &&& sign_extend (m := 64) (0x007#12))
      hG2 hpc2 hmi2' ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hv hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006e7c#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs3]
    apply congrArg
    apply BitVec.eq_of_toNat_eq; decide
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3), ?_⟩
  refine ⟨hG3, by rw [hmem3eq]; exact hloaded, hpc3,
    obs_btaken_other' hobs3 Register.x10 (by decide) ha0_2,
    obs_btaken_other' hobs3 Register.x11 (by decide) ha1_2,
    obs_btaken_other' hobs3 Register.x1 (by decide) hra_2,
    obs_btaken_minstret hobs3, hi3, hreg, hstrb, by rw [hmem3eq]; exact hmemeq, ?_⟩
  -- frame: thread g through or (x15), andi (x15), bnez
  intro R hR
  have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_cpy hobs1 R hR.x15 hR
  have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_cpy hobs2 R hR.x15 hR
  have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_btaken_cpy hobs3 R hR
  rw [e3, e2, e1]; exact hframe R hR

/-! ## The byte-head-path total-correctness spec (from the strcpy entry `0xdc4`)

The complete misaligned-path spec: from the `strcpy` entry `0x80006dc4` with
`x10 = dst`, `x11 = src`, a `StrBytes` source-byte description, `(dst|src)%8 ≠ 0`,
`x1 = r` 4-aligned, and `mem = m0`, the machine runs to `r` with `x10 = dst`,
`GoodState`, and the `len` chars + NUL copied into `[dst, dst+len]`. -/
theorem strcpy_bytehead_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (PreCpyEntry g r dst src len m0 bs) (strcpy_bytehead_post g r dst src len m0 bs) :=
  (entry_dispatch_cpy g r dst src len m0 bs).seq
    (strcpy_bytehead_from_head g r dst src len m0 bs halign)

/-! ## `CString`-phrased corollary

Packaging the source-byte description as `CString m0 src s`: the copy realizes
`s.length + 1` byte writes into `[dst, dst + s.length]` (`s.length` chars + NUL). -/

/-- Entry precondition phrased with `CString m0 src s` (instead of the raw
`StrBytes`).  `misaligned`, regions, alignment, `mem = m0` as before. -/
structure StrcpyPre (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006dc4#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpyRegions dst src s.length
  cstring : CString m0 src.toNat s
  memeq : c.σ.mem = m0
  misaligned : (dst.toNat ||| src.toNat) % 8 ≠ 0
  hframe : ∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R

/-- `CString`-phrased postcondition: PC = r, x10 = dst, x1 = r, the copied region
`[dst, dst+s.length]` holds the source bytes (existential ghost `bs`), everything
outside is unchanged, GoodState, tick < 2, blanket frame. -/
def strcpy_post (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ bs : Nat → BitVec 8,
    (∀ k, k ≤ s.length → m0[(src.toNat + k)]? = some (bs k)) ∧
    (∀ k, k ≤ s.length → c.σ.mem[(dst.toNat + k)]? = some (bs k))) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + s.length < a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenCpy R → c.σ.regs.get? R = g R)

/-- **Top-level `strcpy` byte-head (misaligned) spec, `CString`-phrased.** -/
theorem strcpy_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (StrcpyPre g r dst src s m0) (strcpy_post g r dst src s m0) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hreg, hcstr, hmemeq, hmisa, hframe⟩ := hPre
  obtain ⟨len, bs, hlen, hstrb⟩ := cstring_bytes m0 src s hcstr
  subst hlen
  -- run the raw spec
  obtain ⟨c', hsteps, hpost⟩ :=
    strcpy_bytehead_spec g r dst src s.length m0 bs halign c
      ⟨hgood, hloaded, hpc, ha0, ha1, hra, hmi, htick, hreg, hstrb, hmemeq, hmisa, hframe⟩
  obtain ⟨hG', hpc', ha0', hra', hcopied, houtside, htick', hframe'⟩ := hpost
  refine ⟨c', hsteps, hG', hpc', ha0', hra', ⟨bs, ?_, hcopied⟩, houtside, htick', hframe'⟩
  intro k hk
  exact strbytes_byte m0 src s.length bs hstrb k hk

end Vsa.Sim
