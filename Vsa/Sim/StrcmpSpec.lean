import Vsa.Sim.StrcmpSites
import Vsa.Sim.ChainFrameOut
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivSpec
import Vsa.Sim.StrlenSpec
import Vsa.MemRepr
import Vsa.Triple

/-!
# Layer 3 — `strcmp` total-correctness spec (`strcmp_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/StrcmpSites.lean`) into a total-correctness triple for newlib `strcmp`
(`[0x80006ea0, 0x80006fcc)`).

## Control flow (from the disassembly / `StrcmpSites` header)

* entry / alignment test (`0xea0…eac`): `or a4,a0,a1`; `li t2,-1`;
  `andi a4,a4,7`; `bnez a4,0xf84` (misaligned ⇒ byte loop; aligned ⇒ word loop).
* byte loop (`0xf84…fa0`): `lbu a2,0(a0); lbu a3,0(a1)`; `addi a0,a0,1;
  addi a1,a1,1`; `bne a2,a3` (differ→exit); `bnez a2,0xf84` (loop); `sub a0,a2,a3; ret`.

This file proves the **byte-loop path** end-to-end (entry dispatch on the alignment
test → byte loop → `sub`/`ret`), plus the entry dispatch that routes to it. The
word-loop fast path is a separate, larger segment (see the closing note).

## The result `Q`: the SIGN class

The interpreter (`c/src/*.c`) consumes only the SIGN of `strcmp`: `env.c`/`value.c`
use `strcmp(...) == 0` (equality); `interp.c` uses `cmp < 0`, `<= 0`, `> 0`, `>= 0`
(string ordering). So `Q` characterizes `x10`'s sign as `strcmpSign x10 =
strcmpSpecSign sa sb`, where `strcmpSpecSign` compares the two strings' byte lists
(0 if equal; the sign of the first differing byte, terminator = 0).
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## The spec-level comparison (sign class)

`byteVal cs k` is the C byte at index `k` of the NUL-terminated string whose char
list is `cs`: the char's code (`< 128`) for `k < cs.length`, else `0` (the NUL
terminator). `strcmpSpecSign` is the sign of the difference of the first differing
bytes; `0` when the two strings are equal. -/

/-- The byte at index `k` of the C string `cs` (`0` past the terminator). -/
def byteVal (cs : List Char) (k : Nat) : Nat :=
  match cs[k]? with
  | some c => c.toNat
  | none => 0

/-- Least index at which two byte streams differ, or `n` if none in `[0, n)`. -/
def firstDiff (csa csb : List Char) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let k := firstDiff csa csb n
    if k < n then k
    else if byteVal csa n = byteVal csb n then n + 1 else n

/-- `Int` sign of `a - b` (`-1`, `0`, `+1`). -/
def isign (a b : Nat) : Int := if a < b then -1 else if a = b then 0 else 1

/-- The spec sign of `strcmp csa csb`: compares byte streams up to and including the
terminator. `bound` must be `≥ max length + 1` so the terminator difference is seen. -/
def strcmpSpecSign (csa csb : List Char) : Int :=
  let n := max csa.length csb.length + 1
  let k := firstDiff csa csb n
  isign (byteVal csa k) (byteVal csb k)

/-- The machine sign of the returned `x10` = `sub a2,a3` of two zero-extended bytes:
the two bytes are `< 128`, so `x10.toInt` is exactly their (signed-small) difference.
We read the sign off `x10.toInt`. -/
def strcmpSign (x : BitVec 64) : Int := if x = 0 then 0 else if x.toInt < 0 then -1 else 1

/-! ## Ghost-frame predicate (`NotWrittenStrcmp`) for strcmp's write-set

Strcmp writes `x5, x6, x7, x10, x11, x12, x13, x14, x15` (t0, t1, t2, a0–a5); the
blanket ghost-frame conjunct pins every register outside the union of that GPR set
and the per-step / tick write-set. The generic per-class frame helpers (mirroring
`DivSpec.frame_*`) consume exactly the pc/tick disequalities they need. -/

/-- `R` outside strcmp's written GPRs ∪ per-step write-set ∪ tick-set. -/
abbrev NotWrittenStrcmp (R : Register) : Prop :=
  (Register.x5 == R) = false ∧ (Register.x6 == R) = false ∧
  (Register.x7 == R) = false ∧ (Register.x10 == R) = false ∧
  (Register.x11 == R) = false ∧ (Register.x12 == R) = false ∧
  (Register.x13 == R) = false ∧ (Register.x14 == R) = false ∧
  (Register.x15 == R) = false ∧ (Register.PC == R) = false ∧
  (Register.nextPC == R) = false ∧ (Register.minstret == R) = false ∧
  (Register.minstret_increment == R) = false ∧ (Register.mcycle == R) = false ∧
  (Register.mtime == R) = false ∧ (Register.mip == R) = false

/-- Generic ALU frame step for strcmp: variable-`R` read-back through an ALU
observation. `rd` is one of strcmp's written GPRs; the caller supplies the matching
`(rd == R) = false` from `NotWrittenStrcmp R`. -/
theorem sframe_alu {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenStrcmp R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- Generic taken-branch frame step. -/
theorem sframe_btaken {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenStrcmp R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

/-- Generic not-taken-branch frame step. -/
theorem sframe_bnottaken {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenStrcmp R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-- Generic `jr`/`ret` frame step (`jump_x0`). -/
theorem sframe_jr {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenStrcmp R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## Region / string side conditions (byte path)

`StrcmpRegion p len` bundles the disjointness / no-wrap side facts for a single
NUL-terminated string `[p, p+len]` (`len+1` bytes, the `len` chars plus the NUL) as
scanned by the byte loop: the region lives in RAM, disjoint from the `strcmp` code
`[0x80006ea0, 0x80006fcc)` and the HTIF `tohost` window, and does not wrap. The byte
loop reads one byte at a time up to `p+len` (the NUL), so no trailing over-read. -/
structure StrcmpRegion (p : BitVec 64) (len : Nat) : Prop where
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 1 ≤ 0x100000000
  nowrap : p.toNat + len + 1 < 2^64
  /-- disjoint from the strcmp code region `[0x80006ea0, 0x80006fcc)` -/
  code : p.toNat + len + 1 ≤ 0x80006ea0 ∨ 0x80006fcc ≤ p.toNat
  /-- disjoint from the HTIF `tohost` window (`tohostAddr = 0x8001ad00`, ± 8) -/
  htif : p.toNat + len + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat

/-- The byte `lbu` at address `p + k` (`k ≤ len`) is in RAM, above the HTIF window;
the concrete side facts the width-1 total `lbu` site needs. -/
theorem byte_lbu_bounds (p : BitVec 64) (len k : Nat) (hreg : StrcmpRegion p len)
    (hk : k ≤ len) :
    (p + BitVec.ofNat 64 k).toNat = p.toNat + k ∧
    0x80000000 ≤ ((p + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((p + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000 ∧
    (((p + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((p + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x000#12)).toNat) := by
  have htn : (p + BitVec.ofNat 64 k).toNat = p.toNat + k :=
    ptrN p k (by have := hreg.nowrap; omega)
  have hlo := hreg.lo
  have hhi := hreg.hi
  have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_⟩
  all_goals rw [sext0_add, htn]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega

/-- Char code round-trips: for `b : BitVec 8` with `b.toNat < 128`,
`(Char.ofNat b.toNat).toNat = b.toNat`. -/
theorem char_ofNat_toNat (b : BitVec 8) (hb : b.toNat < 128) :
    (Char.ofNat b.toNat).toNat = b.toNat := by
  rw [Char.toNat, Char.ofNat, dif_pos (by left; show b.toNat < 55296; omega)]
  simp only [Char.ofNatAux, UInt32.toNat]
  rfl

/-- The byte at offset `k < cs.length` in `CStr m p cs` is `< 128` (an ASCII char). -/
theorem cstr_byte_lt128 (m : Mem) (p : Nat) (cs : List Char) (hcstr : CStr m p cs) :
    ∀ (k : Nat), k < cs.length → ∀ (b : BitVec 8), m[p + k]? = some b → b.toNat < 128 := by
  induction hcstr with
  | @nil a hnil => intro k hk; simp at hk
  | @cons a b0 cs hb0 hb0ne hb0lt hrest ih =>
    intro k hk bb hbb
    match k with
    | 0 =>
      simp only [Nat.add_zero] at hbb
      rw [hb0] at hbb; injection hbb with hbb; subst hbb; exact hb0lt
    | k + 1 =>
      have hk' : k < cs.length := by simpa using hk
      have hbb' : m[(a + 1) + k]? = some bb := by
        rw [show (a + 1) + k = a + (k + 1) from by omega]; exact hbb
      exact ih k hk' bb hbb'

/-- The byte value at index `k < cs.length` of `CStr m p cs` matches `byteVal cs k`.
The stored char is `Char.ofNat b.toNat` with `b.toNat < 128`, so its code is `b.toNat`. -/
theorem cstr_byteVal (m : Mem) (p : Nat) (cs : List Char) (hcstr : CStr m p cs) :
    ∀ (k : Nat), k < cs.length → ∀ (b : BitVec 8), m[p + k]? = some b → b ≠ 0 →
      b.toNat = byteVal cs k := by
  induction hcstr with
  | @nil a hnil => intro k hk; simp at hk
  | @cons a b0 cs hb0 hb0ne hb0lt hrest ih =>
    intro k hk bb hbb hbbne
    match k with
    | 0 =>
      -- byteVal (Char.ofNat b0.toNat :: cs) 0 = (Char.ofNat b0.toNat).toNat = b0.toNat
      simp only [Nat.add_zero] at hbb
      rw [hb0] at hbb; injection hbb with hbb; subst hbb
      simp only [byteVal, List.getElem?_cons_zero]
      exact (char_ofNat_toNat b0 hb0lt).symm
    | k + 1 =>
      have hk' : k < cs.length := by simpa using hk
      have hbb' : m[(a + 1) + k]? = some bb := by
        rw [show (a + 1) + k = a + (k + 1) from by omega]; exact hbb
      have := ih k hk' bb hbb' hbbne
      simpa [byteVal, List.getElem?_cons_succ] using this

/-- The byte at index `k ≤ len` in `CStr m p cs` (`len = cs.length`) is mapped, with
value `some (byte)`; it is `0` iff `k = len` (the NUL) and its `toNat` is `byteVal cs k`. -/
theorem cstr_byte_val (m : Mem) (p : Nat) (cs : List Char) (hcstr : CStr m p cs)
    (k : Nat) (hk : k ≤ cs.length) :
    ∃ b : BitVec 8, m[p + k]? = some b ∧ (b = 0 ↔ k = cs.length) ∧
      b.toNat = byteVal cs k := by
  by_cases heq : k = cs.length
  · subst heq
    refine ⟨0, cstr_byte_nul m hcstr, by simp, ?_⟩
    simp [byteVal]
  · have hlt : k < cs.length := by omega
    obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m hcstr k hlt
    refine ⟨b, hb, ⟨fun h => absurd h hbne, fun h => absurd h (by omega)⟩, ?_⟩
    -- b.toNat = byteVal cs k: the char at k is Char.ofNat b.toNat with b.toNat < 128
    exact cstr_byteVal m p cs hcstr k hlt b hb hbne

/-- Under `CStr m p cs`, `byteVal cs k = 0` forces `k = cs.length` (interior chars
are nonzero, so the only zero byte is the terminator past the end). -/
theorem cstr_byteVal_zero (m : Mem) (p : Nat) (cs : List Char) (hcstr : CStr m p cs)
    (k : Nat) (hk : k ≤ cs.length) (hz : byteVal cs k = 0) : k = cs.length := by
  rcases Nat.lt_or_ge k cs.length with hlt | hge
  · exfalso
    obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m hcstr k hlt
    have hval := cstr_byteVal m p cs hcstr k hlt b hb hbne
    -- b ≠ 0 ⇒ b.toNat ≠ 0 ⇒ byteVal cs k ≠ 0
    have : b.toNat ≠ 0 := fun h => hbne (by apply BitVec.eq_of_toNat_eq; rw [h]; rfl)
    rw [hval] at this; exact this hz
  · omega

/-- `byteVal cs k < 128` for all `k` (chars are `< 128`; terminator is `0`). -/
theorem byteVal_lt (m : Mem) (p : Nat) (cs : List Char) (hcstr : CStr m p cs) :
    ∀ k, byteVal cs k < 128 := by
  intro k
  by_cases hk : k < cs.length
  · obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m hcstr k hk
    rw [← cstr_byteVal m p cs hcstr k hk b hb hbne]
    -- b.toNat < 128 comes from CStr's stored bound; re-derive via the cons chain
    exact cstr_byte_lt128 m p cs hcstr k hk b hb
  · have : cs[k]? = none := by simp; omega
    simp [byteVal, this]

/-! ## The byte-compare loop (`0xf84 … 0xfa0`)

Ghosts: `pa`/`pb` (the byte pointers), `csa`/`csb` (the char lists, `= CStr`),
`la = csa.length`, `lb = csb.length`, `r`/`m0`. The loop at head `0xf84` in
iteration `k` has compared bytes `[0,k)` (all equal and nonzero — else it would have
branched out). It loads `a2 = byte@(pa+k)`, `a3 = byte@(pb+k)`, advances both
pointers, and branches: `bne a2,a3` (differ → `sub`/`ret`); `bnez a2` (nonzero →
loop; zero → both are the NUL, `sub = 0`, `ret`). -/

/-- Bytes `[0,k)` of `csa`/`csb` agree and are nonzero: the loop-carried invariant. -/
def BytePrefix (csa csb : List Char) (k : Nat) : Prop :=
  ∀ i, i < k → byteVal csa i = byteVal csb i ∧ byteVal csa i ≠ 0

/-- Loop-head observation at `0xf84`, byte iteration `k`. -/
structure BSt (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (k : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006f84#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 k)
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 k)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpRegion pa csa.length
  regb : StrcmpRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  prefixEq : BytePrefix csa csb k
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Final `strcmp` observation (byte path): returned to `r`, `x10`'s sign is the
spec sign. Carries the blanket ghost-frame over `NotWrittenStrcmp` so callers recover
`sp` and every callee-saved register across the call (the ghost-frame rule). -/
structure BDone (g : (R : Register) → Option (RegisterType R))
    (r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  pc : c.σ.regs.get? Register.PC = some r
  ra : c.σ.regs.get? Register.x1 = some r
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  tick : c.tick < 2
  result : ∃ x, c.σ.regs.get? Register.x10 = some x ∧ strcmpSign x = strcmpSpecSign csa csb
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-! ### Spec-sign bridges

`firstDiff` under the loop invariant: if `csa`/`csb` agree on `[0,k)` and differ at
`k`, then `firstDiff csa csb n = k` for every `n > k`. Hence `strcmpSpecSign` is the
sign of the byte difference at the first differing index `k`. -/

/-- `byteVal cs i ≠ 0` forces `i < cs.length` (the terminator/past-end byte is `0`). -/
theorem byteVal_ne_zero_lt {cs : List Char} {i : Nat} (h : byteVal cs i ≠ 0) :
    i < cs.length := by
  rcases Nat.lt_or_ge i cs.length with hlt | hge
  · exact hlt
  · have : cs[i]? = none := by simp; omega
    simp [byteVal, this] at h

/-- If the streams *agree* on `[0,k)` and `n ≤ k`, then `firstDiff csa csb n = n`
(no difference seen yet within the bound). -/
theorem firstDiff_agree_eq (csa csb : List Char) (k : Nat)
    (h : ∀ i, i < k → byteVal csa i = byteVal csb i) :
    ∀ n, n ≤ k → firstDiff csa csb n = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih =>
    intro hn
    have hnk : n ≤ k := by omega
    have hrec := ih hnk
    have hnltk : n < k := by omega
    have heq := h n hnltk
    simp only [firstDiff, hrec]
    rw [if_neg (Nat.lt_irrefl n), if_pos heq]

/-- If the streams agree on `[0,k)` (`BytePrefix`) and `n ≤ k`, then
`firstDiff csa csb n = n`. -/
theorem firstDiff_prefix_eq (csa csb : List Char) (k : Nat) (h : BytePrefix csa csb k) :
    ∀ n, n ≤ k → firstDiff csa csb n = n :=
  firstDiff_agree_eq csa csb k (fun i hi => (h i hi).1)

/-- If `csa`/`csb` agree on `[0,k)` and differ at `k`, then `firstDiff csa csb n = k`
for all `n ≥ k+1`. -/
theorem firstDiff_at (csa csb : List Char) (k : Nat) (hpre : BytePrefix csa csb k)
    (hne : byteVal csa k ≠ byteVal csb k) :
    ∀ n, k + 1 ≤ n → firstDiff csa csb n = k := by
  intro n
  induction n with
  | zero => intro h; omega
  | succ n ih =>
    intro hn
    rcases Nat.lt_or_ge k (n+1) with hlt | hge
    · -- n ≥ k
      have hnk : k ≤ n := by omega
      rcases Nat.lt_or_ge k n with hkn | hkn
      · -- n > k: recurse
        have hrec := ih (by omega)
        simp only [firstDiff, hrec]
        rw [if_pos hkn]
      · -- n = k: base
        have hnk' : n = k := by omega
        have hpre_n : firstDiff csa csb n = n :=
          firstDiff_prefix_eq csa csb k hpre n hkn
        simp only [firstDiff, hpre_n]
        rw [if_neg (Nat.lt_irrefl n), if_neg (hnk' ▸ hne)]
        exact hnk'
    · omega

/-- Under the loop invariant, the spec sign is the byte-difference sign at the first
differing index `k`. -/
theorem strcmpSpecSign_at (csa csb : List Char) (k : Nat) (hpre : BytePrefix csa csb k)
    (hne : byteVal csa k ≠ byteVal csb k) :
    strcmpSpecSign csa csb = isign (byteVal csa k) (byteVal csb k) := by
  -- one side's byte at k is nonzero (they differ), so k < that length ⇒ k ≤ max la lb
  have hkmax : k ≤ max csa.length csb.length := by
    by_cases ha : byteVal csa k = 0
    · have hb : byteVal csb k ≠ 0 := fun h => hne (by rw [ha, h])
      have := byteVal_ne_zero_lt hb
      omega
    · have := byteVal_ne_zero_lt ha
      omega
  have hbound : k + 1 ≤ max csa.length csb.length + 1 := by omega
  show isign (byteVal csa (firstDiff csa csb (max csa.length csb.length + 1)))
    (byteVal csb (firstDiff csa csb (max csa.length csb.length + 1)))
    = isign (byteVal csa k) (byteVal csb k)
  rw [firstDiff_at csa csb k hpre hne _ hbound]

/-- Under the loop invariant, if both strings terminate at `k` (`length = k`), they
are equal and the spec sign is `0`. `k = length` is supplied from the machine (the
loaded byte at `k` is the NUL, via `cstr_byte_val`'s iff). -/
theorem strcmpSpecSign_eq (csa csb : List Char) (k : Nat) (hpre : BytePrefix csa csb k)
    (hka : csa.length = k) (hkb : csb.length = k) :
    strcmpSpecSign csa csb = 0 := by
  -- bound = k + 1; the two streams agree on [0,k+1) (byte k is 0 both sides), so firstDiff = k+1
  have hmax : max csa.length csb.length + 1 = k + 1 := by rw [hka, hkb]; simp
  -- extend BytePrefix to k+1: at index k both bytes are the NUL (byteVal = 0), equal
  have hbyteEqk : byteVal csa k = byteVal csb k := by
    have ha : byteVal csa k = 0 := by
      unfold byteVal
      have : csa[k]? = none := by simp; omega
      rw [this]
    have hb : byteVal csb k = 0 := by
      unfold byteVal
      have : csb[k]? = none := by simp; omega
      rw [this]
    rw [ha, hb]
  have hagree1 : ∀ i, i < k + 1 → byteVal csa i = byteVal csb i := by
    intro i hi
    rcases Nat.lt_or_ge i k with hik | hik
    · exact (hpre i hik).1
    · have hik' : i = k := by omega
      subst hik'; exact hbyteEqk
  show isign (byteVal csa (firstDiff csa csb (max csa.length csb.length + 1)))
    (byteVal csb (firstDiff csa csb (max csa.length csb.length + 1))) = 0
  rw [hmax, firstDiff_agree_eq csa csb (k+1) hagree1 (k+1) (Nat.le_refl _)]
  -- byteVal at k+1 (past both ends) = 0
  have hna : byteVal csa (k+1) = 0 := by
    unfold byteVal
    have : csa[k+1]? = none := by simp; omega
    rw [this]
  have hnb : byteVal csb (k+1) = 0 := by
    unfold byteVal
    have : csb[k+1]? = none := by simp; omega
    rw [this]
  rw [hna, hnb]; simp [isign]

/-- `(p + ofNat k) + sext 1 = p + ofNat (k+1)` (the `addi …,1` increment), via BitVec
group algebra (avoids `2^64` omega blowup). -/
theorem ptr_incr1 (p : BitVec 64) (k : Nat) :
    (p + BitVec.ofNat 64 k) + sign_extend (m := 64) (0x001#12) = p + BitVec.ofNat 64 (k+1) := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- `zext b` has `toNat = b.toNat` (the byte value, unchanged by widening). -/
theorem zext_toNat (b : BitVec 8) : (zero_extend (m := 64) b).toNat = b.toNat := by
  simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)]

/-- The machine result `sub a2,a3 = zext ba - zext bb` has sign `isign ba bb`, given
both bytes `< 128`. Computed via the wrapped `toNat` of the subtraction. -/
theorem strcmpSign_sub (ba bb : BitVec 8) (hba : ba.toNat < 128) (hbb : bb.toNat < 128) :
    strcmpSign (zero_extend (m := 64) ba - zero_extend (m := 64) bb)
      = isign ba.toNat bb.toNat := by
  have hza := zext_toNat ba
  have hzb := zext_toNat bb
  have hb : ba.toNat < 2^64 := by have := ba.isLt; omega
  have hb2 : bb.toNat < 2^64 := by have := bb.isLt; omega
  have hxnat : (zero_extend (m := 64) ba - zero_extend (m := 64) bb).toNat
      = (2^64 - bb.toNat + ba.toNat) % 2^64 := by
    rw [BitVec.toNat_sub, hza, hzb]
  -- abstract the difference as `x` with its `toNat`
  generalize hxdef : (zero_extend (m := 64) ba - zero_extend (m := 64) bb) = x at hxnat ⊢
  unfold strcmpSign isign
  by_cases heq : ba.toNat = bb.toNat
  · have hx0 : x = 0 := by
      apply BitVec.eq_of_toNat_eq
      rw [hxnat, heq]; simp; rw [Nat.sub_add_cancel (by omega), Nat.mod_self]
    rw [if_pos hx0, if_neg (by omega : ¬ ba.toNat < bb.toNat), if_pos heq]
  · rcases Nat.lt_or_ge ba.toNat bb.toNat with hlt | hge
    · -- x.toNat = 2^64 - (bb - ba) ∈ [2^63, 2^64): negative, nonzero
      have hmod : x.toNat = 2^64 - (bb.toNat - ba.toNat) := by
        rw [hxnat, Nat.mod_eq_of_lt (by omega)]; omega
      have hxne : x ≠ 0 := by intro hx; rw [hx] at hmod; simp at hmod; omega
      have hneg : x.toInt < 0 := by
        rw [BitVec.toInt_eq_msb_cond]
        have hmsb : x.msb = true := by rw [BitVec.msb_eq_decide]; simp; rw [hmod]; omega
        rw [if_pos hmsb, hmod]; omega
      rw [if_neg hxne, if_pos hneg, if_pos hlt]
    · -- ba > bb (heq excludes equal): x.toNat = ba - bb small, positive
      have hgt : bb.toNat < ba.toNat := by omega
      have hmod : x.toNat = ba.toNat - bb.toNat := by
        rw [hxnat, show 2^64 - bb.toNat + ba.toNat = 2^64 + (ba.toNat - bb.toNat) from by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
      have hxne : x ≠ 0 := by intro hx; rw [hx] at hmod; simp at hmod; omega
      have hpos : ¬ x.toInt < 0 := by
        rw [BitVec.toInt_eq_toNat_of_lt (by rw [hmod]; omega), hmod]; omega
      rw [if_neg hxne, if_neg hpos, if_neg (by omega : ¬ ba.toNat < bb.toNat), if_neg heq]

/-- `(zext ba != zext bb) = (ba != bb)` for `BitVec 8` bytes (the `bne a2,a3` guard). -/
theorem zext_bne (ba bb : BitVec 8) :
    ((zero_extend (m := 64) ba) != (zero_extend (m := 64) bb)) = (ba != bb) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne]
  constructor
  · intro h hc; exact h (by rw [hc])
  · intro h hc; apply h
    have : (zero_extend (m := 64) ba).toNat = (zero_extend (m := 64) bb).toNat := by rw [hc]
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show ba.toNat < 2^64 from by have := ba.isLt; omega),
      Nat.mod_eq_of_lt (show bb.toNat < 2^64 from by have := bb.isLt; omega)] at this
    exact BitVec.eq_of_toNat_eq this

/-- Intermediate observation at `0xf94` (the `bne a2,a3`): loaded `a2 = zext byte@(pa+k)`,
`a3 = zext byte@(pb+k)`, pointers advanced to `pa+(k+1)`, `pb+(k+1)`. -/
structure B94 (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (ba bb : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (k : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006f94#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (k+1))
  a1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (k+1))
  a2 : c.σ.regs.get? Register.x12 = some (zero_extend (m := 64) ba)
  a3 : c.σ.regs.get? Register.x13 = some (zero_extend (m := 64) bb)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpRegion pa csa.length
  regb : StrcmpRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  prefixEq : BytePrefix csa csb k
  hba : ba.toNat = byteVal csa k
  hbb : bb.toNat = byteVal csb k
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- `BytePrefix csa csb k` ⇒ `k ≤ csa.length` (bytes `[0,k)` are nonzero string chars). -/
theorem prefix_le_lena {csa csb : List Char} {k : Nat} (h : BytePrefix csa csb k) :
    k ≤ csa.length := by
  rcases Nat.lt_or_ge csa.length k with hk1 | hk1
  · obtain ⟨_, hne⟩ := h csa.length hk1
    exact absurd (byteVal_ne_zero_lt hne) (Nat.lt_irrefl _)
  · exact hk1

/-- `BytePrefix csa csb k` ⇒ `k ≤ csb.length`. -/
theorem prefix_le_lenb {csa csb : List Char} {k : Nat} (h : BytePrefix csa csb k) :
    k ≤ csb.length := by
  rcases Nat.lt_or_ge csb.length k with hk1 | hk1
  · obtain ⟨heq, hne⟩ := h csb.length hk1
    rw [heq] at hne
    exact absurd (byteVal_ne_zero_lt hne) (Nat.lt_irrefl _)
  · exact hk1

/-- Observation at `0xf9c` (`sub a0,a2,a3`): `a2 = zext ba`, `a3 = zext bb`, `x1 = r`,
and the sign target `isign ba bb = strcmpSpecSign csa csb` is already discharged. -/
structure BF9c (g : (R : Register) → Option (RegisterType R))
    (r : BitVec 64) (csa csb : List Char) (ba bb : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006f9c#64 : BitVec 64)
  a2 : c.σ.regs.get? Register.x12 = some (zero_extend (m := 64) ba)
  a3 : c.σ.regs.get? Register.x13 = some (zero_extend (m := 64) bb)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  hba : ba.toNat < 128
  hbb : bb.toNat < 128
  hsign : isign ba.toNat bb.toNat = strcmpSpecSign csa csb
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- Branch dispatch `0xf94 … 0xf9c` from `B94 k`: `bne a2,a3` and `bnez a2` route to
either the loop head `BSt (k+1)` (bytes equal and nonzero) or `BF9c` (bytes differ,
or both NUL). The `BF9c` sign target is discharged via `strcmpSpecSign_at`/`_eq`. -/
theorem byte_dispatch (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (ba bb : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (k : Nat) :
    Triple (B94 g pa pb r csa csb ba bb m0 o k)
      (fun c => BSt g pa pb r csa csb m0 o (k+1) c
        ∨ (∃ ba' bb', BF9c g r csa csb ba' bb' m0 o c)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, ha2, ha3, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hpre, hba, hbb, hframe⟩ := hSt
  have hba128 : ba.toNat < 128 := by rw [hba]; exact byteVal_lt m0 pa.toNat csa hcstra k
  have hbb128 : bb.toNat < 128 := by rw [hbb]; exact byteVal_lt m0 pb.toNat csb hcstrb k
  by_cases hdiff : ba = bb
  · -- bytes equal: bne not taken → f98
    subst hdiff
    have hguard94 : ((zero_extend (m := 64) ba) != (zero_extend (m := 64) ba)) = false := by
      rw [zext_bne]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006f94_nottaken c.σ c.tick c.steps (0x80006f94#64) vmi
        (zero_extend (m := 64) ba) (zero_extend (m := 64) ba)
        hgood hpc hmi ha2 ha3 hloaded rfl hguard94 htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006f98#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006f94#64) 4 = (0x80006f98#64 : BitVec 64) from by decide] at this
    have ha0_1 := obs_bnottaken_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
    have ha1_1 := obs_bnottaken_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
    have ha2_1 := obs_bnottaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2
    have ha3_1 := obs_bnottaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
    have hra_1 := obs_bnottaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    by_cases hz : ba = 0
    · -- bnez a2 not taken (a2 = 0) → f9c (NUL exit). Both strings terminate at k.
      subst hz
      have hguard98 : ((zero_extend (m := 64) (0#8)) != (0#64)) = false := by decide
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006f98_nottaken σ1 i1 (c.steps + 1) (0x80006f98#64) vmi1
          (zero_extend (m := 64) (0#8))
          hG1 hpc1 hmi1' ha2_1 (by rw [hmem1]; exact hloaded) rfl hguard98 hi1
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006f9c#64 : BitVec 64) := by
        have := obs_bnottaken_pc hobs2; rwa [show BitVec.addInt (0x80006f98#64) 4 = (0x80006f9c#64 : BitVec 64) from by decide] at this
      have ha2_2 := obs_bnottaken_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
      have ha3_2 := obs_bnottaken_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
      have hra_2 := obs_bnottaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_bnottaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_bnottaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hout2 : σ2.sailOutput = o :=
        (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
      -- both bytes NUL ⇒ k = length for both
      have hka : csa.length = k := (cstr_byteVal_zero m0 pa.toNat csa hcstra k
        (prefix_le_lena hpre) (by rw [← hba]; rfl)).symm
      have hkb : csb.length = k := (cstr_byteVal_zero m0 pb.toNat csb hcstrb k
        (prefix_le_lenb hpre) (by rw [← hbb]; rfl)).symm
      have hsign : isign (0#8).toNat (0#8).toNat = strcmpSpecSign csa csb := by
        rw [strcmpSpecSign_eq csa csb k hpre hka hkb]; simp [isign]
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inr ?_⟩
      exact ⟨0#8, 0#8, hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem,
        hout2,
        hpc2, ha2_2, ha3_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, (by decide), (by decide), hsign, hframe_2⟩
    · -- bnez a2 taken (a2 ≠ 0) → f84 (loop back), BSt (k+1)
      have hguard98 : ((zero_extend (m := 64) ba) != (0#64)) = true := by
        rw [bne_iff_ne]; intro hc
        apply hz
        have : (zero_extend (m := 64) ba).toNat = 0 := by rw [hc]; rfl
        rw [zext_toNat] at this
        apply BitVec.eq_of_toNat_eq; rw [this]; rfl
      obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
        site_80006f98_taken σ1 i1 (c.steps + 1) (0x80006f98#64) vmi1
          (zero_extend (m := 64) ba)
          hG1 hpc1 hmi1' ha2_1 (by rw [hmem1]; exact hloaded) rfl hguard98 hi1
      have hpceq : (0x80006f98#64 : BitVec 64) + sign_extend (m := 64) (0x1fec#13) = (0x80006f84#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      have hpc2 : σ2.regs.get? Register.PC = some (0x80006f84#64 : BitVec 64) := by
        rw [obs_btaken_pc hobs2, hpceq]
      have ha0_2 := obs_btaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
      have ha1_2 := obs_btaken_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
      have hra_2 := obs_btaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
      have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
        fun R hR => (sframe_btaken hobs2 R hR).trans (hframe_1 R hR)
      obtain ⟨vmi2, hmi2'⟩ := obs_btaken_minstret hobs2
      have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
      have hout2 : σ2.sailOutput = o :=
        (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
      -- extend BytePrefix to k+1: bytes agree (equal) and nonzero (ba ≠ 0)
      have hbaz : byteVal csa k ≠ 0 := by
        rw [← hba]; intro h
        apply hz; apply BitVec.eq_of_toNat_eq; rw [h]; rfl
      have hpre1 : BytePrefix csa csb (k+1) := by
        intro i hi
        rcases Nat.lt_or_ge i k with hik | hik
        · exact hpre i hik
        · have : i = k := by omega
          subst this
          exact ⟨by rw [← hba, ← hbb], hbaz⟩
      refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), Or.inl ?_⟩
      exact ⟨hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem,
        hout2, hpc2,
        ha0_2, ha1_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hrega, hregb, hcstra, hcstrb, hpre1, hframe_2⟩
  · -- bytes differ: bne taken → f9c
    have hguard94 : ((zero_extend (m := 64) ba) != (zero_extend (m := 64) bb)) = true := by
      rw [zext_bne, bne_iff_ne]; exact hdiff
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006f94_taken c.σ c.tick c.steps (0x80006f94#64) vmi
        (zero_extend (m := 64) ba) (zero_extend (m := 64) bb)
        hgood hpc hmi ha2 ha3 hloaded rfl hguard94 htick
    have hpceq : (0x80006f94#64 : BitVec 64) + sign_extend (m := 64) (0x0008#13) = (0x80006f9c#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006f9c#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs1, hpceq]
    have ha2_1 := obs_btaken_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2
    have ha3_1 := obs_btaken_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
    have hra_1 := obs_btaken_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
    -- byteVal differ at k ⇒ sign via strcmpSpecSign_at
    have hbytene : byteVal csa k ≠ byteVal csb k := by
      rw [← hba, ← hbb]; intro h
      apply hdiff; apply BitVec.eq_of_toNat_eq; exact h
    have hsign : isign ba.toNat bb.toNat = strcmpSpecSign csa csb := by
      rw [hba, hbb, ← strcmpSpecSign_at csa csb k hpre hbytene]
    have hout1 : σ1.sailOutput = o :=
      (by chain_out [hobs1] : σ1.sailOutput = c.σ.sailOutput).trans hout
    refine ⟨⟨σ1, i1, c.steps + 1⟩, Steps.single hs1, Or.inr ?_⟩
    exact ⟨ba, bb, hG1, by rw [hmem1]; exact hloaded, by rw [hmem1]; exact hmem,
      hout1,
      hpc1, ha2_1, ha3_1, hra_1, ⟨vmi1, hmi1'⟩, hi1, hba128, hbb128, hsign, hframe_1⟩

/-- `0xf9c → ret → BDone`: `sub a0,a2,a3` writes the byte difference; `ret` returns to
`r` with `x10`'s sign the spec sign. Needs `r` 4-aligned (bit-0 clear a no-op). -/
theorem byte_f9c_ret (g : (R : Register) → Option (RegisterType R))
    (r : BitVec 64) (csa csb : List Char) (ba bb : BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (halignr : r.toNat % 4 = 0) :
    Triple (BF9c g r csa csb ba bb m0 o) (BDone g r csa csb m0 o) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha2, ha3, hra, ⟨vmi, hmi⟩, htick, hba, hbb, hsign, hframe⟩ := hSt
  -- === f9c: sub a0,a2,a3 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006f9c c.σ c.tick c.steps (0x80006f9c#64) vmi
      (zero_extend (m := 64) ba) (zero_extend (m := 64) bb)
      hgood hpc hmi ha2 ha3 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006fa0#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006f9c#64) 4 = (0x80006fa0#64 : BitVec 64) from by decide] at this
  have ha0_1 : σ1.regs.get? Register.x10 = some (zero_extend (m := 64) ba - zero_extend (m := 64) bb) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === fa0: ret ===
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halignr]; exact halignr
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006fa0 σ1 i1 (c.steps + 1) (0x80006fa0#64) vmi1 r
      hG1 hpc1 hmi1' hra_1 (by rw [hmem1]; exact hloaded) rfl htgt hi1
  have hpc2 : σ2.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs2, ret_tgt r halignr]
  have ha0_2 := obs_jr_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have hra_2 := obs_jr_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_jr hobs2 R hR).trans (hframe_1 R hR)
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  have hout2 : σ2.sailOutput = o :=
    (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, hpc2, hra_2, by rw [hmem2eq]; exact hmem, hout2,
    hi2, ?_, hframe_2⟩
  refine ⟨zero_extend (m := 64) ba - zero_extend (m := 64) bb, ha0_2, ?_⟩
  rw [strcmpSign_sub ba bb hba hbb]; exact hsign

/-- Straight-line body `0xf84 → 0xf94`: `lbu a2; lbu a3; addi a0,1; addi a1,1`. -/
theorem byte_straight (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (k : Nat) :
    Triple (BSt g pa pb r csa csb m0 o k)
      (fun c => ∃ ba bb, B94 g pa pb r csa csb ba bb m0 o k c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hpre, hframe⟩ := hSt
  have hka : k ≤ csa.length := prefix_le_lena hpre
  have hkb : k ≤ csb.length := prefix_le_lenb hpre
  -- byte values at pa+k, pb+k
  obtain ⟨ba, hbamem, _, hbaval⟩ := cstr_byte_val m0 pa.toNat csa hcstra k hka
  obtain ⟨bb, hbbmem, _, hbbval⟩ := cstr_byte_val m0 pb.toNat csb hcstrb k hkb
  obtain ⟨htna, hloa, hhia, hhtifa⟩ := byte_lbu_bounds pa csa.length k hrega hka
  obtain ⟨htnb, hlob, hhib, hhtifb⟩ := byte_lbu_bounds pb csb.length k hregb hkb
  -- === f84: lbu a2,0(a0) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006f84 c.σ c.tick c.steps (0x80006f84#64) vmi (pa + BitVec.ofNat 64 k) ba
      hgood hpc hmi ha0 hloaded rfl hloa hhia hhtifa
      (by rw [sext0_add, htna, hmem]; exact hbamem) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006f88#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006f84#64) 4 = (0x80006f88#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha2_1 : σ1.regs.get? Register.x12 = some (zero_extend (m := 64) ba) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === f88: lbu a3,0(a1) ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006f88 σ1 i1 (c.steps + 1) (0x80006f88#64) vmi1 (pb + BitVec.ofNat 64 k) bb
      hG1 hpc1 hmi1' ha1_1 (by rw [hmem1]; exact hloaded) rfl hlob hhib hhtifb
      (by rw [sext0_add, htnb, hmem1, hmem]; exact hbbmem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006f8c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006f88#64) 4 = (0x80006f8c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha2_2 := obs_alu_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
  have ha3_2 : σ2.regs.get? Register.x13 = some (zero_extend (m := 64) bb) :=
    obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === f8c: addi a0,a0,1 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006f8c σ2 i2 (c.steps + 1 + 1) (0x80006f8c#64) vmi2 (pa + BitVec.ofNat 64 k)
      hG2 hpc2 hmi2' ha0_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006f90#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006f8c#64) 4 = (0x80006f90#64 : BitVec 64) from by decide] at this
  have ha0_3 : σ3.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (k+1)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_incr1 pa k] at this
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha2_3 := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_2
  have ha3_3 := obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.2.2.2.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === f90: addi a1,a1,1 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006f90 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006f90#64) vmi3 (pb + BitVec.ofNat 64 k)
      hG3 hpc3 hmi3' ha1_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006f94#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006f90#64) 4 = (0x80006f94#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 : σ4.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (k+1)) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_incr1 pb k] at this
  have ha2_4 := obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_3
  have ha3_4 := obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs4 R hR.2.2.2.2.1 hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  have hmem4eq : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
  have hout4 : σ4.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3, hobs4] : σ4.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩,
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4),
    ba, bb, ?_⟩
  exact ⟨hG4, by rw [hmem4eq]; exact hloaded, by rw [hmem4eq]; exact hmem,
    hout4, hpc4, ha0_4, ha1_4,
    ha2_4, ha3_4, hra_4, ⟨vmi4, hmi4'⟩, hi4, hrega, hregb, hcstra, hcstrb, hpre,
    hbaval, hbbval, hframe_4⟩

/-! ### Byte-loop assembly (`Triple.loop`)

Invariant `BLoopI`: either at the loop head `0xf84` (some iteration `k`) or done at
`0xf9c` (`BF9c`, having found the first difference / common terminator). Guard
`BLoopB`: at the head. Measure `BLoopMu = max la lb + 1 - k` **at the head**, else
`0` — the exit edge to `0xf9c` drops the measure to `0`; the loop back-edge advances
`k`, strictly decreasing the measure since `k ≤ la` (prefix nonzero). -/

/-- The full body `0xf84 → (0xf84 | 0xf9c)`: straight-line then dispatch. -/
theorem byte_body_step (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (k : Nat) :
    Triple (BSt g pa pb r csa csb m0 o k)
      (fun c => BSt g pa pb r csa csb m0 o (k+1) c
        ∨ (∃ ba' bb', BF9c g r csa csb ba' bb' m0 o c)) :=
  (byte_straight g pa pb r csa csb m0 o k).seq
    (by
      intro c hc
      obtain ⟨ba, bb, hB94⟩ := hc
      exact byte_dispatch g pa pb r csa csb ba bb m0 o k c hB94)

def BAtHead (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ k, BSt g pa pb r csa csb m0 o k c

def BAtDone (g : (R : Register) → Option (RegisterType R)) (r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  ∃ ba bb, BF9c g r csa csb ba bb m0 o c

def BLoopI (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  BAtHead g pa pb r csa csb m0 o c ∨ BAtDone g r csa csb m0 o c

def BLoopB (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  BAtHead g pa pb r csa csb m0 o c

/-- Measure: `max la lb + 1 - k` at the head `0xf84` (via `a0 = pa + k`), else `0`. -/
def BLoopMu (pa : BitVec 64) (csa csb : List Char) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006f84#64)
  then max csa.length csb.length + 1 - (((c.σ.regs.get? Register.x10).getD (0#64)).toNat - pa.toNat)
  else 0

/-- At the head, `BLoopMu = max la lb + 1 - k`. -/
theorem bloopmu_head (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (k : Nat) (c : Config)
    (hSt : BSt g pa pb r csa csb m0 o k c) :
    BLoopMu pa csa csb c = max csa.length csb.length + 1 - k := by
  simp only [BLoopMu, hSt.pc, hSt.a0, Option.getD_some, if_pos]
  have h : (pa + BitVec.ofNat 64 k).toNat = pa.toNat + k :=
    ptrN pa k (by have := hSt.rega.nowrap; have := prefix_le_lena hSt.prefixEq; omega)
  rw [h]; omega

/-- **Byte-loop body**: one iteration re-establishes `BLoopI`, strictly decreasing
`BLoopMu`. Back-edge (`BSt (k+1)`): `k ≤ la` (prefix nonzero) ⇒ measure drops. Exit
(`BF9c`): measure `0` (PC ≠ `0xf84`). -/
theorem byte_loop_body (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) :
    Triple (fun c => BLoopI g pa pb r csa csb m0 o c ∧ BLoopB g pa pb r csa csb m0 o c
             ∧ BLoopMu pa csa csb c = n)
           (fun c => BLoopI g pa pb r csa csb m0 o c ∧ BLoopMu pa csa csb c < n) := by
  intro c hc
  obtain ⟨_, ⟨k, hSt⟩, hmu⟩ := hc
  have hmu_eq : BLoopMu pa csa csb c = max csa.length csb.length + 1 - k :=
    bloopmu_head g pa pb r csa csb m0 o k c hSt
  rw [hmu_eq] at hmu
  have hkla : k ≤ csa.length := prefix_le_lena hSt.prefixEq
  obtain ⟨c1, hs1, hstep⟩ := byte_body_step g pa pb r csa csb m0 o k c hSt
  rcases hstep with hHead | hDone
  · -- back-edge: BSt (k+1), measure drops (k ≤ la ⇒ k < la+1 ≤ max+1)
    refine ⟨c1, hs1, Or.inl ⟨k+1, hHead⟩, ?_⟩
    have hmu1 : BLoopMu pa csa csb c1 = max csa.length csb.length + 1 - (k+1) :=
      bloopmu_head g pa pb r csa csb m0 o (k+1) c1 hHead
    rw [hmu1, ← hmu]; omega
  · -- exit: BF9c, measure 0
    refine ⟨c1, hs1, Or.inr hDone, ?_⟩
    obtain ⟨ba, bb, hF9c⟩ := hDone
    have hmu1 : BLoopMu pa csa csb c1 = 0 := by
      simp only [BLoopMu, hF9c.pc]
      rw [if_neg (by intro h; injection h with h; exact absurd h (by decide))]
    rw [hmu1]; omega

/-- The byte loop runs from `BLoopI` to `BAtDone` (`0xf9c`). -/
theorem byte_loop_to_done (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) :
    Triple (BLoopI g pa pb r csa csb m0 o) (BAtDone g r csa csb m0 o) := by
  have hloop := Triple.loop (I := BLoopI g pa pb r csa csb m0 o)
    (B := BLoopB g pa pb r csa csb m0 o) (BLoopMu pa csa csb) (byte_loop_body g pa pb r csa csb m0 o)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hDone⟩

/-! ## Entry / alignment dispatch (`0xea0 … 0xeac`)

Entry at `0xea0`: `or a4,a0,a1`; `li t2,-1`; `andi a4,a4,7`; `bnez a4,0xf84`. The
**misaligned** case `(pa|pb) % 8 ≠ 0` takes the branch to the byte loop `0xf84` with
`BSt 0` (`a0 = pa`, `a1 = pb` unchanged). -/

/-- Entry precondition at `0x80006ea0` (byte path: `(pa|pb) % 8 ≠ 0` misaligned). -/
structure PreBCmp (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcmpLoaded c.σ.mem
  mem : c.σ.mem = m0
  out : c.σ.sailOutput = o
  pc : c.σ.regs.get? Register.PC = some (0x80006ea0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some pa
  a1 : c.σ.regs.get? Register.x11 = some pb
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  rega : StrcmpRegion pa csa.length
  regb : StrcmpRegion pb csb.length
  cstra : CStr m0 pa.toNat csa
  cstrb : CStr m0 pb.toNat csb
  misaligned : ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) ≠ 0#64
  hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R

/-- `bnez a4` is taken iff `a4 ≠ 0`. -/
theorem bnez_ne {v : BitVec 64} (h : v ≠ 0#64) : (v != (0#64)) = true := by
  rw [bne_iff_ne]; exact h

/-- **Entry (misaligned)** `0xea0 → 0xf84`: `or a4,a0,a1`; `li t2,-1`; `andi a4,a4,7`;
`bnez a4` taken. Establishes the byte-loop head `BSt 0`. -/
theorem entry_byte (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) :
    Triple (PreBCmp g pa pb r csa csb m0 o) (BAtHead g pa pb r csa csb m0 o) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmisal, hframe⟩ := hPre
  -- ea0: or a4,a0,a1 → a4 = pa | pb
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006ea0 c.σ c.tick c.steps (0x80006ea0#64) vmi pa pb hgood hpc hmi ha0 ha1 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006ea4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006ea0#64) 4 = (0x80006ea4#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha4_1 : σ1.regs.get? Register.x14 = some (pa ||| pb) :=
    obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs1 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe R hR)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- ea4: li t2,-1 → x7 (unused downstream; framed)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006ea4 σ1 i1 (c.steps + 1) (0x80006ea4#64) vmi1 hG1 hpc1 hmi1' (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006ea8#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006ea4#64) 4 = (0x80006ea8#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs2 R hR.2.2.1 hR).trans (hframe_1 R hR)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- ea8: andi a4,a4,7 → a4 = (pa|pb) & 7
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006ea8 σ2 i2 (c.steps + 1 + 1) (0x80006ea8#64) vmi2 (pa ||| pb)
      hG2 hpc2 hmi2' ha4_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006eac#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006ea8#64) 4 = (0x80006eac#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha4_3 : σ3.regs.get? Register.x14 = some ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
    fun R hR => (sframe_alu hobs3 R hR.2.2.2.2.2.2.2.1 hR).trans (hframe_2 R hR)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- eac: bnez a4 taken → f84
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006eac_taken σ3 i3 (c.steps + 1 + 1 + 1) (0x80006eac#64) vmi3
      ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12))
      hG3 hpc3 hmi3' ha4_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl (bnez_ne hmisal) hi3
  have hpceq : (0x80006eac#64 : BitVec 64) + sign_extend (m := 64) (0x00d8#13) = (0x80006f84#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006f84#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs4, hpceq]
  have ha0_4 := obs_btaken_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_btaken_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have hra_4 := obs_btaken_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have hframe_4 : ∀ R, NotWrittenStrcmp R → σ4.regs.get? R = g R :=
    fun R hR => (sframe_btaken hobs4 R hR).trans (hframe_3 R hR)
  obtain ⟨vmi4, hmi4'⟩ := obs_btaken_minstret hobs4
  have hmem4eq : σ4.mem = c.σ.mem := by rw [hmem4, hmem3, hmem2, hmem1]
  have hout4 : σ4.sailOutput = o :=
    (by chain_out [hobs1, hobs2, hobs3, hobs4] : σ4.sailOutput = c.σ.sailOutput).trans hout
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩,
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4),
    0, ?_⟩
  refine ⟨hG4, by rw [hmem4eq]; exact hloaded, by rw [hmem4eq]; exact hmem,
    hout4, hpc4, ?_, ?_,
    hra_4, ⟨vmi4, hmi4'⟩, hi4, hrega, hregb, hcstra, hcstrb, (fun i hi => absurd hi (by omega)), hframe_4⟩
  · rw [show pa + BitVec.ofNat 64 0 = pa from by simp]; exact ha0_4
  · rw [show pb + BitVec.ofNat 64 0 = pb from by simp]; exact ha1_4

/-! ## The byte-path `strcmp` spec (`PreBCmp → BDone`)

For the misaligned dispatch: entry → byte loop → `sub`/`ret`. `r` must be 4-aligned. -/
theorem strcmp_byte_path (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (halignr : r.toNat % 4 = 0) :
    Triple (PreBCmp g pa pb r csa csb m0 o) (BDone g r csa csb m0 o) := by
  refine ((entry_byte g pa pb r csa csb m0 o).seq
    ((fun c hc => byte_loop_to_done g pa pb r csa csb m0 o c (Or.inl hc)) :
      Triple (BAtHead g pa pb r csa csb m0 o) (BAtDone g r csa csb m0 o))).seq ?_
  -- BAtDone (∃ ba bb, BF9c) → BDone
  intro c hc
  obtain ⟨ba, bb, hF9c⟩ := hc
  exact byte_f9c_ret g r csa csb ba bb m0 o halignr c hF9c

/-! ## Top-level `strcmp` specification (byte path)

`strcmp_pre`/`strcmp_post` package the prompt's P/Q for the byte-loop dispatch. The
precondition pins the entry configuration (`PC = 0x80006ea0`, `x10 = pa`, `x11 = pb`,
`x1 = r` 4-aligned, `mem = m0`), `CString`s for both arguments, the `StrcmpRegion`
disjointness side conditions, the misalignment guard `(pa|pb) % 8 ≠ 0` selecting the
byte path, and the ghost-frame tie `g`.

The postcondition returns to `r` with `x10`'s **sign** equal to the spec sign
`strcmpSpecSign` (0 if equal; the sign of the first differing byte otherwise —
exactly what the interpreter's `!strcmp` / `strcmp < 0` uses), `x1 = r`, `mem = m0`,
`GoodState`, `tick < 2`, and the blanket frame outside strcmp's clobbers. -/

/-- Top-level precondition (byte path). -/
def strcmp_pre (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ StrcmpLoaded c.σ.mem ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧
  c.σ.regs.get? Register.PC = some (0x80006ea0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some pa ∧ c.σ.regs.get? Register.x11 = some pb ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  r.toNat % 4 = 0 ∧ CString m0 pa.toNat sa ∧ CString m0 pb.toNat sb ∧
  ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) ≠ 0#64 ∧
  (∀ cs, CStr m0 pa.toNat cs → StrcmpRegion pa cs.length) ∧
  (∀ cs, CStr m0 pb.toNat cs → StrcmpRegion pb cs.length) ∧
  (∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R)

/-- Top-level postcondition (byte path): returned to `r`; `x10`'s sign is the spec
sign of comparing `sa`, `sb` as byte streams (the `csa`/`csb` char lists witness the
`CString` representations, so `strcmpSpecSign csa csb` is the honest comparison). -/
def strcmp_post (g : (R : Register) → Option (RegisterType R))
    (r : BitVec 64) (pa pb : BitVec 64) (sa sb : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x1 = some r ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧ c.tick < 2 ∧
  (∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) ∧
  ∃ (csa csb : List Char) (x : BitVec 64),
    CStr m0 pa.toNat csa ∧ CStr m0 pb.toNat csb ∧
    sa = String.ofList csa ∧ sb = String.ofList csb ∧
    c.σ.regs.get? Register.x10 = some x ∧ strcmpSign x = strcmpSpecSign csa csb

/-- **`strcmp` total-correctness spec (byte-loop path).** From `strcmp_pre` the machine
runs to `strcmp_post`: it returns to `r` with `x10`'s sign the comparison sign, memory
unchanged. Bridges the `CString` existentials to the concrete `CStr` char-list ghosts. -/
theorem strcmp_spec (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (strcmp_pre g pa pb r sa sb m0 o) (strcmp_post g r pa pb sa sb m0 o) := by
  intro c hpre
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, hmi, htick, halignr,
    ⟨csa, hcstra, hsa⟩, ⟨csb, hcstrb, hsb⟩, hmisal, hrega, hregb, hframe⟩ := hpre
  have hPreB : PreBCmp g pa pb r csa csb m0 o c :=
    ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, hmi, htick,
      hrega csa hcstra, hregb csb hcstrb, hcstra, hcstrb, hmisal, hframe⟩
  obtain ⟨c', hsteps, hDone⟩ := strcmp_byte_path g pa pb r csa csb m0 o halignr c hPreB
  obtain ⟨hG', hpc', hra', hmem', hout', htick', ⟨x, hx, hsign⟩, hframe'⟩ := hDone
  exact ⟨c', hsteps, hG', hpc', hra', hmem', hout', htick', hframe', csa, csb, x, hcstra, hcstrb, hsa, hsb, hx, hsign⟩

/-! ## Closing note — what lands and what remains

**Complete & kernel-checked (`propext, Classical.choice, Quot.sound` only):** the
**byte-loop path** of newlib `strcmp`, end-to-end:

* `strcmp_spec` — from `strcmp_pre` (entry `0xea0`, both `CString`s, `StrcmpRegion`
  side conditions, misalignment guard `(pa|pb) % 8 ≠ 0`, ghost-frame tie) to
  `strcmp_post` (returned to `r`, `mem = m0`, `tick < 2`, blanket frame, and the
  RESULT `strcmpSign x10 = strcmpSpecSign csa csb`).
* `entry_byte` (`0xea0 → 0xf84`): `or a4,a0,a1`; `li t2,-1`; `andi a4,a4,7`;
  `bnez a4` taken (misaligned).
* `byte_loop_to_done` (`Triple.loop`, measure `max la lb + 1 - k`): `byte_straight`
  (`0xf84 → 0xf94`, two `lbu` + two `addi`) then `byte_dispatch` (`bne a2,a3`;
  `bnez a2` → loop `BSt (k+1)` | exit `BF9c`).
* `byte_f9c_ret` (`0xf9c → ret`): `sub a0,a2,a3`; `ret`, result-sign discharged.

**The result `Q` — SIGN class, honest.** `strcmpSpecSign csa csb` compares the two
NUL-terminated byte streams: `0` when equal; the sign of the first differing byte
otherwise. `strcmpSign x10` reads the sign of the returned `x10` (`= 0`, `toInt < 0`,
or `> 0`). The bridge `strcmpSign_sub` shows the machine `sub` of two zero-extended
`< 128` bytes has exactly this sign. **C-usage evidence:** `env.c`/`value.c` use
`strcmp(...) == 0` (equality); `interp.c` uses `cmp < 0/<=/>/>=` (ordering) — the
interpreter consumes the SIGN, so a sign-class `Q` is the honest, sufficient spec.

**Coverage.** Byte-loop path (misaligned dispatch) complete. The 8-aligned WORD fast
path (`0xeb0 … 0xf80`: `auipc`/`ld` magic-mask setup → 3×-unrolled word loop → lane
compare) is NOT proved here; `strcmp_pre` selects the byte path via the misalignment
guard. All 75 sites (`StrcmpSites`) exist, so the word path is site-threading +
its own magic-detection + lane-extraction arithmetic (analogous to `StrlenSpec`'s
word loop plus a `slli/srli`-probe first-difference-byte lemma).

**New gotchas (precise).**
1. `Mathlib is NOT available` here: `by_contra`, `push_neg`, `set`, `norm_num`,
   `Int.bmod_eq_of_le_of_lt` all fail. Use `rcases Nat.lt_or_ge`, `generalize … at`,
   and compute `BitVec.toInt` from `toNat` via `BitVec.toInt_eq_msb_cond` /
   `toInt_eq_toNat_of_lt` (the `2^64`-bmod route hits the literal-omega blowup AND
   missing lemmas).
2. `Char.ofNat b.toNat |>.toNat = b.toNat` (for `b < 128`) is
   `rw [Char.toNat, Char.ofNat, dif_pos …]; simp only [Char.ofNatAux, UInt32.toNat]; rfl`
   — no single simp set closes it; the `dif_pos` needs `Nat.isValidChar` as
   `Or.inl (b.toNat < 55296)`.
3. `byteVal cs k = 0` does NOT imply `k = cs.length` in general (a mid-string NUL
   char would also give 0). It only does UNDER `CStr` (interior chars nonzero):
   `cstr_byteVal_zero`. Feed the length equality from the machine's loaded NUL byte
   (`cstr_byte_val`'s iff), not from `byteVal` alone.
4. `firstDiff_prefix_eq` only needs byte *agreement* on `[0,k)`, not the full
   `BytePrefix` (which also demands nonzero). Split it out (`firstDiff_agree_eq`) so
   the equal-NUL exit (byte `k` is `0`, equal but not nonzero) can extend agreement
   to `k+1`. Using `BytePrefix` there is unprovable (byte `k` is the NUL).
5. `NotWrittenStrcmp` must list strcmp's FULL write-set `{x5,x6,x7,x10..x15}` (9 GPRs)
   plus the pc/tick set — `DivSpec.NotWritten` (only `x10..x13`) is too narrow to
   reuse; the frame helpers (`sframe_*`) are cloned with the wider destructure. The
   `hR.2.2…` projection index into `NotWrittenStrcmp` for the `(rd == R) = false`
   the ALU frame wants depends on `rd`'s position in the 9-GPR list (e.g. `x12` is
   `.2.2.2.2.2.1`) — count carefully per site.
-/

end Vsa.Sim
