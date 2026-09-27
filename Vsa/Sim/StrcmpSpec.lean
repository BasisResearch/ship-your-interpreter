import Vsa.Sim.StrcmpSites
import Vsa.Sim.ChainFrameOut
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DivSpec
import Vsa.Sim.StrlenSpec
import Vsa.MemRepr
import Vsa.Triple
import Vsa.Sim.ObsAvoid

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

/-! ### Byte-loop assembly (`Triple.loop`)

Invariant `BLoopI`: either at the loop head `0xf84` (some iteration `k`) or done at
`0xf9c` (`BF9c`, having found the first difference / common terminator). Guard
`BLoopB`: at the head. Measure `BLoopMu = max la lb + 1 - k` **at the head**, else
`0` — the exit edge to `0xf9c` drops the measure to `0`; the loop back-edge advances
`k`, strictly decreasing the measure since `k ≤ la` (prefix nonzero). -/

/-! ## Entry / alignment dispatch (`0xea0 … 0xeac`)

Entry at `0xea0`: `or a4,a0,a1`; `li t2,-1`; `andi a4,a4,7`; `bnez a4,0xf84`. The
**misaligned** case `(pa|pb) % 8 ≠ 0` takes the branch to the byte loop `0xf84` with
`BSt 0` (`a0 = pa`, `a1 = pb` unchanged). -/

/-! ## The byte-path `strcmp` spec (`PreBCmp → BDone`)

For the misaligned dispatch: entry → byte loop → `sub`/`ret`. `r` must be 4-aligned. -/

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
