import Vsa.Sim.MemcpySites
import Vsa.Sim.Muldi3Spec
import Vsa.Triple

/-!
# Layer 3 — `memcpy` byte-copy-path total-correctness spec (`memcpy_bytepath_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/MemcpySites.lean`) into a total-correctness triple for the **byte-copy
path** of newlib `memcpy` — the path taken when the source/destination alignment
fast-path does not apply.

This is the first STORE-heavy M3 spec; it pilots the **described-memory-update Q
pattern**. The loop body stores one byte per iteration, so the config predicate
`St` carries the current memory's relation to the ghosts `m0`/`bs` (a
copied-prefix description) and each `stepObs_store` transition threads it through
the single-byte insert (`Std.ExtHashMap.getElem?_insert` read-over-write; key
disequalities are omega-shaped from the region bounds + non-overlap).

## The byte loop (`[0x80006c48, 0x80006c5c)`, back-edge `0x58 → 0x48`)

At loop head `0x48`, iteration `i` (`0 ≤ i ≤ n`):
* `x11 (a1) = src + i`, `x14 (a4) = dst + i`, `x17 (a7) = dst + n`, `x10 (a0) = dst`;
* memory: bytes `[dst, dst+i)` hold `bs`; bytes outside `[dst, dst+n)` hold `m0`;
  the source region `[src+i, src+n)` still reads `bs` (non-overlap keeps it stable);
* measure `n - i` strictly decreases.

## Ghost parameters

`dst` (x10 in), `src` (x11 in), `n : Nat` (byte count, x12 in), `r` (x1, return
addr, 4-aligned), `m0` (pinned memory), `bs : List (BitVec 8)` (source bytes,
`bs.length = n`, `∀ k < n, m0[(src+k)] = bs[k]`). The described update is stated
observationally in `Q`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded memcpyChunk0 memcpyChunk1 memcpyChunk2 memcpyChunk3 memcpyChunk4)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Pointer arithmetic: `(base + ofNat k).toNat = base.toNat + k` under no-wrap -/

/-- If `base.toNat + k < 2^64`, the BitVec add is exact: `(base + k).toNat = base.toNat + k`. -/
theorem ptr_toNat (base : BitVec 64) (k : Nat) (h : base.toNat + k < 2^64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat]
  have hkmod : k % 2^64 = k := Nat.mod_eq_of_lt (by omega)
  rw [hkmod]
  exact Nat.mod_eq_of_lt h

/-- `sbData` on `zero_extend (m := 64) b` recovers the byte `b` (as `BitVec (8*1)`).
The stored low byte of `a5 = zero_extend b` is `b`. -/
theorem sbData_zext (b : BitVec 8) :
    sbData (zero_extend (m := 64) (b : BitVec (8*1))) = (b : BitVec (8*1)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [sbData, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
    zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
    Nat.shiftRight_zero]
  have hlt : (b : BitVec 8).toNat < 2^8 := b.isLt
  have key : ∀ W : Nat, (2:Nat)^W = 2^8 → (BitVec.ofNat W (b.toNat % 2^64)).toNat = b.toNat := by
    intro W hW
    rw [BitVec.toNat_ofNat, hW]
    have h2 : (b : BitVec 8).toNat % 2^64 = (b : BitVec 8).toNat := Nat.mod_eq_of_lt (by omega)
    rw [h2, Nat.mod_eq_of_lt hlt]
  exact key _ (by decide)

/-! ## `MemcpyLoaded` preserved by a single byte insert outside the code region -/

/-- Read-over-write at a distinct key: `(mem.insert k v)[a]? = mem[a]?` when `k ≠ a`. -/
theorem getElem_transfer (mem : Std.ExtHashMap Nat (BitVec 8)) (k a : Nat) (v b : BitVec 8)
    (hne : k ≠ a) (h : mem[a]? = some b) : (mem.insert k v)[a]? = some b := by
  rw [Std.ExtHashMap.getElem?_insert, if_neg (by simp [hne])]; exact h

/-- **`MemcpyLoaded` is preserved by inserting a byte outside the code region**
`[0x80006bc8, 0x80006cf0)`. Each of the 74×4 code-byte reads survives the insert
because its (concrete) address differs from the (out-of-range) key `k` (`omega`). -/
theorem loaded_insert (mem : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) (v : BitVec 8)
    (hk : k < 0x80006bc8 ∨ 0x80006cf0 ≤ k) (h : MemcpyLoaded mem) :
    MemcpyLoaded (mem.insert k v) := by
  obtain ⟨c0, c1, c2, c3, c4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [memcpyChunk0] at c0 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [memcpyChunk1] at c1 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [memcpyChunk2] at c2 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [memcpyChunk3] at c3 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])
  · simp only [memcpyChunk4] at c4 ⊢
    repeat' apply And.intro
    all_goals (apply getElem_transfer _ _ _ _ _ (by omega); simp_all only [])

/-! ## The described-memory invariant

`MemInv dst src n bs i mem` is the standing description of `mem` at loop iteration
`i` (`0 ≤ i ≤ n`), over the ghost byte function `bs : Nat → BitVec 8`:
* `copied`: the destination prefix `[dst, dst+i)` holds the copied bytes `bs`;
* `outside`: every address outside `[dst, dst+n)` still holds `m0`-content, stated
  as equal to the *source-provided* byte function via the reference map;
* `src_intact`: the remaining source region `[src+i, src+n)` still reads `bs`
  (non-overlap keeps the source stable across the copy).

We package the "outside untouched" description directly against a reference map
`m0` rather than `bs`, and carry `src_intact` explicitly (re-established each
iteration from `outside` + non-overlap). -/
structure MemInv (dst src : BitVec 64) (n : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8)) : Prop where
  copied : ∀ k, k < i → mem[(dst.toNat + k)]? = some (bs k)
  outside : ∀ a, (a < dst.toNat ∨ dst.toNat + n ≤ a) → mem[a]? = m0[a]?
  src_intact : ∀ k, i ≤ k → k < n → mem[(src.toNat + k)]? = some (bs k)

/-! ## Region bounds bundle

The disjointness / no-wraparound side facts used to discharge the store's
read-over-write key disequalities and the pointer arithmetic. `dst`, `src`, `n`
are the ghosts. -/
structure Regions (dst src : BitVec 64) (n : Nat) : Prop where
  dst_nowrap : dst.toNat + n < 2^64
  src_nowrap : src.toNat + n < 2^64
  disjoint : dst.toNat + n ≤ src.toNat ∨ src.toNat + n ≤ dst.toNat
  -- the destination region is disjoint from the `memcpy` code `[0x80006bc8, 0x80006cf0)`
  code_disjoint : dst.toNat + n ≤ 0x80006bc8 ∨ 0x80006cf0 ≤ dst.toNat
  -- both regions in RAM `[0x80000000, 0x100000000)`
  dst_lo : 0x80000000 ≤ dst.toNat
  dst_hi : dst.toNat + n ≤ 0x100000000
  src_lo : 0x80000000 ≤ src.toNat
  src_hi : src.toNat + n ≤ 0x100000000
  -- both regions above the HTIF window (`tohostAddr = 0x8001ad00`, ± 16)
  dst_win : tohostAddr + 16 ≤ dst.toNat
  src_win : tohostAddr + 16 ≤ src.toNat

/-- **Store preserves the memory invariant.** From `MemInv … i mem` at iteration
`i < n`, storing byte `bs i` at `dst + i` re-establishes `MemInv … (i+1)` for the
updated map `mem.insert (dst.toNat + i) (bs i)`. All key disequalities are
omega-shaped from `Regions`. -/
theorem meminv_store (dst src : BitVec 64) (n : Nat) (bs : Nat → BitVec 8) (i : Nat)
    (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (hreg : Regions dst src n) (hi : i < n)
    (hinv : MemInv dst src n bs i m0 mem) :
    MemInv dst src n bs (i + 1) m0 (mem.insert (dst.toNat + i) (bs i)) := by
  refine ⟨?_, ?_, ?_⟩
  · -- copied for k < i+1
    intro k hk
    rw [Std.ExtHashMap.getElem?_insert]
    by_cases hik : k = i
    · subst hik; simp only [beq_self_eq_true, if_true]
    · have hne : ((dst.toNat + i) == (dst.toNat + k)) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; omega
      rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
      exact hinv.copied k (by omega)
  · -- outside untouched (the inserted key dst+i is inside [dst,dst+n))
    intro a ha
    rw [Std.ExtHashMap.getElem?_insert]
    have hne : ((dst.toNat + i) == a) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]; omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv.outside a ha
  · -- source region [src+(i+1), src+n) still reads bs (disjoint from dst+i)
    intro k hik hkn
    rw [Std.ExtHashMap.getElem?_insert]
    have hne : ((dst.toNat + i) == (src.toNat + k)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      rcases hreg.disjoint with hd | hd <;> omega
    rw [if_neg (by simp only [hne, Bool.false_eq_true, not_false_eq_true])]
    exact hinv.src_intact k (by omega) hkn

/-! ## Blanket ghost-frame predicate (`NotWrittenB`) + generic per-class helpers

`StB` tracks the byte-loop live GPRs (`x10, x11, x14, x17, x1`) plus the scratch
`x15`. To make preservation of *every other* register recoverable after packaging
into a `Triple` (needed by callers that need callee-saved / `sp` preservation),
`StB` carries a ghost snapshot `g : (R : Register) → Option (RegisterType R)` and a
blanket conjunct: every register outside the write-set reads as its ghost value.

`NotWrittenB R` is the disequality conjunction over the union of the byte-path
written GPRs (`x11` = `addi a1`, `x14` = `mv a4`/`addi a4`, `x15` = `lbu a5`) and the
per-step write-set / tick-set registers (`PC, nextPC, minstret, minstret_increment,
mcycle, mtime, mip`). The STORE writes only memory (no rd), so it is covered by the
noise disequalities alone. -/

/-- `R` is outside the union of the byte-path written GPRs (`x11, x14, x15`) and
every register any hot-path step (ALU / branch / store / tick) can write. -/
abbrev NotWrittenB (R : Register) : Prop :=
  (Register.x11 == R) = false ∧ (Register.x14 == R) = false ∧
  (Register.x15 == R) = false ∧
  (Register.PC == R) = false ∧ (Register.nextPC == R) = false ∧
  (Register.minstret == R) = false ∧ (Register.minstret_increment == R) = false ∧
  (Register.mcycle == R) = false ∧ (Register.mtime == R) = false ∧
  (Register.mip == R) = false

theorem NotWrittenB.x11 {R : Register} (h : NotWrittenB R) : (Register.x11 == R) = false := h.1
theorem NotWrittenB.x14 {R : Register} (h : NotWrittenB R) : (Register.x14 == R) = false := h.2.1
theorem NotWrittenB.x15 {R : Register} (h : NotWrittenB R) : (Register.x15 == R) = false := h.2.2.1

/-- Generic ALU frame step for the byte path. -/
theorem frame_alu_b {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) (R : Register)
    (hrd : (rd == R) = false) (hR : NotWrittenB R) :
    σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_alu σ pc vm rd v R hmi hpc hrd hnpc hmii

/-- Generic taken-branch frame step for the byte path (no `rd`). -/
theorem frame_btaken_b {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenB R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

/-- Generic not-taken-branch frame step for the byte path. -/
theorem frame_bnottaken_b {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenB R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-- Generic STORE frame step (write-set `PC, minstret, nextPC, minstret_increment`;
NO `rd` — the store touches only memory, so every non-noise register is preserved). -/
theorem frame_store_b {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register)
    (hR : NotWrittenB R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_store σ pc vm m' R hmi hpc hnpc hmii

/-- Generic `jr`/`ret` frame step for the byte path. -/
theorem frame_jr_b {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) (R : Register)
    (hR : NotWrittenB R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_jump_x0 σ pc vm tgt R hmi hpc hnpc hmii

/-! ## The config-level state predicate

`StB pc i r dst src n m0 bs c` is the standing observation at a byte-loop program
point `pc`, iteration `i`. It bundles `GoodState`, code loaded, PC at `pc`, the
live pointers (`a1 = src+i`, `a4 = dst+i`, `a7 = dst+n`, `a0 = dst`), the return
register `x1 = r`, `minstret` defined, `tick < 2`, the `Regions` bounds, `i ≤ n`,
and the described-memory invariant `MemInv … i`. The scratch register `a5` (x15)
is not tracked (overwritten every iteration).

The pointer registers are stated at their `BitVec` values `src + ofNat i` etc.;
`ptr_toNat` bridges to `.toNat` where the fetch/access bounds need it. -/
structure StB (g : (R : Register) → Option (RegisterType R)) (pc : BitVec 64) (i : Nat)
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some pc
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 i)
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 i)
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  ile : i ≤ n
  meminv : MemInv dst src n bs i m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R

/-! ## Pointer BitVec identities (unconditional, mod-2^64) -/

/-- `base + ofNat i + 1 = base + ofNat (i+1)` (the `addi …,1` increment). -/
theorem ptr_succ (base : BitVec 64) (i : Nat) :
    base + BitVec.ofNat 64 i + sign_extend (m := 64) (0x001#12) = base + BitVec.ofNat 64 (i + 1) := by
  apply BitVec.eq_of_toNat_eq
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 from by apply BitVec.eq_of_toNat_eq; decide]
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `ofNat (i+1) = ofNat i + 1` in `BitVec 64`. -/
theorem ofNat_succ (i : Nat) : (BitVec.ofNat 64 (i + 1) : BitVec 64) = BitVec.ofNat 64 i + 1#64 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

/-- `sbAddr (base + ofNat (i+1)) = base + ofNat i`: the `sb …,-1(a4)` back-offset
undoes the increment (`+ sext 0xfff = - 1`), proved via `BitVec` group ops (no
`2^64`-literal omega). -/
theorem sbAddr_succ (base : BitVec 64) (i : Nat) :
    sbAddr (base + BitVec.ofNat 64 (i + 1)) = base + BitVec.ofNat 64 i := by
  show (base + BitVec.ofNat 64 (i+1)) + sign_extend (m := 64) (0xfff#12) = base + BitVec.ofNat 64 i
  have hsext : (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -(1#64) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hsext, ofNat_succ]
  generalize BitVec.ofNat 64 i = w
  rw [BitVec.add_assoc base (w + 1#64) (-(1#64)), BitVec.add_assoc w (1#64) (-(1#64)),
    show (1#64 + -(1#64) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
    BitVec.add_zero]

/-! ## State at 0x58 (post-store, pre-`bne`) for iteration `i`

`StB58 i r dst src n m0 bs c` describes the config after one full loop body
(load/addi/addi/store) for iteration `i < n`: the pointers are advanced by one
(`a1 = src+(i+1)`, `a4 = dst+(i+1)`), `a7 = dst+n`, `a0 = dst`, and the memory
invariant has moved to `i+1`. -/
structure StB58 (g : (R : Register) → Option (RegisterType R)) (i : Nat)
    (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c58#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (i + 1))
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (i + 1))
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  ile : i + 1 ≤ n
  meminv : MemInv dst src n bs (i + 1) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R

/-! ## RAM/window facts for the per-iteration source and dest pointers

From `Regions` + `i < n`, the pointer `p + ofNat i` (for `p ∈ {dst, src}`) lands in
RAM and above the HTIF window; `ptr_toNat` bridges `.toNat`. -/

theorem src_ptr_bounds (dst src : BitVec 64) (n : Nat) (hreg : Regions dst src n) (i : Nat)
    (hi : i < n) :
    (src + BitVec.ofNat 64 i).toNat = src.toNat + i ∧
    0x80000000 ≤ (src + BitVec.ofNat 64 i).toNat ∧
    (src + BitVec.ofNat 64 i).toNat + 1 ≤ 0x100000000 ∧
    ((src + BitVec.ofNat 64 i).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (src + BitVec.ofNat 64 i).toNat) := by
  have htn : (src + BitVec.ofNat 64 i).toNat = src.toNat + i :=
    ptr_toNat src i (by have := hreg.src_nowrap; omega)
  have hlo := hreg.src_lo
  have hhi := hreg.src_hi
  have hwin := hreg.src_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_⟩
  · rw [htn]; omega
  · rw [htn]; omega
  · right; rw [htn]; omega

theorem dst_ptr_bounds (dst src : BitVec 64) (n : Nat) (hreg : Regions dst src n) (i : Nat)
    (hi : i < n) :
    (dst + BitVec.ofNat 64 (i + 1)).toNat = dst.toNat + (i + 1) ∧
    0x80000000 ≤ (sbAddr (dst + BitVec.ofNat 64 (i + 1))).toNat ∧
    (sbAddr (dst + BitVec.ofNat 64 (i + 1))).toNat + 1 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ (sbAddr (dst + BitVec.ofNat 64 (i + 1))).toNat ∧
    (sbAddr (dst + BitVec.ofNat 64 (i + 1))).toNat = dst.toNat + i := by
  have htn : (dst + BitVec.ofNat 64 (i + 1)).toNat = dst.toNat + (i + 1) :=
    ptr_toNat dst (i + 1) (by have := hreg.dst_nowrap; omega)
  have hsb : (sbAddr (dst + BitVec.ofNat 64 (i + 1))).toNat = dst.toNat + i := by
    rw [sbAddr_succ]; exact ptr_toNat dst i (by have := hreg.dst_nowrap; omega)
  have hlo := hreg.dst_lo
  have hhi := hreg.dst_hi
  have hwin := hreg.dst_win
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, hsb⟩
  · rw [hsb]; omega
  · rw [hsb]; omega
  · rw [hsb]; omega

/-! ## STORE-observation consumers

From a STORE observation `ReadsLikePost σ' (sigmaPost_store σ pc vm m')`, read the
framing fields: `obs_store_pc` gives PC := pc+4; `obs_store_other` gives any GPR
from `σ` (the STORE writes only memory); `obs_store_minstret` gives minstret
defined. These mirror the `obs_alu_*` consumers over the `sigmaPost_store` frame. -/

theorem post_store_pc (σ : MState) (pc vminstret : BitVec 64)
    (m' : Std.ExtHashMap Nat (BitVec 8)) :
    (sigmaPost_store σ pc vminstret m').regs.get? Register.PC = some (BitVec.addInt pc 4) := by
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vminstret 1))).get? Register.PC = _
  rw [Std.ExtDHashMap.get?_insert]
  simp only [show (Register.minstret == Register.PC) = false from by decide, dif_neg, reduceCtorEq, not_false_eq_true]
  rw [Std.ExtDHashMap.get?_insert_self]

theorem obs_store_pc {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    σ'.regs.get? Register.PC = some (BitVec.addInt pc 4) :=
  readback σ' _ hobs Register.PC (by decide) (by decide) (by decide) (post_store_pc σ pc vm m')

theorem obs_store_other {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) (R : Register) {w : RegisterType R}
    (hmc : (Register.mcycle == R) = false) (hmt : (Register.mtime == R) = false)
    (hmi : (Register.mip == R) = false)
    (h1 : (Register.minstret == R) = false) (h2 : (Register.PC == R) = false)
    (h4 : (Register.nextPC == R) = false) (h5 : (Register.minstret_increment == R) = false)
    (hσ : σ.regs.get? R = some w) : σ'.regs.get? R = some w :=
  readback σ' _ hobs R hmc hmt hmi ((get?_sigmaPost_store σ pc vm m' R h1 h2 h4 h5).trans hσ)

theorem obs_store_minstret {σ' σ : MState} {pc vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) :
    ∃ w, σ'.regs.get? Register.minstret = some w := by
  refine ⟨BitVec.addInt vm 1, readback σ' _ hobs Register.minstret (w := BitVec.addInt vm 1)
    (by decide) (by decide) (by decide) ?_⟩
  show ((((sigma3_store σ pc m').regs.insert Register.PC (BitVec.addInt pc 4)).insert
    Register.minstret (BitVec.addInt vm 1))).get? Register.minstret = _
  rw [Std.ExtDHashMap.get?_insert_self]

/-! ## One loop body iteration (`0x48 → 0x58`)

Chains `lbu → addi a4 → addi a1 → sb`. The `lbu` reads `bs i` from `src+i`
(`src_intact`); the two `addi`s advance the pointers; the `sb` writes `bs i` back
at `dst+i` (`sbAddr_succ`), and `meminv_store` re-establishes `MemInv … (i+1)`. -/
theorem iterB (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (hi : i < n) :
    Triple (StB g (0x80006c48#64) i r dst src n m0 bs) (StB58 g i r dst src n m0 bs) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hile, hminv, hframe⟩ := hSt
  obtain ⟨htn_src, hslo, hshi, hshtif⟩ := src_ptr_bounds dst src n hreg i hi
  obtain ⟨htn_dst, hdlo, hdhi, hdwin, hsbeq⟩ := dst_ptr_bounds dst src n hreg i hi
  -- the loaded byte b = bs i (src_intact at index i)
  have hbyte : c.σ.mem[(src + BitVec.ofNat 64 i).toNat]? = some (bs i) := by
    rw [htn_src]; exact hminv.src_intact i (Nat.le_refl i) hi
  -- === c48: lbu a5,0(a1) ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c48 c.σ c.tick c.steps (0x80006c48#64) vmi (src + BitVec.ofNat 64 i) (bs i)
      hgood hpc hmi ha1 hloaded rfl hslo hshi hshtif hbyte htick
  -- read the successor's registers/mem
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c4c#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c48#64) 4 = (0x80006c4c#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha4_1 := obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have ha7_1 := obs_alu_other hobs1 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hmi_1 := obs_alu_minstret hobs1
  -- === c4c: addi a4,a4,1 ===
  obtain ⟨vmi1, hmi1'⟩ := hmi_1
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c4c σ1 i1 (c.steps + 1) (0x80006c4c#64) vmi1 (dst + BitVec.ofNat 64 i)
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c50#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006c4c#64) 4 = (0x80006c50#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha7_2 := obs_alu_other hobs2 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_alu_other hobs2 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (i + 1)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_succ dst i] at this
  have hmi_2 := obs_alu_minstret hobs2
  -- === c50: addi a1,a1,1 ===
  obtain ⟨vmi2, hmi2'⟩ := hmi_2
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006c50 σ2 i2 (c.steps + 1 + 1) (0x80006c50#64) vmi2 (src + BitVec.ofNat 64 i)
      hG2 hpc2 hmi2' ha1_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c54#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006c50#64) 4 = (0x80006c54#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha4_3 := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_2
  have ha7_3 := obs_alu_other hobs3 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha5_3 := obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_2
  have ha1_3 : σ3.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (i + 1)) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptr_succ src i] at this
  have hmi_3 := obs_alu_minstret hobs3
  -- === c54: sb a5,-1(a4) ===  (a5 = zext (bs i), a4 = dst + (i+1))
  obtain ⟨vmi3, hmi3'⟩ := hmi_3
  -- σ3.mem = c.σ.mem (three regs-only steps)
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006c54 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006c54#64) vmi3
      (dst + BitVec.ofNat 64 (i + 1)) (zero_extend (m := 64) ((bs i) : BitVec (8*1)))
      hG3 hpc3 hmi3' ha4_3 ha5_3 (by rw [hmem3eq]; exact hloaded) rfl
      hdlo hdhi hdwin hi3
  -- the store's post map, simplified
  have hstore_mem : σ4.mem = c.σ.mem.insert (dst.toNat + i) (bs i) := by
    rw [hmem4, mem_afterNextPC, hmem3eq, sbData_zext, hsbeq]
  have hsteps : Steps c ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ :=
    (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans (Steps.single hs4)
  refine ⟨⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩, hsteps, ?_⟩
  · -- StB58 i
    have hpc4 : σ4.regs.get? Register.PC = some (0x80006c58#64 : BitVec 64) := by
      have := obs_store_pc hobs4
      rwa [show BitVec.addInt (0x80006c54#64) 4 = (0x80006c58#64 : BitVec 64) from by decide] at this
    have ha0_4 := obs_store_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
    have ha1_4 := obs_store_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
    have ha4_4 := obs_store_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_3
    have ha7_4 := obs_store_other hobs4 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_3
    have hra_4 := obs_store_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
    have hmi_4 := obs_store_minstret hobs4
    refine ⟨hG4,
      by rw [hstore_mem]
         exact loaded_insert c.σ.mem (dst.toNat + i) (bs i)
           (by have := hreg.code_disjoint; have := hreg.dst_nowrap; omega) hloaded,
      hpc4, ha0_4, ha1_4, ha4_4, ha7_4, hra_4, hmi_4, hi4, hreg, hi, ?_, ?_⟩
    · -- MemInv … (i+1) via meminv_store, with σ4.mem = c.σ.mem.insert (dst.toNat+i) (bs i)
      rw [hstore_mem]
      exact meminv_store dst src n bs i m0 c.σ.mem hreg hi hminv
    · -- frame: thread g through the 4 body steps (lbu x15, addi x14, addi x11, sb)
      intro R hR
      have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_b hobs1 R hR.x15 hR
      have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_b hobs2 R hR.x14 hR
      have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_b hobs3 R hR.x11 hR
      have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_store_b hobs4 R hR
      rw [e4, e3, e2, e1]; exact hframe R hR

/-! ## The `bne a7,a4` at 0x58 (loop back-edge / exit to ret)

`a7 = dst+n`, `a4 = dst+(i+1)`. Taken iff `a7 ≠ a4` iff `i+1 < n` (no-wrap); loops
back to `0x48` iteration `i+1`. Not-taken iff `i+1 = n`; falls through to `0x5c`
(ret) with the full described update in place (`MemInv … n`). -/

/-- The "done" configuration at 0x5c (ret entry): `a0 = dst` (memcpy returns dst),
`x1 = r`, and the full described memory update `MemInv … n`. -/
structure StBDone (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c5c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a4 : c.σ.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 n)
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  meminv : MemInv dst src n bs n m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R

/-- `bne a7,a4` value guard: `a7 = dst+n`, `a4 = dst+(i+1)`, `i+1 < n` ⇒ `!=` is true. -/
theorem bne_true (dst : BitVec 64) (n i : Nat) (hreg_nw : dst.toNat + n < 2^64)
    (hlt : i + 1 < n) :
    ((dst + BitVec.ofNat 64 n) != (dst + BitVec.ofNat 64 (i + 1))) = true := by
  rw [bne_iff_ne, ne_eq]
  intro heq
  have h1 : (dst + BitVec.ofNat 64 n).toNat = dst.toNat + n := ptr_toNat dst n (by omega)
  have h2 : (dst + BitVec.ofNat 64 (i+1)).toNat = dst.toNat + (i+1) := ptr_toNat dst (i+1) (by omega)
  rw [heq] at h1; omega

/-- `bne a7,a4` value guard: `i+1 = n` ⇒ `!=` is false (`a7 = a4`). -/
theorem bne_false (dst : BitVec 64) (n i : Nat) (heq : i + 1 = n) :
    ((dst + BitVec.ofNat 64 n) != (dst + BitVec.ofNat 64 (i + 1))) = false := by
  rw [heq]; simp only [bne_self_eq_false]

/-- `bne a7,a4` taken (0x58 → 0x48): loop back to iteration `i+1`. -/
theorem tr_bne_back (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (hlt : i + 1 < n) :
    Triple (StB58 g i r dst src n m0 bs) (StB g (0x80006c48#64) (i + 1) r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hile, hminv, hframe⟩ := hSt
  have hv : ((dst + BitVec.ofNat 64 n) != (dst + BitVec.ofNat 64 (i + 1))) = true :=
    bne_true dst n i hreg.dst_nowrap hlt
  have htgt : ((0x80006c58#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006c58_taken c.σ c.tick c.steps (0x80006c58#64) vmi (dst + BitVec.ofNat 64 n)
      (dst + BitVec.ofNat 64 (i + 1)) hgood hpc hmi ha7 ha4 hloaded rfl htgt hv htick
  have hpceq : (0x80006c58#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13) = (0x80006c48#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_btaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_btaken_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, by omega, by rw [hmem']; exact hminv,
    fun R hR => (frame_btaken_b hobs R hR).trans (hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bne a7,a4` not taken (0x58 → 0x5c, `i+1 = n`): fall through to ret with the
full described update. -/
theorem tr_bne_done (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (heq : i + 1 = n) :
    Triple (StB58 g i r dst src n m0 bs) (StBDone g r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hile, hminv, hframe⟩ := hSt
  have hv : ((dst + BitVec.ofNat 64 n) != (dst + BitVec.ofNat 64 (i + 1))) = false :=
    bne_false dst n i heq
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006c58_nottaken c.σ c.tick c.steps (0x80006c58#64) vmi (dst + BitVec.ofNat 64 n)
      (dst + BitVec.ofNat 64 (i + 1)) hgood hpc hmi ha7 ha4 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006c5c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006c58#64) 4 = (0x80006c5c#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, hpc',
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    ?_, ?_,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, ?_,
    fun R hR => (frame_bnottaken_b hobs R hR).trans (hframe R hR)⟩
  · -- a4 = dst+(i+1) = dst+n
    have := obs_bnottaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
    rwa [heq] at this
  · -- a7 = dst+n
    exact obs_bnottaken_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7
  · -- MemInv … n from MemInv … (i+1) via i+1 = n (rewrite only the iteration index)
    rw [hmem']
    exact heq ▸ hminv

/-! ## Loop invariant, guard, measure

`LoopIB = AtHeadB ∨ AtDone`: either at `0x48` iteration `i ≤ n` (with the described
memory prefix), or done at `0x5c` (ret) with the full update. `LoopB` = "at `0x48`
with `i < n`" (more to copy). Measure `LoopMuB = a7.toNat - a4.toNat = n - i`
(computed from the pointer registers; total via `getD`). -/

/-- At the loop head `0x48`, some iteration `i < n` (strict: the head is only ever
reached with copy remaining; the exiting iteration leaves via the `bne` to
`StBDone`, never back to the head at `i = n`). -/
def AtHeadB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) : Prop :=
  ∃ i, i < n ∧ StB g (0x80006c48#64) i r dst src n m0 bs c

def LoopIB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadB g r dst src n m0 bs c ∨ StBDone g r dst src n m0 bs c

/-- Loop guard: at the head (`AtHeadB`, which already implies `i < n`). -/
def LoopBB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadB g r dst src n m0 bs c

/-- Loop measure: `a7.toNat - a4.toNat` (= `n - i` at the head). -/
def LoopMuB (c : Config) : Nat :=
  ((c.σ.regs.get? Register.x17).getD (0#64)).toNat - ((c.σ.regs.get? Register.x14).getD (0#64)).toNat

/-- At loop head iteration `i`, `LoopMuB = n - i`. -/
theorem loopmu_headB (g : (R : Register) → Option (RegisterType R)) (i : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config)
    (hSt : StB g (0x80006c48#64) i r dst src n m0 bs c) (hile : i ≤ n) :
    LoopMuB c = n - i := by
  simp only [LoopMuB, hSt.a7, hSt.a4, Option.getD_some]
  have h7 : (dst + BitVec.ofNat 64 n).toNat = dst.toNat + n :=
    ptr_toNat dst n (by have := hSt.regions.dst_nowrap; omega)
  have h4 : (dst + BitVec.ofNat 64 i).toNat = dst.toNat + i :=
    ptr_toNat dst i (by have := hSt.regions.dst_nowrap; omega)
  rw [h7, h4]; omega

/-- **Loop body**: one full iteration (`iterB` then `bne`) re-establishes `LoopIB`
strictly decreasing `LoopMuB`. -/
theorem loop_bodyB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (k : Nat) :
    Triple (fun c => LoopIB g r dst src n m0 bs c ∧ LoopBB g r dst src n m0 bs c ∧ LoopMuB c = k)
           (fun c => LoopIB g r dst src n m0 bs c ∧ LoopMuB c < k) := by
  intro c hc
  obtain ⟨_, ⟨i, hilt, hSt⟩, hmu⟩ := hc
  have hmu_eq : LoopMuB c = n - i := loopmu_headB g i r dst src n m0 bs c hSt (Nat.le_of_lt hilt)
  rw [hmu_eq] at hmu
  -- one iteration to 0x58
  obtain ⟨c1, hs1, hSt58⟩ := iterB g i r dst src n m0 bs hilt c hSt
  by_cases hdone : i + 1 = n
  · -- exit: bne not taken → StBDone
    obtain ⟨c2, hs2, hDone⟩ := tr_bne_done g i r dst src n m0 bs hdone c1 hSt58
    refine ⟨c2, hs1.trans hs2, Or.inr hDone, ?_⟩
    -- LoopMuB c2 = a7.toNat - a4.toNat = (dst+n) - (dst+n) = 0 < k (= n-i = 1 since i+1=n)
    have hmu2 : LoopMuB c2 = 0 := by
      simp only [LoopMuB, hDone.a7, hDone.a4, Option.getD_some, Nat.sub_self]
    rw [hmu2]; omega
  · -- loop back: bne taken → AtHeadB (i+1)
    have hlt2 : i + 1 < n := by omega
    obtain ⟨c2, hs2, hSt2⟩ := tr_bne_back g i r dst src n m0 bs hlt2 c1 hSt58
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨i + 1, hlt2, hSt2⟩, ?_⟩
    have hmu2 : LoopMuB c2 = n - (i + 1) := loopmu_headB g (i+1) r dst src n m0 bs c2 hSt2 (Nat.le_of_lt hlt2)
    rw [hmu2, ← hmu]; omega

/-- The loop runs to `StBDone` (`0x5c`, full described update). `Triple.loop`
reaches `LoopIB ∧ ¬LoopBB`; `¬LoopBB` = ¬`AtHeadB`, so the invariant's `AtHeadB`
disjunct is excluded and only `StBDone` remains. -/
theorem loop_to_doneB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (LoopIB g r dst src n m0 bs) (StBDone g r dst src n m0 bs) := by
  have hloop := Triple.loop (I := LoopIB g r dst src n m0 bs) (B := LoopBB g r dst src n m0 bs)
    LoopMuB (loop_bodyB g r dst src n m0 bs)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hDone⟩

/-! ## Prefix `0x40 → 0x48`: `mv a4,a0` then `bgeu a0,a7` not-taken

Entry (byte path): `a0 = dst`, `a1 = src`, `a7 = dst+n`, with `n > 0`. `mv a4,a0`
sets `a4 := dst`; `bgeu a0,a7` is not-taken (`dst <u dst+n` since `n > 0`, no wrap),
falling to `0x48` iteration `0`. -/

/-- Entry precondition at `0x40` (byte path): the ghost pointers in place, `n > 0`,
regions well-formed, and the described-memory invariant at `i = 0` (nothing copied
yet, `mem = m0` outside, source fully readable). -/
structure PreB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c40#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  npos : 0 < n
  meminv : MemInv dst src n bs 0 m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R

/-- `bgeu a0,a7` not-taken value: `dst <u dst+n` (`n > 0`, no wrap) ⇒ `≥u` is false. -/
theorem bgeu_false_dst_span (dst : BitVec 64) (n : Nat) (hnw : dst.toNat + n < 2^64) (hn : 0 < n) :
    zopz0zKzJ_u dst (dst + BitVec.ofNat 64 n) = false := by
  have hval : (dst + BitVec.ofNat 64 n).toNat = dst.toNat + n := ptr_toNat dst n (by omega)
  unfold zopz0zKzJ_u Sail.BitVec.toNatInt
  rw [decide_eq_false_iff_not, ge_iff_le, hval]
  simp only [Int.ofNat_eq_natCast]
  omega

/-- Prefix: `0x40 → 0x48` establishing `AtHeadB` at iteration `0`. -/
theorem prefixB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreB g r dst src n m0 bs) (AtHeadB g r dst src n m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hnpos, hminv, hframe⟩ := hPre
  -- 0x40: mv a4,a0  (a4 := dst)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c40 c.σ c.tick c.steps (0x80006c40#64) vmi dst hgood hpc hmi ha0 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c44#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c40#64) 4 = (0x80006c44#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha7_1 := obs_alu_other hobs1 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha4_1 : σ1.regs.get? Register.x14 = some dst := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show dst + sign_extend (m := 64) (0x000#12) = dst from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide]; exact BitVec.add_zero dst] at this
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- 0x44: bgeu a0,a7 not-taken → 0x48
  have hv : zopz0zKzJ_u dst (dst + BitVec.ofNat 64 n) = false := bgeu_false_dst_span dst n hreg.dst_nowrap hnpos
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c44_nottaken σ1 i1 (c.steps + 1) (0x80006c44#64) vmi1 dst (dst + BitVec.ofNat 64 n)
      hG1 hpc1 hmi1' ha0_1 ha7_1 (by rw [hmem1]; exact hloaded) rfl hv hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c48#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs2; rwa [show BitVec.addInt (0x80006c44#64) 4 = (0x80006c48#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), 0, hnpos, ?_⟩
  refine ⟨hG2, by rw [hmem2, hmem1]; exact hloaded, hpc2, ?_, ?_, ?_, ?_,
    obs_bnottaken_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1,
    obs_bnottaken_minstret hobs2, hi2, hreg, Nat.zero_le n, ?_,
    fun R hR => (frame_bnottaken_b hobs2 R hR).trans
      ((frame_alu_b hobs1 R hR.x14 hR).trans (hframe R hR))⟩
  · exact obs_bnottaken_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  · -- a1 = src = src + ofNat 0
    have := obs_bnottaken_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
    rwa [show src = src + BitVec.ofNat 64 0 from by rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]] at this
  · -- a4 = dst = dst + ofNat 0
    have := obs_bnottaken_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
    rwa [show dst = dst + BitVec.ofNat 64 0 from by rw [show (BitVec.ofNat 64 0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero]] at this
  · exact obs_bnottaken_other hobs2 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_1
  · -- MemInv at i=0
    rw [hmem2, hmem1]; exact hminv

/-! ## `ret` (`0x5c → r`) and the byte-path spec

`ret` reads `x1 = r` (4-aligned), redirects the PC to `r`, and preserves all GPRs
— in particular `x10 = dst` (memcpy returns the destination) and the described
memory update `MemInv … n`. -/

/-- The described-update postcondition: PC back at `r`, `x10 = dst`, `GoodState`,
`x1 = r`, and the observational described update — the `n` copied bytes are present
at `[dst, dst+n)` and everything outside is unchanged from `m0`. -/
def memcpy_bytepath_post (g : (R : Register) → Option (RegisterType R)) (r dst : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some dst ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∀ k, k < n → c.σ.mem[(dst.toNat + k)]? = some (bs k)) ∧
  (∀ a, (a < dst.toNat ∨ dst.toNat + n ≤ a) → c.σ.mem[a]? = m0[a]?) ∧
  c.tick < 2 ∧ (∀ R : Register, NotWrittenB R → c.σ.regs.get? R = g R)

/-- `ret` transition (`0x5c → r`): from `StBDone` to the described-update
postcondition. Requires `r` 4-aligned (so `ret`'s bit-0 clear is a no-op). -/
theorem tr_retB (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (StBDone g r dst src n m0 bs) (memcpy_bytepath_post g r dst n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha4, ha7, hra, ⟨vmi, hmi⟩, htick, hreg, hminv, hframe⟩ := hSt
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006c5c c.σ c.tick c.steps (0x80006c5c#64) vmi r hgood hpc hmi hra hloaded rfl htgt htick
  have hpc' : σ'.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs, ret_tgt r halign]
  have ha0' := obs_jr_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have hra' := obs_jr_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG', hpc', ha0', hra', ?_, ?_, hi',
    fun R hR => (frame_jr_b hobs R hR).trans (hframe R hR)⟩
  · -- copied bytes present: mem unchanged by ret (regs-only), so σ'.mem = c.σ.mem
    intro k hk; rw [hmem']; exact hminv.copied k hk
  · intro a ha; rw [hmem']; exact hminv.outside a ha

/-! ## The byte-copy-path total-correctness spec

Entry precondition at `0x80006c40` (the byte-copy path the binary takes when the
alignment fast-path does not apply), `n > 0`. The machine runs (finitely many
architectural steps, tick parity unconstrained) to `r` with `x10 = dst`,
`GoodState`, and the memory holding the described update: the `n` source bytes
copied into `[dst, dst+n)`, everything else untouched. -/
theorem memcpy_bytepath_spec (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (halign : r.toNat % 4 = 0) :
    Triple (PreB g r dst src n m0 bs) (memcpy_bytepath_post g r dst n m0 bs) :=
  ((prefixB g r dst src n m0 bs).seq
    ((fun c hc => loop_to_doneB g r dst src n m0 bs c (Or.inl hc)) : Triple (AtHeadB g r dst src n m0 bs) (StBDone g r dst src n m0 bs))).seq
    (tr_retB g r dst src n m0 bs halign)

end Vsa.Sim
