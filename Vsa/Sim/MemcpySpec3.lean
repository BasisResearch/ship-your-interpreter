import Vsa.Sim.MemcpySpec2
import Vsa.Sim.MemcpySites3
import Vsa.Sim.DivSpec
import Vsa.Triple

/-!
# Layer 3 — `memcpy` small-word-loop rule, epilogue, dispatch, and unified spec

Builds on `Vsa/Sim/MemcpySpec2.lean` (the word-loop body `iterW`, `StW`/`StW18`,
`meminv_store8`, the pointer identities) and `Vsa/Sim/MemcpySites2.lean` (the
per-site steps for the small word loop `[0x80006bfc, 0x80006c38]`).

## Task 1: the word-loop rule

The small word loop copies `p` full words (`8p ≤ n`, `p > 0` and small enough to
avoid the unrolled ×8 path).  Control flow:

* `c04 : bgeu a4,a2` — entry guard.  `a4 = dst`, `a2 = dst + 8p`.  Not-taken
  (`dst <u dst+8p`, i.e. `p > 0`) falls to the loop head `c08`; taken skips the
  loop entirely (`p = 0`).
* `c08 … c14` — one iteration (`iterW`, `c08 → c18`).
* `c18 : bltu a5,a2` — back-edge.  `a5 = dst + 8(j+1)`, `a2 = dst + 8p`.  Taken
  (`8(j+1) < 8p`, i.e. `j+1 < p`) loops back to `c08`; not-taken (`j+1 = p`)
  falls through to the epilogue at `c1c` with `MemInv … (8p)`.

Encoded for `Triple.loop` (DivLoops bottom-tested pattern): a PC-guarded measure
`LoopMuW = a2.toNat - a5.toNat` (= `8(p-j)` at the head, `0` elsewhere), invariant
`LoopIW = AtHeadW ∨ AtDoneW`, guard `LoopBW = AtHeadW`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Word-path branch frame helpers (over `NotWrittenW`) -/

/-- Generic taken-branch frame step for the word path (no `rd`). -/
theorem frame_btaken_w {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) (R : Register)
    (hR : NotWrittenW R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_taken σ pc vm imm R hmi hpc hnpc hmii

/-- Generic not-taken-branch frame step for the word path. -/
theorem frame_bnottaken_w {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) (R : Register)
    (hR : NotWrittenW R) : σ'.regs.get? R = σ.regs.get? R := by
  obtain ⟨_, _, _, hpc, hnpc, hmi, hmii, hmc, hmt, hmip⟩ := hR
  rw [hobs.1 R hmc hmt hmip]
  exact get?_sigmaPost_branch_nottaken σ pc vm R hmi hpc hnpc hmii

/-! ## Word-loop epilogue-entry state (`StWDone`, at `0x80006c1c`)

When the word loop exits (`c18` not-taken, `j+1 = p`), the machine is at `c1c`
with all `p` words copied (`MemInv … (8p)`) and the pointers at their loop-final
values: `a2 = dst + 8p`, `a4 = dst`, `a5 = dst + 8p`, `a3 = src + 8p`.  The `a1`
still holds `src` (the small word loop never touches `a1`). -/
structure StWDone (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c1c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8 * p))
  a4 : c.σ.regs.get? Register.x14 = some dst
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  dst_align : dst.toNat % 8 = 0
  src_align : src.toNat % 8 = 0
  ple : 8 * p ≤ n
  meminv : MemInv dst src n bs (8 * p) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenW R → c.σ.regs.get? R = g R

/-! ## The `bltu a5,a2` back-edge (`0x80006c18`)

`a5 = dst + 8(j+1)`, `a2 = dst + 8p`.  Taken iff `dst+8(j+1) <u dst+8p` iff
`j+1 < p` (no wrap); loops back to `c08` iteration `j+1`.  Not-taken iff
`j+1 = p`; falls through to `c1c` with `MemInv … (8p)`. -/

/-- `bltu a5,a2` value guard, taken: `j+1 < p` ⇒ `<u` is true. -/
theorem bltu_word_true {src : BitVec 64} (dst : BitVec 64) (n p j : Nat) (hreg : Regions dst src n)
    (hp : 8 * p ≤ n) (hlt : j + 1 < p) :
    zopz0zI_u (dst + BitVec.ofNat 64 (8 * (j + 1))) (dst + BitVec.ofNat 64 (8 * p)) = true := by
  have h1 : (dst + BitVec.ofNat 64 (8 * (j + 1))).toNat = dst.toNat + 8 * (j + 1) :=
    ptr_toNat dst (8 * (j + 1)) (by have := hreg.dst_nowrap; omega)
  have h2 : (dst + BitVec.ofNat 64 (8 * p)).toNat = dst.toNat + 8 * p :=
    ptr_toNat dst (8 * p) (by have := hreg.dst_nowrap; omega)
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [decide_eq_true_iff]
  apply Int.ofNat_lt.mpr
  rw [h1, h2]; omega

/-- `bltu a5,a2` value guard, not-taken: `j+1 = p` ⇒ `<u` is false (`a5 = a2`). -/
theorem bltu_word_false (dst : BitVec 64) (p j : Nat) (heq : j + 1 = p) :
    zopz0zI_u (dst + BitVec.ofNat 64 (8 * (j + 1))) (dst + BitVec.ofNat 64 (8 * p)) = false := by
  rw [heq]
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [decide_eq_false_iff_not]
  exact fun h => absurd (Int.ofNat_lt.mp h) (Nat.lt_irrefl _)

/-- `bltu a5,a2` taken (`0x80006c18 → 0x80006c08`): loop back to iteration `j+1`. -/
theorem tr_bltu_back (g : (R : Register) → Option (RegisterType R)) (p j : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (hlt : j + 1 < p) (hp : 8 * p ≤ n) :
    Triple (StW18 g p j r dst src n m0 bs) (StW g p (j + 1) r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha5, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hjlt, hminv, hframe⟩ := hSt
  have hv : zopz0zI_u (dst + BitVec.ofNat 64 (8 * (j + 1))) (dst + BitVec.ofNat 64 (8 * p)) = true :=
    bltu_word_true dst n p j hreg hp hlt
  have htgt : ((0x80006c18#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006c18_taken c.σ c.tick c.steps (0x80006c18#64) vmi
      (dst + BitVec.ofNat 64 (8 * (j + 1))) (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha5 ha2 hloaded rfl htgt hv htick
  have hpceq : (0x80006c18#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13) = (0x80006c08#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
    obs_btaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_btaken_other hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5,
    obs_btaken_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, hda, hsa, by omega, by rw [hmem']; exact hminv,
    fun R hR => (frame_btaken_w hobs R hR).trans (hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- `bltu a5,a2` not-taken (`0x80006c18 → 0x80006c1c`, `j+1 = p`): exit to the
epilogue with the full `p`-word update. -/
theorem tr_bltu_done (g : (R : Register) → Option (RegisterType R)) (p j : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (heq : j + 1 = p) :
    Triple (StW18 g p j r dst src n m0 bs) (StWDone g p r dst src n m0 bs) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha5, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hjlt, hminv, hframe⟩ := hSt
  have hv : zopz0zI_u (dst + BitVec.ofNat 64 (8 * (j + 1))) (dst + BitVec.ofNat 64 (8 * p)) = false :=
    bltu_word_false dst p j heq
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006c18_nottaken c.σ c.tick c.steps (0x80006c18#64) vmi
      (dst + BitVec.ofNat 64 (8 * (j + 1))) (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha5 ha2 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006c1c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006c18#64) 4 = (0x80006c1c#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, hpc',
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2,
    obs_bnottaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_bnottaken_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, hda, hsa, by omega, ?_,
    fun R hR => (frame_bnottaken_w hobs R hR).trans (hframe R hR)⟩
  -- MemInv … (8p) from MemInv … (8(j+1)) via j+1 = p
  rw [hmem']
  exact heq ▸ hminv

/-! ## Loop invariant, guard, measure (`Triple.loop`, DivLoops PC-guarded pattern) -/

/-- At the loop head `c08`, some iteration `j < p`, with the full-loop bound
`8p ≤ n` carried (`StW`'s `jlt` only bounds the current word). -/
def AtHeadW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  8 * p ≤ n ∧ ∃ j, j < p ∧ StW g p j r dst src n m0 bs c

def LoopIW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadW g p r dst src n m0 bs c ∨ StWDone g p r dst src n m0 bs c

/-- Loop guard: at the head (`AtHeadW`, which already implies `j < p`). -/
def LoopBW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadW g p r dst src n m0 bs c

/-- Loop measure: `a2.toNat - a5.toNat` **at the loop head `c08`**, else `0`.  The
PC guard keeps it well-defined off the head (DivLoops pattern). -/
def LoopMuW (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006c08#64)
  then ((c.σ.regs.get? Register.x12).getD (0#64)).toNat - ((c.σ.regs.get? Register.x15).getD (0#64)).toNat
  else 0

/-- At loop head iteration `j` (`8p ≤ n`, `j ≤ p`), `LoopMuW = 8(p - j)`. -/
theorem loopmu_headW (g : (R : Register) → Option (RegisterType R)) (p j : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config)
    (hSt : StW g p j r dst src n m0 bs c) (hpn : 8 * p ≤ n) (hjp : j ≤ p) :
    LoopMuW c = 8 * (p - j) := by
  simp only [LoopMuW, hSt.pc, hSt.a2, hSt.a5, Option.getD_some, if_pos]
  have h2 : (dst + BitVec.ofNat 64 (8 * p)).toNat = dst.toNat + 8 * p :=
    ptr_toNat dst (8 * p) (by have := hSt.regions.dst_nowrap; omega)
  have h5 : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j :=
    ptr_toNat dst (8 * j) (by have := hSt.regions.dst_nowrap; omega)
  rw [h2, h5]; omega

/-- **Word-loop body**: one full iteration (`iterW` then `bltu`) re-establishes
`LoopIW`, strictly decreasing `LoopMuW`. -/
theorem loop_bodyW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (mmeas : Nat) :
    Triple (fun c => LoopIW g p r dst src n m0 bs c ∧ LoopBW g p r dst src n m0 bs c ∧ LoopMuW c = mmeas)
           (fun c => LoopIW g p r dst src n m0 bs c ∧ LoopMuW c < mmeas) := by
  intro c hc
  obtain ⟨_, ⟨hpn, j, hjlt, hSt⟩, hmu⟩ := hc
  have hmu_eq : LoopMuW c = 8 * (p - j) := loopmu_headW g p j r dst src n m0 bs c hSt hpn (Nat.le_of_lt hjlt)
  rw [hmu_eq] at hmu
  -- one iteration to c18
  obtain ⟨c1, hs1, hSt18⟩ := iterW g p j r dst src n m0 bs c hSt
  by_cases hdone : j + 1 = p
  · -- exit: bltu not taken → StWDone
    obtain ⟨c2, hs2, hDone⟩ := tr_bltu_done g p j r dst src n m0 bs hdone c1 hSt18
    refine ⟨c2, hs1.trans hs2, Or.inr hDone, ?_⟩
    -- LoopMuW c2 = 0 (not at c08) < mmeas (= 8(p-j) = 8 > 0)
    have hmu2 : LoopMuW c2 = 0 := by
      simp only [LoopMuW, hDone.pc]
      rw [if_neg (by intro h; injection h with h; exact absurd h (by decide))]
    rw [hmu2, ← hmu]; omega
  · -- loop back: bltu taken → AtHeadW (j+1)
    have hlt2 : j + 1 < p := by omega
    obtain ⟨c2, hs2, hSt2⟩ := tr_bltu_back g p j r dst src n m0 bs hlt2 hpn c1 hSt18
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨hpn, j + 1, hlt2, hSt2⟩, ?_⟩
    have hmu2 : LoopMuW c2 = 8 * (p - (j + 1)) := loopmu_headW g p (j+1) r dst src n m0 bs c2 hSt2 hpn (Nat.le_of_lt hlt2)
    rw [hmu2, ← hmu]; omega

/-- The word loop runs from `LoopIW` to `StWDone` (`c1c`, all `p` words copied).
`Triple.loop` reaches `LoopIW ∧ ¬LoopBW`; `¬LoopBW = ¬AtHeadW`, so only `StWDone`
remains. -/
theorem loop_to_doneW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (LoopIW g p r dst src n m0 bs) (StWDone g p r dst src n m0 bs) := by
  have hloop := Triple.loop (I := LoopIW g p r dst src n m0 bs) (B := LoopBW g p r dst src n m0 bs)
    LoopMuW (loop_bodyW g p r dst src n m0 bs)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hDone⟩

/-! ## The `c04` bgeu entry into the word loop

`bgeu a4,a2` at `c04` with `a4 = dst`, `a2 = dst + 8p`, `a3 = src`, `a5 = dst`.
For `p > 0` the branch is not-taken (`dst <u dst+8p`), falling to the loop head
`c08` at iteration `0` (`AtHeadW`).  `MemInv … 0` (nothing copied yet). -/

/-- Entry precondition at `c04` (word-loop entry, `p > 0`, `8p ≤ n`). -/
structure PreW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : MemcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006c04#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8 * p))
  a3 : c.σ.regs.get? Register.x13 = some src
  a4 : c.σ.regs.get? Register.x14 = some dst
  a5 : c.σ.regs.get? Register.x15 = some dst
  a7 : c.σ.regs.get? Register.x17 = some (dst + BitVec.ofNat 64 n)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : Regions dst src n
  dst_align : dst.toNat % 8 = 0
  src_align : src.toNat % 8 = 0
  ppos : 0 < p
  ple : 8 * p ≤ n
  meminv : MemInv dst src n bs 0 m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenW R → c.σ.regs.get? R = g R

/-- `bgeu a4,a2` not-taken value: `dst <u dst+8p` (`p > 0`, no wrap) ⇒ `≥u` is false. -/
theorem bgeu_word_false (dst : BitVec 64) (n p : Nat) (hnw : dst.toNat + n < 2^64)
    (hp : 8 * p ≤ n) (hpos : 0 < p) :
    zopz0zKzJ_u dst (dst + BitVec.ofNat 64 (8 * p)) = false := by
  have hval : (dst + BitVec.ofNat 64 (8 * p)).toNat = dst.toNat + 8 * p := ptr_toNat dst (8 * p) (by omega)
  unfold zopz0zKzJ_u Sail.BitVec.toNatInt
  rw [decide_eq_false_iff_not]
  intro h
  have := Int.ofNat_le.mp h
  rw [hval] at this; omega

/-- Word-loop entry `c04 → c08`: establishes `AtHeadW` at iteration `0`. -/
theorem entryW (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreW g p r dst src n m0 bs) (LoopIW g p r dst src n m0 bs) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha5, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hpos, hpn, hminv, hframe⟩ := hPre
  have hv : zopz0zKzJ_u dst (dst + BitVec.ofNat 64 (8 * p)) = false :=
    bgeu_word_false dst n p hreg.dst_nowrap hpn hpos
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006c04_nottaken c.σ c.tick c.steps (0x80006c04#64) vmi dst (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha4 ha2 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006c08#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006c04#64) 4 = (0x80006c08#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, (Steps.single hstep), Or.inl ⟨hpn, 0, hpos, ?_⟩⟩
  refine ⟨hG', by rw [hmem']; exact hloaded, hpc',
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2,
    ?_, ?_, ?_, ?_,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, hda, hsa, by omega, ?_,
    fun R hR => (frame_bnottaken_w hobs R hR).trans (hframe R hR)⟩
  · -- a3 = src = src + 8*0
    have := obs_bnottaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
    rwa [show src = src + BitVec.ofNat 64 (8 * 0) from by rw [show (BitVec.ofNat 64 (8 * 0) : BitVec 64) = 0#64 from rfl, BitVec.add_zero]] at this
  · exact obs_bnottaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  · -- a5 = dst = dst + 8*0
    have := obs_bnottaken_other hobs Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5
    rwa [show dst = dst + BitVec.ofNat 64 (8 * 0) from by rw [show (BitVec.ofNat 64 (8 * 0) : BitVec 64) = 0#64 from rfl, BitVec.add_zero]] at this
  · exact obs_bnottaken_other hobs Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7
  · -- MemInv at 8*0 = 0
    rw [hmem']; exact (show (8 * 0 : Nat) = 0 from rfl) ▸ hminv

/-- Word-loop entry through to the epilogue: `c04 → c1c`, all `p` words copied. -/
theorem word_loop_spec (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreW g p r dst src n m0 bs) (StWDone g p r dst src n m0 bs) :=
  (entryW g p r dst src n m0 bs).seq (loop_to_doneW g p r dst src n m0 bs)

/-! ## Task 2: the word-loop epilogue (`0x80006c1c … 0x80006c38`)

Straight-line pointer recomputation, then `bltu a4,a7` at `c38`.  From `StWDone`
(`a2 = dst+8p`, `a4 = dst`, `a1 = src`), the seven ALU steps compute (using
`dst%8 = 0`, `p ≥ 1`):

* `a2 := (((dst+8p) - 1) - dst) & ~7 = 8(p-1)`  (`epilogue_a2`, `mask_low3`);
* `a1 := (src + 8) + 8(p-1) = src + 8p`;
* `a4 := (dst + 8) + 8(p-1) = dst + 8p`.

`c38 : bltu a4,a7` then tests `dst+8p <u dst+n`: taken (`8p < n`, tail bytes remain)
enters the byte loop at `c48` with the byte-loop head state `StB` at iteration
`8p`; not-taken (`8p = n`, whole copy word-aligned) rets at `c3c` (the ret site
there is a documented follow-up — see the return note).

The byte loop uses the `NotWrittenB` frame predicate, disjoint from the word
loop's `NotWrittenW` (the epilogue writes `x11, x12, x14`, and `x12 ∉ NotWrittenB`).
So the epilogue instantiates a **fresh** byte-loop ghost `g' := c'.σ.regs.get?`
(making the byte-loop `hframe` trivially `rfl` at entry) — the DivLoops
callee-ghost-at-call-site pattern.  The original `g` connection is not needed
inside the byte path (whose own post re-exposes every untouched register). -/

/-- The number `2^64 - 8` as a `BitVec 64`: clearing low 3 bits.  Nat mask fact
`x &&& (2^64 - 8) = x/8*8` proved bitwise (`Nat.eq_of_testBit_eq`). -/
theorem mask_low3 (x : Nat) (hx : x < 2^64) : x &&& (2^64 - 8) = x / 8 * 8 := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have hmask : (2:Nat)^64 - 8 = (2^61 - 1) * 2^3 := by decide
  have h88 : (8:Nat) = 2^3 := by decide
  rw [hmask, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one, h88,
    Nat.testBit_mul_two_pow, Nat.testBit_div_two_pow]
  by_cases hi : 3 ≤ i
  · have h2 : i - 3 + 3 = i := by omega
    rw [h2]
    by_cases hib : i < 64
    · have hlt : i - 3 < 61 := by omega
      simp only [hi, decide_true, Bool.true_and, hlt, Bool.and_true]
    · have hxb : x.testBit i = false := by
        apply Nat.testBit_lt_two_pow
        exact Nat.lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) (by omega))
      simp only [hxb, Bool.false_and, Bool.and_false]
  · simp only [hi, decide_false, Bool.false_and, Bool.and_false]

/-- The `c1c;c20;c24` result: `a2 = (((dst+8p) - 1) - dst) & ~7 = ofNat (8(p-1))`. -/
theorem epilogue_a2 (dst : BitVec 64) (p : Nat) (hp : 1 ≤ p) (hb : dst.toNat + 8 * p < 2^64) :
    (((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) - dst) &&& sign_extend (m := 64) (0xff8#12)
      = BitVec.ofNat 64 (8 * (p - 1)) := by
  have hstep1 : ((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) - dst
      = BitVec.ofNat 64 (8 * p) + (-1#64) := by
    have hs : (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -1#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs]
    generalize BitVec.ofNat 64 (8 * p) = w
    have h : dst + w + (-1#64) = (w + (-1#64)) + dst := by
      rw [BitVec.add_assoc dst w (-1#64), BitVec.add_comm dst (w + (-1#64))]
    rw [h, BitVec.add_sub_cancel]
  rw [hstep1]
  have hmask : (sign_extend (m := 64) (0xff8#12) : BitVec 64) = BitVec.ofNat 64 (2^64 - 8) := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hmask]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  have hm1 : ((-1#64 : BitVec 64)).toNat = 2^64 - 1 := by decide
  rw [hm1]
  have e8p : (8 * p) % 2^64 = 8 * p := Nat.mod_eq_of_lt (by omega)
  have emask : (2^64 - 8) % 2^64 = 2^64 - 8 := Nat.mod_eq_of_lt (by omega)
  rw [e8p, emask]
  have hsum : (8 * p + (2^64 - 1)) % 2^64 = 8 * p - 1 := by omega
  rw [hsum, mask_low3 (8 * p - 1) (by omega)]
  have hdm : (8 * p - 1) / 8 * 8 = 8 * (p - 1) := by omega
  rw [hdm]
  exact (Nat.mod_eq_of_lt (by omega)).symm

/-- The `+8` then `+8(p-1)` pointer chain: `(base + 8) + ofNat (8(p-1)) = base + ofNat (8p)`. -/
theorem epilogue_ptr (base : BitVec 64) (p : Nat) (hp : 1 ≤ p) :
    (base + sign_extend (m := 64) (0x008#12)) + BitVec.ofNat 64 (8 * (p - 1))
      = base + BitVec.ofNat 64 (8 * p) := by
  have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [hs, BitVec.add_assoc]
  congr 1
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  omega

/-- `bltu a4,a7` at `c38`, taken: `a4 = dst+8p`, `a7 = dst+n`, `8p < n` ⇒ `<u` true. -/
theorem bltu_tail_true (dst : BitVec 64) (n p : Nat) (hnw : dst.toNat + n < 2^64)
    (hlt : 8 * p < n) :
    zopz0zI_u (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n) = true := by
  have h1 : (dst + BitVec.ofNat 64 (8 * p)).toNat = dst.toNat + 8 * p := ptr_toNat dst (8 * p) (by omega)
  have h2 : (dst + BitVec.ofNat 64 n).toNat = dst.toNat + n := ptr_toNat dst n (by omega)
  unfold zopz0zI_u Sail.BitVec.toNatInt
  rw [decide_eq_true_iff]
  apply Int.ofNat_lt.mpr
  rw [h1, h2]; omega

/-- The byte-loop entry state reached by the epilogue when a tail remains
(`8p < n`): exactly `StB` at iteration `8p` (byte loop head `c48`), with a fresh
ghost `g'`.  This is the interface into `MemcpySpec.loop_to_doneB`. -/
theorem epilogue_to_bytehead (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (hpos : 1 ≤ p) (htail : 8 * p < n) :
    Triple (fun c => StWDone g p r dst src n m0 bs c)
      (fun c => ∃ g', StB g' (0x80006c48#64) (8 * p) r dst src n m0 bs c) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha4, ha7, hra, ⟨vmi, hmi⟩, htick,
    hreg, hda, hsa, hple, hminv, _⟩ := hSt
  have hnw := hreg.dst_nowrap
  -- === c1c: addi a2,a2,-1 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006c1c c.σ c.tick c.steps (0x80006c1c#64) vmi (dst + BitVec.ofNat 64 (8 * p))
      hgood hpc hmi ha2 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006c20#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006c1c#64) 4 = (0x80006c20#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have ha4_1 := obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have ha7_1 := obs_alu_other hobs1 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha2_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === c20: sub a2,a2,a4 ===  (a4 = dst)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006c20 σ1 i1 (c.steps + 1) (0x80006c20#64) vmi1
      ((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) dst
      hG1 hpc1 hmi1' ha2_1 ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006c24#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006c20#64) 4 = (0x80006c24#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha4_2 := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have ha7_2 := obs_alu_other hobs2 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha2_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === c24: andi a2,a2,-8 ===
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006c24 σ2 i2 (c.steps + 1 + 1) (0x80006c24#64) vmi2
      (((dst + BitVec.ofNat 64 (8 * p)) + sign_extend (m := 64) (0xfff#12)) - dst)
      hG2 hpc2 hmi2' ha2_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006c28#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006c24#64) 4 = (0x80006c28#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha4_3 := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_2
  have ha7_3 := obs_alu_other hobs3 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have ha2_3 : σ3.regs.get? Register.x12 = some (BitVec.ofNat 64 (8 * (p - 1))) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_a2 dst p (by omega) (by omega)] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === c28: addi a1,a1,8 ===  (a1 = src)
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006c28 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006c28#64) vmi3 src
      hG3 hpc3 hmi3' ha1_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006c2c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006c28#64) 4 = (0x80006c2c#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha4_4 := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_3
  have ha7_4 := obs_alu_other hobs4 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have ha2_4 := obs_alu_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_3
  have ha1_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === c2c: addi a4,a4,8 ===  (a4 = dst)
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006c2c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006c2c#64) vmi4 dst
      hG4 hpc4 hmi4' ha4_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006c30#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006c2c#64) 4 = (0x80006c30#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have ha7_5 := obs_alu_other hobs5 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_4
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have ha2_5 := obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_4
  have ha4_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === c30: add a1,a1,a2 ===  (a1 = src+8, a2 = ofNat(8(p-1)))
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006c30 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006c30#64) vmi5
      (src + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG5 hpc5 hmi5' ha1_5 ha2_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006c34#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006c30#64) 4 = (0x80006c34#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have ha7_6 := obs_alu_other hobs6 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_5
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have ha2_6 := obs_alu_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_5
  have ha4_6 := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_5
  have ha1_6 : σ6.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_ptr src p (by omega)] at this
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  -- === c34: add a4,a4,a2 ===  (a4 = dst+8, a2 = ofNat(8(p-1)))
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006c34 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c34#64) vmi6
      (dst + sign_extend (m := 64) (0x008#12)) (BitVec.ofNat 64 (8 * (p - 1)))
      hG6 hpc6 hmi6' ha4_6 ha2_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006c38#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006c34#64) 4 = (0x80006c38#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have ha1_7 := obs_alu_other hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_6
  have ha7_7 := obs_alu_other hobs7 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_6
  have hra_7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have ha4_7 : σ7.regs.get? Register.x14 = some (dst + BitVec.ofNat 64 (8 * p)) := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [epilogue_ptr dst p (by omega)] at this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  -- memory unchanged across the 7 regs-only steps
  have hmem7eq : σ7.mem = c.σ.mem := by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  -- === c38: bltu a4,a7 taken (8p < n) → c48 ===
  have hv : zopz0zI_u (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n) = true :=
    bltu_tail_true dst n p hnw htail
  have htgt : ((0x80006c38#64 : BitVec 64) + sign_extend (m := 64) (0x0010#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006c38_taken σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006c38#64) vmi7
      (dst + BitVec.ofNat 64 (8 * p)) (dst + BitVec.ofNat 64 n)
      hG7 hpc7 hmi7' ha4_7 ha7_7 (by rw [hmem7eq]; exact hloaded) rfl htgt hv hi7
  have hpceq : (0x80006c38#64 : BitVec 64) + sign_extend (m := 64) (0x0010#13) = (0x80006c48#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006c48#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs8, hpceq]
  have hsteps : Steps c ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    (((((((Steps.single (by cases c; exact hs1)).trans (Steps.single hs2)).trans
      (Steps.single hs3)).trans (Steps.single hs4)).trans (Steps.single hs5)).trans
      (Steps.single hs6)).trans (Steps.single hs7)).trans (Steps.single hs8)
  refine ⟨⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    fun R => σ8.regs.get? R, ?_⟩
  -- StB (fresh ghost) at i = 8p
  refine ⟨hG8, by rw [hmem8, hmem7eq]; exact hloaded, hpc8,
    obs_btaken_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7,
    obs_btaken_other hobs8 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_7,
    obs_btaken_other hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_7,
    obs_btaken_other hobs8 Register.x17 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha7_7,
    ?_, obs_btaken_minstret hobs8, hi8, hreg, by omega, ?_, fun R _ => rfl⟩
  · -- x1 = r : preserved through all 7 ALU steps + branch
    exact obs_btaken_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7
  · -- MemInv at 8p
    rw [hmem8, hmem7eq]; exact hminv

/-- **Epilogue tail composition**: from `StWDone` (word loop done, `1 ≤ p`) with a
non-empty byte tail (`8p < n`), the epilogue enters the byte loop and copies the
remaining `n - 8p` bytes, reaching `memcpy_bytepath_post` (`x10 = dst`, PC back at
`r`, and the full described update `∀ k < n, mem[dst+k] = bs k`).  The byte-loop
ghost is fresh (`∃ g'`), since the epilogue rewrites the frame across the
`NotWrittenW → NotWrittenB` boundary; `memcpy_bytepath_post`'s own frame conjunct
re-exposes every register the byte path leaves untouched.  Requires `r` 4-aligned
(for the `ret`). -/
theorem epilogue_tail_spec (g : (R : Register) → Option (RegisterType R)) (p : Nat) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (hpos : 1 ≤ p) (htail : 8 * p < n) (halign : r.toNat % 4 = 0) :
    Triple (fun c => StWDone g p r dst src n m0 bs c)
      (fun c => ∃ g', memcpy_bytepath_post g' r dst n m0 bs c) := by
  refine (epilogue_to_bytehead g p r dst src n m0 bs hpos htail).seq ?_
  intro c hc
  obtain ⟨g', hStB⟩ := hc
  -- run the byte loop from the head at i = 8p to StBDone, then ret
  have hhead : Triple (StB g' (0x80006c48#64) (8 * p) r dst src n m0 bs)
      (StBDone g' r dst src n m0 bs) :=
    fun c hc => loop_to_doneB g' r dst src n m0 bs c (Or.inl ⟨8 * p, htail, hc⟩)
  have hbyte : Triple (StB g' (0x80006c48#64) (8 * p) r dst src n m0 bs)
      (memcpy_bytepath_post g' r dst n m0 bs) :=
    hhead.seq (tr_retB g' r dst src n m0 bs halign)
  obtain ⟨c', hs', hpost⟩ := hbyte c hStB
  exact ⟨c', hs', g', hpost⟩

end Vsa.Sim
