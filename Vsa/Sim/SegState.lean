import Vsa.Sim.RegPins
import Vsa.Sim.SnprintfSpec18

/-!
# `SegState` — a generic segment-state record over `RegPins`

Every Layer-3 segment so far defines a bespoke 12–16-field `structure`
(`StMv`/`StMvF0`/`PreMv`/`PreSp`/…) holding the same five "harness" facts —
`GoodState`, the PC pin, the tracked-register pins, minstret existence, the
tick bound — plus a per-segment payload (code-`Loaded`, memory invariants,
region ghosts, the register blanket frame).  `SegSt` collapses the harness
into ONE generic record parameterized by

* `pcv` — the program counter this state sits at,
* `L : List Pin` — the tracked registers, in `RegPins` list form, and
* `P : MState → Prop` — the segment payload (absorbs `Loaded`, memory
  invariants, ghost regions, and the `g`-frame; anything that is a function
  of the machine state alone).

The six transport lemmas `segst_alu` / `segst_store` / `segst_btaken` /
`segst_bnottaken` / `segst_jr` / `segst_jal` carry a `SegSt` across one
step-observation (`ReadsLikePost σ' (sigmaPost_* …)`), rebuilding the harness
automatically (PC via `obs_*_pc`, minstret via `obs_*_minstret`); the caller
supplies

* the new PC as an equation (`by decide` for `pc+4`, the usual
  `BitVec.eq_of_toNat_eq; decide` for branch targets),
* the new pin list with a proof it holds — typically
  `pins_* hobs (by rfl) h.pins`, with a cons for the written `rd`
  (`obs_alu_rd`/`obs_jal_rd`), and
* the payload transfer `P c.σ → P' σ'` — one lambda combining the step's
  memory equation with the per-class `frame_*` blanket lemma.

## Verdict (honest)

The record composes cleanly and DOES reduce ceremony, but not to nothing:

* **Eliminated per step** (vs the `Spec18`-style ceremony): the ~5–8
  `obs_*_other … (by decide)×8` register-transport lines (already replaced by
  `RegPins`, now threaded through the record), the explicit `hpc'` rewrite
  block (`have := obs_*_pc …; rwa [show BitVec.addInt … from by decide]`),
  and the `obs_*_minstret` bookkeeping.  A branch/store/jump step becomes a
  site call + one `segst_*` call (2 `have`s); an ALU step adds one line for
  the `rd` value fact when a new pin is wanted.  In `tr_setup_mv` terms:
  ~10 lines/step down to ~4–5 lines/step.
* **Not eliminated**: the site-lemma invocation itself (its argument list is
  the irreducible content of a step), the per-step
  `obtain ⟨vmi, hmi⟩ := h.minstret` (site lemmas want the minstret *value*),
  value-normalization rewrites (`li31_val`, `ptr_succ`, …), and the payload
  transfer lambda (1–3 lines, replacing the old per-field `by rw [hmem…]`
  re-proofs and the `hframe` chain at the end of a segment — a wash on lines
  but done incrementally instead of in one n-step `rw [e7, e6, …]` block).
* **Positional pin extraction** (`h.pins.2.2.1`) replaces named fields
  (`hSt.a3`) — slightly less readable, same length.  Where a segment's states
  are used across files, the bespoke named record is still nicer as the
  *published* interface; `SegSt` pays off *inside* a segment proof for the
  step-to-step ceremony, and the bridge lemmas (`segst_of_stMvF0` below)
  show the two forms interconvert for free.

The worked `example` at the bottom re-derives the first two steps of
`tr_setup_mv` (`0x800069f0` li / `0x800069f4` bltu-not-taken) from an
`StMvF0`-equivalent `SegSt` state to demonstrate the intended usage.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.Sim.Code (MemmoveLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-- Generic segment state: the machine sits at `pcv` with the tracked pins
`L`, the standard harness facts, and the segment payload `P` (Loaded
predicates, memory invariants, region ghosts, register blanket frames —
anything that is a function of `c.σ` alone). -/
structure SegSt (pcv : BitVec 64) (L : List Pin) (P : MState → Prop) (c : Config) : Prop where
  good : GoodState c.σ
  pcAt : c.σ.regs.get? Register.PC = some pcv
  pins : PinsHold c.σ L
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  extra : P c.σ

/-! ## Structural helpers -/

/-- Pins for a sublist still hold (drop stale pins, e.g. before the register
is overwritten, or thin the list at a segment boundary). -/
theorem pinsHold_sublist {σ : MState} {L' L : List Pin}
    (hs : List.Sublist L' L) (h : PinsHold σ L) : PinsHold σ L' := by
  induction hs with
  | slnil => trivial
  | cons _ _ ih => exact ih h.2
  | cons₂ _ _ ih => exact ⟨h.1, ih h.2⟩

/-- Extend a pin list with a freshly-written register (the `rd` of an
ALU/JAL step, from `obs_alu_rd`/`obs_jal_rd`).  A determined application —
use this rather than an anonymous `⟨_, _⟩`, whose expected `PinsHold` type
is still a metavariable while the transport lemma's `L'` is being solved. -/
theorem pins_cons {σ : MState} {R : Register} {v : RegisterType R} {L : List Pin}
    (h1 : σ.regs.get? R = some v) (h : PinsHold σ L) :
    PinsHold σ (⟨R, v⟩ :: L) := ⟨h1, h⟩

/-- Weaken a `SegSt` in place: thin the pin list, weaken the payload. -/
theorem SegSt.weaken {pcv : BitVec 64} {L L' : List Pin} {P P' : MState → Prop} {c : Config}
    (h : SegSt pcv L P c) (hsub : List.Sublist L' L) (hP : P c.σ → P' c.σ) :
    SegSt pcv L' P' c :=
  ⟨h.good, h.pcAt, pinsHold_sublist hsub h.pins, h.minstret, h.tick, hP h.extra⟩

/-! ## Transport lemmas — one per instruction class

Shape: from `SegSt pcv L P c` plus the step observation produced by a site
lemma (`hobs`, `hG'`, `hi'`), rebuild `SegSt pc' L' P' ⟨σ', i', u⟩`.  The PC
equation, the new pin list (with proof), and the payload transfer are the
caller's three inputs; `good`/`minstret`/`tick` are automatic. -/

/-- ALU step (`sigmaPost_alu`): `PC := pcv+4`, `rd` written. -/
theorem segst_alu {pcv : BitVec 64} {L : List Pin} {P : MState → Prop} {c : Config}
    {σ' : MState} {vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (h : SegSt pcv L P c)
    (hobs : ReadsLikePost σ' (sigmaPost_alu c.σ pcv vm rd v))
    (hG' : GoodState σ') {i' : Nat} (hi' : i' < 2)
    {pc' : BitVec 64} (hpc' : BitVec.addInt pcv 4 = pc')
    {L' : List Pin} (hpins' : PinsHold σ' L')
    {P' : MState → Prop} (hP' : P c.σ → P' σ') (u : Nat) :
    SegSt pc' L' P' ⟨σ', i', u⟩ :=
  ⟨hG', by rw [← hpc']; exact obs_alu_pc hobs, hpins',
   obs_alu_minstret hobs, hi', hP' h.extra⟩

/-- Store step (`sigmaPost_store`): `PC := pcv+4`, memory written (the
payload transfer carries the memory update). -/
theorem segst_store {pcv : BitVec 64} {L : List Pin} {P : MState → Prop} {c : Config}
    {σ' : MState} {vm : BitVec 64} {m' : Std.ExtHashMap Nat (BitVec 8)}
    (h : SegSt pcv L P c)
    (hobs : ReadsLikePost σ' (sigmaPost_store c.σ pcv vm m'))
    (hG' : GoodState σ') {i' : Nat} (hi' : i' < 2)
    {pc' : BitVec 64} (hpc' : BitVec.addInt pcv 4 = pc')
    {L' : List Pin} (hpins' : PinsHold σ' L')
    {P' : MState → Prop} (hP' : P c.σ → P' σ') (u : Nat) :
    SegSt pc' L' P' ⟨σ', i', u⟩ :=
  ⟨hG', by rw [← hpc']; exact obs_store_pc hobs, hpins',
   obs_store_minstret hobs, hi', hP' h.extra⟩

/-- Taken branch (`sigmaPost_branch_taken`): `PC := pcv + sext imm`. -/
theorem segst_btaken {pcv : BitVec 64} {L : List Pin} {P : MState → Prop} {c : Config}
    {σ' : MState} {vm : BitVec 64} {imm : BitVec 13}
    (h : SegSt pcv L P c)
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken c.σ pcv vm imm))
    (hG' : GoodState σ') {i' : Nat} (hi' : i' < 2)
    {pc' : BitVec 64} (hpc' : pcv + sign_extend (m := 64) imm = pc')
    {L' : List Pin} (hpins' : PinsHold σ' L')
    {P' : MState → Prop} (hP' : P c.σ → P' σ') (u : Nat) :
    SegSt pc' L' P' ⟨σ', i', u⟩ :=
  ⟨hG', by rw [← hpc']; exact obs_btaken_pc hobs, hpins',
   obs_btaken_minstret hobs, hi', hP' h.extra⟩

/-- Not-taken branch (`sigmaPost_branch_nottaken`): `PC := pcv+4`. -/
theorem segst_bnottaken {pcv : BitVec 64} {L : List Pin} {P : MState → Prop} {c : Config}
    {σ' : MState} {vm : BitVec 64}
    (h : SegSt pcv L P c)
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken c.σ pcv vm))
    (hG' : GoodState σ') {i' : Nat} (hi' : i' < 2)
    {pc' : BitVec 64} (hpc' : BitVec.addInt pcv 4 = pc')
    {L' : List Pin} (hpins' : PinsHold σ' L')
    {P' : MState → Prop} (hP' : P c.σ → P' σ') (u : Nat) :
    SegSt pc' L' P' ⟨σ', i', u⟩ :=
  ⟨hG', by rw [← hpc']; exact obs_bnottaken_pc hobs, hpins',
   obs_bnottaken_minstret hobs, hi', hP' h.extra⟩

/-- Register-indirect jump with `rd = x0` (`jr`/`ret`/`j`): `PC := tgt`. -/
theorem segst_jr {pcv : BitVec 64} {L : List Pin} {P : MState → Prop} {c : Config}
    {σ' : MState} {vm tgt : BitVec 64}
    (h : SegSt pcv L P c)
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 c.σ pcv vm tgt))
    (hG' : GoodState σ') {i' : Nat} (hi' : i' < 2)
    {pc' : BitVec 64} (hpc' : tgt = pc')
    {L' : List Pin} (hpins' : PinsHold σ' L')
    {P' : MState → Prop} (hP' : P c.σ → P' σ') (u : Nat) :
    SegSt pc' L' P' ⟨σ', i', u⟩ :=
  ⟨hG', by rw [← hpc']; exact obs_jr_pc hobs, hpins',
   obs_jr_minstret hobs, hi', hP' h.extra⟩

/-- Linking jump (`sigmaPost_jal`): `PC := pcv + sext imm`, `rd_reg := link`. -/
theorem segst_jal {pcv : BitVec 64} {L : List Pin} {P : MState → Prop} {c : Config}
    {σ' : MState} {vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (h : SegSt pcv L P c)
    (hobs : ReadsLikePost σ' (sigmaPost_jal c.σ pcv vm imm rd_reg link))
    (hG' : GoodState σ') {i' : Nat} (hi' : i' < 2)
    {pc' : BitVec 64} (hpc' : pcv + sign_extend (m := 64) imm = pc')
    {L' : List Pin} (hpins' : PinsHold σ' L')
    {P' : MState → Prop} (hP' : P c.σ → P' σ') (u : Nat) :
    SegSt pc' L' P' ⟨σ', i', u⟩ :=
  ⟨hG', by rw [← hpc']; exact obs_jal_pc hobs, hpins',
   obs_jal_minstret hobs, hi', hP' h.extra⟩

/-! ## Bridge: a bespoke segment record is a `SegSt` (demo on `StMvF0`)

The `memmove` mid-dispatch state `StMvF0` (SnprintfSpec18) in `SegSt` form:
pins = `a0/a1/a2/ra`, payload = code-Loaded + `mem = m0` + the `g`-frame.
The pure ghosts (`MvRegions`, `MvBytes`) do not depend on `c` and stay
outside the record, as hypotheses of the segment lemma. -/

/-- The `StMvF0` payload as a `SegSt` payload. -/
abbrev MvF0Extra (g : (R : Register) → Option (RegisterType R))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (σ : MState) : Prop :=
  MemmoveLoaded σ.mem ∧ σ.mem = m0 ∧
    ∀ R : Register, NotWrittenMv R → σ.regs.get? R = g R

/-- Construction: `StMvF0 → SegSt` (the harness fields transfer 1-1; the
payload is the remaining conjunction). -/
theorem segst_of_stMvF0 (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) (h : StMvF0 g r dst src n m0 bs c) :
    SegSt (0x800069f0#64)
      [⟨Register.x10, dst⟩, ⟨Register.x11, src⟩, ⟨Register.x12, BitVec.ofNat 64 n⟩,
       ⟨Register.x1, r⟩]
      (MvF0Extra g m0) c :=
  ⟨h.good, h.pc, ⟨h.a0, h.a1, h.a2, h.ra, trivial⟩, h.minstret, h.tick,
   ⟨h.loaded, h.memeq, h.hframe⟩⟩

/-- Destruction: `SegSt → StMvF0` (given the pure ghosts). -/
theorem stMvF0_of_segst (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config)
    (hreg : MvRegions dst src n) (hbs : MvBytes m0 src n bs)
    (h : SegSt (0x800069f0#64)
      [⟨Register.x10, dst⟩, ⟨Register.x11, src⟩, ⟨Register.x12, BitVec.ofNat 64 n⟩,
       ⟨Register.x1, r⟩]
      (MvF0Extra g m0) c) : StMvF0 g r dst src n m0 bs c :=
  ⟨h.good, h.extra.1, h.pcAt, h.pins.1, h.pins.2.1, h.pins.2.2.1, h.pins.2.2.2.1,
   h.minstret, h.tick, hreg, hbs, h.extra.2.1, h.extra.2.2⟩

/-! ## Worked example — the first two steps of `tr_setup_mv` in `SegSt` style

`0x800069f0: li a5,31` (ALU, new pin for `a5`) then
`0x800069f4: bltu a5,a2` NOT taken (`n ≤ 31`, pins unchanged).
Compare `tr_setup_mv` (SnprintfSpec18): the same two steps take ~25 lines of
per-register/PC/minstret ceremony there; here each step is the site call plus
one `segst_*` transport (the ALU step pays one extra line to normalize the
written `rd` value). -/

example (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (n : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (hn1 : 1 ≤ n) (hn31 : n ≤ 31) (c : Config)
    (h : SegSt (0x800069f0#64)
      [⟨Register.x10, dst⟩, ⟨Register.x11, src⟩, ⟨Register.x12, BitVec.ofNat 64 n⟩,
       ⟨Register.x1, r⟩]
      (MvF0Extra g m0) c) :
    ∃ c', Steps c c' ∧
      SegSt (0x800069f8#64)
        [⟨Register.x15, (0x1f#64 : BitVec 64)⟩, ⟨Register.x10, dst⟩, ⟨Register.x11, src⟩,
         ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x1, r⟩]
        (MvF0Extra g m0) c' := by
  have hntn : (BitVec.ofNat 64 n : BitVec 64).toNat = n :=
    BitVec.toNat_ofNat _ _ ▸ Nat.mod_eq_of_lt (by omega)
  -- === 0x800069f0: li a5,31 ===
  obtain ⟨vmi, hmi⟩ := h.minstret
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_69f0 c.σ c.tick c.steps (0x800069f0#64) vmi h.good h.pcAt hmi h.extra.1 rfl h.tick
  have ha5_1 : σ1.regs.get? Register.x15 = some (0x1f#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [li31_val] at this
  have h1 : SegSt (0x800069f4#64)
      [⟨Register.x15, (0x1f#64 : BitVec 64)⟩, ⟨Register.x10, dst⟩, ⟨Register.x11, src⟩,
       ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x1, r⟩]
      (MvF0Extra g m0) ⟨σ1, i1, c.steps + 1⟩ :=
    segst_alu h hobs1 hG1 hi1 (by decide)
      (pins_cons ha5_1 (pins_alu hobs1 (by rfl) h.pins))
      (fun hp => ⟨by rw [hmem1]; exact hp.1, by rw [hmem1]; exact hp.2.1,
        fun R hR => (frame_alu_mv hobs1 R hR.x15 hR).trans (hp.2.2 R hR)⟩)
      (c.steps + 1)
  -- === 0x800069f4: bltu a5,a2 → NOT taken (n ≤ 31) ===
  obtain ⟨vmi1, hmi1⟩ := h1.minstret
  have hv1 : zopz0zI_u (0x1f#64) (BitVec.ofNat 64 n) = false :=
    bltu_false_of_ge (0x1f#64) (BitVec.ofNat 64 n)
      (by rw [hntn, show (0x1f#64 : BitVec 64).toNat = 31 from by decide]; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_69f4_nottaken σ1 i1 (c.steps + 1) (0x800069f4#64) vmi1 (BitVec.ofNat 64 n)
      h1.good h1.pcAt hmi1 h1.pins.1 h1.pins.2.2.2.1 h1.extra.1 rfl hv1 h1.tick
  have h2 : SegSt (0x800069f8#64)
      [⟨Register.x15, (0x1f#64 : BitVec 64)⟩, ⟨Register.x10, dst⟩, ⟨Register.x11, src⟩,
       ⟨Register.x12, BitVec.ofNat 64 n⟩, ⟨Register.x1, r⟩]
      (MvF0Extra g m0) ⟨σ2, i2, c.steps + 1 + 1⟩ :=
    segst_bnottaken h1 hobs2 hG2 hi2 (by decide)
      (pins_bnottaken hobs2 (by rfl) h1.pins)
      (fun hp => ⟨by rw [hmem2]; exact hp.1, by rw [hmem2]; exact hp.2.1,
        fun R hR => (frame_bnottaken_mv hobs2 R hR).trans (hp.2.2 R hR)⟩)
      (c.steps + 1 + 1)
  exact ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2), h2⟩

end Vsa.Sim
