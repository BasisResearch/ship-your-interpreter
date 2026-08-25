import Vsa.Sim.RegPins

/-!
# `KeepRegs` — value-free register-preservation transport

The post-widening companion to `RegPins`: a spec exports
`KeepRegs Rs c.σ c'.σ` for a *concrete* register list `Rs` disjoint from the
segment's write-set, and any caller holding `c.σ.regs.get? R = some w` for
`R ∈ Rs` transports it across the whole segment.  Unlike a `PinsHold` bundle
the list carries **no values**, so the statement needs no extra binders and the
side conditions close by `decide` (everything is concrete registers).

Threading cost inside a proof: one `keep_*` line per site (mirroring the
`pins_*` classes), or one `keep_of_frame` per callee/loop with a `NotWritten*`
register frame.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- Every register in `Rs` still reads in `σ'` whatever it read in `σ0`. -/
def KeepRegs (Rs : List Register) (σ0 σ' : MState) : Prop :=
  ∀ R ∈ Rs, ∀ w : RegisterType R, σ0.regs.get? R = some w → σ'.regs.get? R = some w

/-- Register-list avoidance (the value-free `pinsAvoid`). -/
def avoidsK (S Rs : List Register) : Bool :=
  Rs.all fun R => S.all fun r => !(r == R)

theorem avoidsK_single {S Rs : List Register} {R : Register} (w : RegisterType R)
    (h : avoidsK S Rs = true) (hR : R ∈ Rs) :
    pinsAvoid S [(⟨R, w⟩ : Pin)] = true := by
  simp only [pinsAvoid, List.all_cons, List.all_nil, Bool.and_true]
  exact List.all_eq_true.mp h R hR

theorem keep_rfl (Rs : List Register) (σ : MState) : KeepRegs Rs σ σ :=
  fun _ _ _ hw => hw

theorem keep_trans {Rs : List Register} {σ0 σ1 σ2 : MState}
    (h1 : KeepRegs Rs σ0 σ1) (h2 : KeepRegs Rs σ1 σ2) : KeepRegs Rs σ0 σ2 :=
  fun R hR w hw => h2 R hR w (h1 R hR w hw)

/-- Shrink the tracked list (`Rs' ⊆ Rs`, dischargeable by `decide`). -/
theorem keep_sub {Rs' Rs : List Register} {σ0 σ' : MState}
    (hsub : ∀ R ∈ Rs', R ∈ Rs) (h : KeepRegs Rs σ0 σ') : KeepRegs Rs' σ0 σ' :=
  fun R hR w hw => h R (hsub R hR) w hw

/-- ALU step (writes `rd` + noise). -/
theorem keep_alu {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) {Rs : List Register}
    (hav : avoidsK (rd :: noiseRegs) Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (pins_alu hobs (avoidsK_single w hav hR) (⟨h R hR w hw, trivial⟩ :
      PinsHold σ [(⟨R, w⟩ : Pin)])).1

/-- Store step (memory + noise only). -/
theorem keep_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) {Rs : List Register}
    (hav : avoidsK noiseRegs Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (pins_store hobs (avoidsK_single w hav hR) (⟨h R hR w hw, trivial⟩ :
      PinsHold σ [(⟨R, w⟩ : Pin)])).1

/-- Taken branch. -/
theorem keep_btaken {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) {Rs : List Register}
    (hav : avoidsK noiseRegs Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (pins_btaken hobs (avoidsK_single w hav hR) (⟨h R hR w hw, trivial⟩ :
      PinsHold σ [(⟨R, w⟩ : Pin)])).1

/-- Not-taken branch. -/
theorem keep_bnottaken {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) {Rs : List Register}
    (hav : avoidsK noiseRegs Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (pins_bnottaken hobs (avoidsK_single w hav hR) (⟨h R hR w hw, trivial⟩ :
      PinsHold σ [(⟨R, w⟩ : Pin)])).1

/-- `jr`/`j`/`ret` (jump with `rd = x0`). -/
theorem keep_jr {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) {Rs : List Register}
    (hav : avoidsK noiseRegs Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (pins_jr hobs (avoidsK_single w hav hR) (⟨h R hR w hw, trivial⟩ :
      PinsHold σ [(⟨R, w⟩ : Pin)])).1

/-- Linking jump (`jal`, writes `rd_reg` + noise). -/
theorem keep_jal {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) {Rs : List Register}
    (hav : avoidsK (rd_reg :: noiseRegs) Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (pins_jal hobs (avoidsK_single w hav hR) (⟨h R hR w hw, trivial⟩ :
      PinsHold σ [(⟨R, w⟩ : Pin)])).1

/-- Callee/loop hop through a `NotWritten*`-style register frame stated over an
explicit write-set list `W`. -/
theorem keep_of_frame {σ' σ : MState} {W : List Register}
    (hframe : ∀ R : Register, (∀ r ∈ W, (r == R) = false) →
      σ'.regs.get? R = σ.regs.get? R)
    {Rs : List Register} (hav : avoidsK W Rs = true)
    {σ0 : MState} (h : KeepRegs Rs σ0 σ) : KeepRegs Rs σ0 σ' :=
  fun R hR w hw =>
    (hframe R (all_notin (List.all_eq_true.mp hav R hR))).trans (h R hR w hw)

/-- The five mid-registers the flush path (`PreSr` + `svfprintf_flushReturn`)
consumes at `0x8000e908`: `gp`, `s1` (= the locale pointer), and the
callee-saved `s2/s3/s5`. -/
abbrev midRegs5 : List Register :=
  [Register.x3, Register.x9, Register.x18, Register.x19, Register.x21]

end Vsa.Sim
