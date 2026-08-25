import Vsa.Sim.Muldi3Spec
import Vsa.Sim.MemcpySpec
import Vsa.Sim.DivSites2

/-!
# `RegPins` — list-driven register-frame transport

Every Layer-3 composition currently threads each tracked register through each
step by hand: one `obs_*_other … (by decide) ×8` line per register per site
(O(sites × registers) `have`s — the single largest boilerplate term in the spec
files).  This file collapses that to **one line per site**: bundle the tracked
registers as a `List Pin`, and transport the whole bundle with `pins_alu` /
`pins_store` / `pins_btaken` / `pins_bnottaken` / `pins_jr` / `pins_jal`.

Usage pattern inside a composition:

```lean
-- entry: pins from the precondition
have hp0 : PinsHold c.σ [⟨Register.x10, dst⟩, ⟨Register.x1, r⟩, ⟨Register.x2, vsp⟩] :=
  ⟨ha0, hra, hsp⟩
-- after an ALU step writing rd (rd ∉ pins):
have hp1 := pins_alu hobs1 (by rfl) hp0
-- after a store / branch / jr:
have hp2 := pins_store hobs2 (by rfl) hp1
-- extract when needed (positional):
-- hp2.1 : σ2.regs.get? Register.x10 = some dst
-- hp2.2.1 : σ2.regs.get? Register.x1 = some r
```

The `by rfl` closes the side condition `pinsAvoid S L = true` (`S` = the
step's write-set: `rd :: noiseRegs` for ALU/JAL, `noiseRegs` for the rest);
it reduces by kernel evaluation because only the *registers* of the pins are
inspected, never the (symbolic) values.  NB it must be `rfl`, not `decide`:
the pin list contains free variables (the values), which `decide` rejects
even though they are never consulted.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- One tracked register pin: a register and the value it must read. -/
abbrev Pin := (R : Register) × RegisterType R

/-- All pins hold in `σ`. -/
def PinsHold (σ : MState) : List Pin → Prop
  | [] => True
  | p :: rest => σ.regs.get? p.1 = some p.2 ∧ PinsHold σ rest

@[simp] theorem pinsHold_nil (σ : MState) : PinsHold σ [] := trivial

@[simp] theorem pinsHold_cons (σ : MState) (p : Pin) (L : List Pin) :
    PinsHold σ (p :: L) ↔ (σ.regs.get? p.1 = some p.2 ∧ PinsHold σ L) := Iff.rfl

/-- The per-step noise write-set common to every instruction class. -/
def noiseRegs : List Register :=
  [Register.minstret, Register.PC, Register.nextPC, Register.minstret_increment,
   Register.mcycle, Register.mtime, Register.mip]

/-- Every register in `S` differs from every pinned register.  Bool-valued and
kernel-reducible for concrete lists (pin *values* are never inspected). -/
def pinsAvoid (S : List Register) (L : List Pin) : Bool :=
  L.all fun p => S.all fun r => !(r == p.1)

theorem all_notin {S : List Register} {R : Register}
    (h : (S.all fun r => !(r == R)) = true) : ∀ r ∈ S, (r == R) = false := by
  intro r hr
  have := List.all_eq_true.mp h r hr
  simpa using this

theorem pinsAvoid_cons {S : List Register} {p : Pin} {L : List Pin}
    (h : pinsAvoid S (p :: L) = true) :
    (∀ r ∈ S, (r == p.1) = false) ∧ pinsAvoid S L = true := by
  have h' := h
  simp only [pinsAvoid, List.all_cons, Bool.and_eq_true] at h'
  exact ⟨all_notin h'.1, h'.2⟩

/-- ALU step (`sigmaPost_alu`, writes `rd` + noise): transport all pins. -/
theorem pins_alu {σ' σ : MState} {pc vm : BitVec 64} {rd : Register} {v : RegisterType rd}
    (hobs : ReadsLikePost σ' (sigmaPost_alu σ pc vm rd v)) {L : List Pin}
    (hav : pinsAvoid (rd :: noiseRegs) L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_alu_other hobs p.1
      (hn Register.mcycle (List.mem_cons_of_mem rd (by decide)))
      (hn Register.mtime (List.mem_cons_of_mem rd (by decide)))
      (hn Register.mip (List.mem_cons_of_mem rd (by decide)))
      (hn Register.minstret (List.mem_cons_of_mem rd (by decide)))
      (hn Register.PC (List.mem_cons_of_mem rd (by decide)))
      (hn rd (List.mem_cons_self ..))
      (hn Register.nextPC (List.mem_cons_of_mem rd (by decide)))
      (hn Register.minstret_increment (List.mem_cons_of_mem rd (by decide)))
      h.1, ih hrest h.2⟩

/-- Store step (`sigmaPost_store`, writes memory + noise only). -/
theorem pins_store {σ' σ : MState} {pc vm : BitVec 64}
    {m' : Std.ExtHashMap Nat (BitVec 8)}
    (hobs : ReadsLikePost σ' (sigmaPost_store σ pc vm m')) {L : List Pin}
    (hav : pinsAvoid noiseRegs L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_store_other hobs p.1
      (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
      (hn Register.mip (by decide)) (hn Register.minstret (by decide))
      (hn Register.PC (by decide)) (hn Register.nextPC (by decide))
      (hn Register.minstret_increment (by decide))
      h.1, ih hrest h.2⟩

/-- Taken branch (`sigmaPost_branch_taken`). -/
theorem pins_btaken {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 13}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_taken σ pc vm imm)) {L : List Pin}
    (hav : pinsAvoid noiseRegs L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_btaken_other hobs p.1
      (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
      (hn Register.mip (by decide)) (hn Register.minstret (by decide))
      (hn Register.PC (by decide)) (hn Register.nextPC (by decide))
      (hn Register.minstret_increment (by decide))
      h.1, ih hrest h.2⟩

/-- Not-taken branch (`sigmaPost_branch_nottaken`). -/
theorem pins_bnottaken {σ' σ : MState} {pc vm : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_branch_nottaken σ pc vm)) {L : List Pin}
    (hav : pinsAvoid noiseRegs L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_bnottaken_other hobs p.1
      (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
      (hn Register.mip (by decide)) (hn Register.minstret (by decide))
      (hn Register.PC (by decide)) (hn Register.nextPC (by decide))
      (hn Register.minstret_increment (by decide))
      h.1, ih hrest h.2⟩

/-- Register-indirect jump with `rd = x0` (`sigmaPost_jump_x0`: `jr`/`ret`/`j`). -/
theorem pins_jr {σ' σ : MState} {pc vm tgt : BitVec 64}
    (hobs : ReadsLikePost σ' (sigmaPost_jump_x0 σ pc vm tgt)) {L : List Pin}
    (hav : pinsAvoid noiseRegs L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_jr_other hobs p.1
      (hn Register.mcycle (by decide)) (hn Register.mtime (by decide))
      (hn Register.mip (by decide)) (hn Register.minstret (by decide))
      (hn Register.PC (by decide)) (hn Register.nextPC (by decide))
      (hn Register.minstret_increment (by decide))
      h.1, ih hrest h.2⟩

/-- Callee-frame transport (the call-composition template): pins whose
registers avoid the callee's write-set `W` survive the *whole call*, given the
callee spec's register frame in list form.  Instantiate the callee's `g` with
the call-time registers so its frame reads `σ'.regs.get? R = σ.regs.get? R`,
convert its `NotWrittenX` tuple to the list form once per callee (an 11-way
`⟨h _ (by decide), …⟩` adapter), and one `pins_of_frame` call replaces the
per-register recovery after `memmove`/`__ssputs_r`/… calls. -/
theorem pins_of_frame {σ' σ : MState} {W : List Register}
    (hframe : ∀ R : Register, (∀ r ∈ W, (r == R) = false) →
      σ'.regs.get? R = σ.regs.get? R)
    {L : List Pin} (hav : pinsAvoid W L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨(hframe p.1 hn).trans h.1, ih hrest h.2⟩

/-- Linking jump (`sigmaPost_jal`, writes `rd_reg` + noise). -/
theorem pins_jal {σ' σ : MState} {pc vm : BitVec 64} {imm : BitVec 21}
    {rd_reg : Register} {link : RegisterType rd_reg}
    (hobs : ReadsLikePost σ' (sigmaPost_jal σ pc vm imm rd_reg link)) {L : List Pin}
    (hav : pinsAvoid (rd_reg :: noiseRegs) L = true)
    (h : PinsHold σ L) : PinsHold σ' L := by
  induction L with
  | nil => trivial
  | cons p rest ih =>
    obtain ⟨hn, hrest⟩ := pinsAvoid_cons hav
    exact ⟨obs_jal_other hobs p.1
      (hn Register.mcycle (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.mtime (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.mip (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.minstret (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.PC (List.mem_cons_of_mem rd_reg (by decide)))
      (hn rd_reg (List.mem_cons_self ..))
      (hn Register.nextPC (List.mem_cons_of_mem rd_reg (by decide)))
      (hn Register.minstret_increment (List.mem_cons_of_mem rd_reg (by decide)))
      h.1, ih hrest h.2⟩

end Vsa.Sim
