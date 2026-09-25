import VsaIris.LocalRunO
import VsaIris.Vsa.SymRun
import VsaIris.Vsa.Console

/-!
# Symbolic runs that print (lane N1)

A printing run is an `SWP` (`SymRun.lean`) whose end condition is a printing
run (`LRO`, `LocalRunO.lean`) from the end values: `SWP … (LRO … Q t) pc R Mt`.
Every silent step lemma (`swp_step`, the generated step tables) applies to it
unchanged. At `tohost` putchar stores `swp_putc` prints one character and
continues with the console advanced: the goal's end condition becomes
`LRO … Q (t ++ c)`. `swpo_run` reads the whole run back as an `LRO` from any
matching concrete values, which `wp_lroW` consumes.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Iris

variable {live : Nat → Prop} {text : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- A printing run's symbolic goal: the silent run to any state from which
the printing run continues with the console at `t`. -/
abbrev SWPO (live : Nat → Prop) (text : List (Nat × BitVec 8)) (rs : List Nat) (S : Nat → Prop)
    (Q : String → (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) (t : String) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SWP live text rs S (LRO (vsaModel live) roR text rs S Q t)

/-- **Reading a printing run back.** Every concrete state matching the
symbolic one runs. -/
theorem swpo_run {t : String} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : SWPO live text rs S Q t pc R Mt) {rv : Nat → BitVec 64} {mv : Nat → BitVec 8}
    (hm : Matches rs S pc R Mt rv mv) : LRO (vsaModel live) roR text rs S Q t rv mv := by
  obtain ⟨n, hn⟩ := h
  exact lro_of_localRun n rv mv (hn rv mv hm)

/-- **The run is done.** -/
theorem swpo_done {t : String} {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ rv mv, Matches rs S pc R Mt rv mv → Q t rv mv) : SWPO live text rs S Q t pc R Mt :=
  swp_done fun rv mv hm => LRO.done (h rv mv hm)

/-- **One putchar store.** At a `tohost` site with the base and the putchar
word for `c` in its registers, the store prints `c`; the run continues after
it with the console at `t ++ c`. -/
theorem swp_putc (T : TohostSite) (hT : T.Cert) (c : BitVec 8) {t : String}
    {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ text, live p.1) (hcode : ∀ p ∈ codeFoot T.pc T.code, (p.1, p.2.2) ∈ text)
    (hPC : VsaIris.PC ∈ rs) (h1 : T.rs1 ∈ rs) (h2 : T.rs2 ∈ rs)
    (hne1 : T.rs1 ≠ VsaIris.PC) (hne2 : T.rs2 ≠ VsaIris.PC)
    (hpc : pc = BitVec.ofNat 64 T.pc) (hr1 : R T.rs1 = T.base) (hr2 : R T.rs2 = putcWord c)
    (hk : SWPO live text rs S Q (t ++ putcStr c) (BitVec.ofNat 64 (T.pc + 4)) R Mt) :
    SWPO live text rs S Q t pc R Mt := by
  subst hpc
  refine swp_done fun rv mv hm => LRO.seg 0 (segFromO_of_runFactO
    (putc_runFact live T hT c (DFrac.own 1) (DFrac.own 1)
      (fun p hp => hlive _ (hcode p hp))) ?_ ?_ ?_ (fun p hp => by cases hp) ?_)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inr ⟨h1, (hm.regs _ h1 hne1).trans hr1⟩
    · exact .inr ⟨h2, (hm.regs _ h2 hne2).trans hr2⟩
  · exact fun p hp => .inl (hcode p hp)
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    subst hp
    exact .inl ⟨hPC, hm.pc⟩
  · intro rv' mv' hRW hkeep _ hmv
    refine swpo_run hk ⟨hRW _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · refine (hkeep r hr fun p hp e => ?_).trans (hm.regs r hr hne)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      subst hp
      exact hne e.symm
    · exact (hmv a ha fun p hp => by cases hp).trans (hm.img a ha)

end VsaIris.Sym
