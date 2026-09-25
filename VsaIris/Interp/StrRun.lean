import VsaIris.Vsa.SymData
import VsaIris.Vsa.SymObs

/-!
# Symbolic runs of the string leaves (`strlen`, `strcpy`)

`SR live T D S Q pc R Mt` is `SWP` (`VsaIris/Vsa/SymRun.lean`) for a leaf
function that owns NO read-only register: `SWP` pins `gp` read-only
(`roR`), which `strlenSpec`/`strcpySpec` (`fnSpecW`, no `codeRes`) do not
hand over, and neither leaf reads `gp`. The read-only list is live code `T`
followed by persistent data `D` (a C string's bytes, total reads; no
liveness, `SymData.lean`); the owned registers are `sRegs`.

The word loops of both leaves load whole aligned words, so they read up to
seven bytes past a string's NUL that nobody hands them. `sr_havoc` is such a
load: the machine reads whatever the bytes hold, and the continuation holds
for EVERY byte function `f` that agrees with `D`, with the register taking
`val f`. The over-read bytes need no ownership and no liveness, only the
load's RAM/HTIF window (`LdOK`); the bytes the value actually depends on are
those of `D`. This is `swp_havocD` with the loaded value tied to the data.

`sr_seg` (a reflected segment that reads no memory, writes owned bytes) and
`sr_alu` (an observed ALU step, `snez`) are `swp_segLD` and `swp_aluRR`
without the `gp` pin.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast
open Vsa.Machine (Config)
open Iris
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-- The registers a string leaf owns: `PC`, `ra`, `a0`-`a6`. -/
abbrev sRegs : List Nat := [32, 1, 10, 11, 12, 13, 14, 15, 16]

section SR

variable (live : Nat → Prop) (T D : List (Nat × BitVec 8)) (S : Nat → Prop)
  (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop)

/-- **A string leaf's run at a symbolic state**: one fuel bound under which
every matching state runs to `Q`, with no read-only register. -/
def SR (pc : BitVec 64) (R : Nat → BitVec 64) (Mt : Mem) : Prop :=
  ∃ n, ∀ rv mv, Matches sRegs S pc R Mt rv mv →
    LocalRun (vsaModel live) [] (T ++ D) sRegs S Q n rv mv

variable {live T D S Q}

theorem sr_done {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : ∀ rv mv, Matches sRegs S pc R Mt rv mv → Q rv mv) : SR live T D S Q pc R Mt :=
  ⟨0, h⟩

/-- Only the owned registers other than `PC` matter. -/
theorem sr_congr {pc : BitVec 64} {R R' : Nat → BitVec 64} {Mt : Mem}
    (hR : ∀ r ∈ sRegs, r ≠ VsaIris.PC → R' r = R r) (h : SR live T D S Q pc R' Mt) :
    SR live T D S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv ⟨hm.pc, fun r hr hne =>
    (hm.regs r hr hne).trans (hR r hr hne).symm, hm.img⟩⟩

/-- Only the owned bytes of the tracking memory matter. -/
theorem sr_congr_mem {pc : BitVec 64} {R : Nat → BitVec 64} {Mt Mt' : Mem}
    (hM : ∀ a, S a → imgM Mt' a = imgM Mt a) (h : SR live T D S Q pc R Mt') :
    SR live T D S Q pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => hn rv mv ⟨hm.pc, hm.regs, fun a ha => (hm.img a ha).trans (hM a ha).symm⟩⟩

theorem sr_mono {Q' : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}
    (hQ : ∀ rv mv, Q rv mv → Q' rv mv) {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (h : SR live T D S Q pc R Mt) : SR live T D S Q' pc R Mt := by
  obtain ⟨n, hn⟩ := h
  exact ⟨n, fun rv mv hm => LocalRun.mono hQ n rv mv (hn rv mv hm)⟩

theorem pinsOf_mem {ks : List Nat} {R : Nat → BitVec 64} {p : Nat × BitVec 64}
    (hks : ∀ x ∈ ks, x ≠ gp) (hp : p ∈ pinsOf ks R) : p.1 ∈ ks ∧ R p.1 = p.2 := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  exact ⟨hx, by simp [hks x hx]⟩

/-- The text list of a run: code, then data. -/
theorem textLoaded_code {T D : List (Nat × BitVec 8)} {c : Config}
    (hok : VsaOk live c) (hlive : ∀ p ∈ T, live p.1)
    {MR : List (Nat × DFrac × BitVec 8)}
    (hMR : ∀ p ∈ textMRof T ++ MR, (vsaModel live).mem c p.1 = p.2.2) :
    TextLoaded T c.σ.mem := textLoaded_of_foot hok hlive hMR

/-- **One reflected segment that reads no data** (ALU, store, branch, jump,
`ret`). The pins are the registers `ks` read off `R` (all owned; no `gp`),
the written owned bytes `W` are read off the tracking memory, and the
successor is computed from the segment. -/
theorem sr_seg {pc0 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (ks : List Nat) (lds : List (List (BitVec 8)))
    (W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ T, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded T m → ChainFacts m m (pinsOf ks R) lds bs)
    (hks : ∀ x ∈ ks, x ∈ sRegs ∧ x ≠ VsaIris.PC ∧ x ≠ gp)
    (hW : ∀ a ∈ W, S a)
    (hk : SR live T D S Q (evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs)
      (fun r => if r ∈ ks then finReg bs (pinsOf ks R) lds r else R r)
      (writeLog Mt (segOut bs (pinsOf ks R) lds).log)) :
    SR live T D S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  have hgp : ∀ x ∈ ks, x ≠ gp := fun x hx => (hks x hx).2.2
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨k, segFrom_of_runFact
    (seg_runFact live bs (pinsOf ks R) lds pc0 (textMRof T)
      (W.map fun a => (a, imgM Mt a)) k hlen (by rw [hK]; exact hwf) (by rw [hK]; exact hkeys)
      (fun x hx => by rw [hK]; exact hwr x hx) ?_ ?_)
    (fun p hp => by cases hp) ?_ ?_ ?_ ?_⟩⟩
  · intro a ha
    exact hcover a fun hW' => ha _ (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hW') rfl
  · intro c hok hfoot
    obtain ⟨_, hMR, _, _⟩ := hfoot
    exact hfacts c.σ.mem (textLoaded_of_foot (LD := []) hok hlive (by simpa using hMR))
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact .inl (List.mem_append_left _ hq)
  · intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .inl ⟨List.mem_cons_self, hm.pc⟩
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      obtain ⟨h1, h2⟩ := pinsOf_mem hgp hq
      exact .inl ⟨(hks _ h1).1, (hm.regs _ (hks _ h1).1 (hks _ h1).2.1).trans h2⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hq
    exact ⟨hW a ha, hm.img a (hW a ha)⟩
  · intro rv' mv' h1 h2 h3 h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hkL : r ∈ ks
      · rw [if_pos hkL]
        exact h1 _ (List.mem_cons_of_mem _
          (List.mem_map_of_mem (f := fun p => (p.1, p.2, finReg bs (pinsOf ks R) lds p.1))
            (List.mem_map_of_mem (f := fun k => (k, if k = gp then gpV else R k)) hkL)))
      · rw [if_neg hkL]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        rcases List.mem_cons.mp hp with rfl | hp
        · exact fun e => hne e.symm
        · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
          exact fun e => hkL (e ▸ (pinsOf_mem hgp hq).1)
    · by_cases hw : a ∈ W
      · have := h3 _ (List.mem_map_of_mem
          (f := fun p => (p.1, p.2, ((writeLog (wbase (W.map fun a => (a, imgM Mt a)))
            (segOut bs (pinsOf ks R) lds).log)[p.1]?).getD 0))
          (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hw))
        refine this.trans (writeLog_getD_congr _ _ _ _ ?_)
        obtain ⟨o', ho', hg⟩ := wbase_get (List.mem_map_of_mem (f := fun a => (a, imgM Mt a)) hw)
        show ((wbase (W.map fun a => (a, imgM Mt a)))[a]?).getD 0 = (Mt[a]?).getD 0
        rw [hg]
        obtain ⟨b, _, e⟩ := List.mem_map.mp ho'
        simp only [Prod.mk.injEq] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rw [h4 a ha fun p hp => by
          obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hp
          obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hb
          exact fun e => hw (e ▸ hc)]
        rw [hm.img a ha]
        unfold imgM
        rw [writeLog_out _ _ _ (hcover a hw)]

/-- **One reflected segment, successor named** (`swp_step` without `gp`). -/
theorem sr_step {pc0 pc1 : BitVec 64} {R R' : Nat → BitVec 64} {Mt Mt' : Mem}
    (bs : List BBlock) (ks : List Nat) (lds : List (List (BitVec 8)))
    (W : List Nat) (k : Nat)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ a, a ∉ W → OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ T, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded T m → ChainFacts m m (pinsOf ks R) lds bs)
    (hks : ∀ x ∈ ks, x ∈ sRegs ∧ x ≠ VsaIris.PC ∧ x ≠ gp)
    (hW : ∀ a ∈ W, S a)
    (hpc : evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs = pc1)
    (hR : ∀ x ∈ ks, finReg bs (pinsOf ks R) lds x = R' x)
    (hRo : ∀ x ∈ sRegs, x ≠ VsaIris.PC → x ∉ ks → R' x = R x)
    (hMt : writeLog Mt (segOut bs (pinsOf ks R) lds).log = Mt')
    (hk : SR live T D S Q pc1 R' Mt') :
    SR live T D S Q pc0 R Mt := by
  refine sr_seg bs ks lds W k hlen hwf hkeys hwr hcover hlive hfacts hks hW ?_
  rw [hpc, hMt]
  refine sr_congr (fun r hr hne => ?_) hk
  by_cases hk' : r ∈ ks
  · rw [if_pos hk']
    exact (hR r hk').symm
  · rw [if_neg hk']
    exact hRo r hr hne hk'

/-- A fuel bound uniform over the values a predicate admits. -/
theorem fuel_unif_of {P : Nat → BitVec 64 → Prop} (A : BitVec 64 → Prop)
    (hmono : ∀ n n' v, n ≤ n' → P n v → P n' v)
    (h : ∀ v, A v → ∃ n, P n v) : ∃ n, ∀ v, A v → P n v := by
  classical
  obtain ⟨n, hn⟩ := fuel_unif (P := fun n v => A v → P n v)
    (fun n n' v hle hp ha => hmono n n' v hle (hp ha))
    (fun v => if hv : A v then (h v hv).elim fun n hn => ⟨n, fun _ => hn⟩
      else ⟨0, fun ha => absurd ha hv⟩)
  exact ⟨n, hn⟩

/-- **A load that may read past the bytes anybody hands over** (`swp_havocD`
with the value tied to the data). The segment writes no memory and changes
the owned registers `ks` as the reflection says; the destination `rd` takes
`val f`, where `f` is the machine's byte image, which agrees with the data
`D`. The loaded byte lists are a function `ldsOf` of the image on the
accessed addresses `A`. -/
theorem sr_havoc {pc0 pc1 : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (bs : List BBlock) (ks : List Nat) (rd : Nat) (A : List Nat)
    (ldsOf : (Nat → BitVec 8) → List (List (BitVec 8))) (val : (Nat → BitVec 8) → BitVec 64)
    (k : Nat)
    (hdep : ∀ f g : Nat → BitVec 8, (∀ a ∈ A, f a = g a) → ldsOf f = ldsOf g)
    (hlen : evalBlocksFuel bs = k + 1) (hwf : ChainOK pc0 ks bs)
    (hkeys : KeysOK ks) (hwr : ∀ x ∈ wrChain bs, x ∈ ks)
    (hcover : ∀ lds a, OutL (segOut bs (pinsOf ks R) lds).log a)
    (hlive : ∀ p ∈ T, live p.1)
    (hfacts : ∀ m : Mem, TextLoaded T m → ChainFacts m m (pinsOf ks R) (ldsOf (imgM m)) bs)
    (hrd : rd ∈ ks)
    (hks : ∀ x ∈ ks, x ∈ sRegs ∧ x ≠ VsaIris.PC ∧ x ≠ gp)
    (hpc : ∀ lds, evalBlocksPC pc0 (SegEvalState.init (pinsOf ks R) lds) bs = pc1)
    (hR : ∀ lds, ∀ x ∈ ks, x ≠ rd → finReg bs (pinsOf ks R) lds x = R x)
    (hval : ∀ f, finReg bs (pinsOf ks R) (ldsOf f) rd = val f)
    (hk : ∀ f : Nat → BitVec 8, (∀ p ∈ D, f p.1 = p.2) →
      SR live T D S Q pc1 (upd R rd (val f)) Mt) :
    SR live T D S Q pc0 R Mt := by
  have hK := keysG_pinsOf R ks
  have hgp : ∀ x ∈ ks, x ≠ gp := fun x hx => (hks x hx).2.2
  obtain ⟨n, hn⟩ := fuel_unif_of (P := fun n v => ∀ rv mv, Matches sRegs S pc1 (upd R rd v) Mt rv mv →
      LocalRun (vsaModel live) [] (T ++ D) sRegs S Q n rv mv)
    (fun v => ∃ f : Nat → BitVec 8, (∀ p ∈ D, f p.1 = p.2) ∧ val f = v)
    (fun _ _ _ hle h rv mv hm => LocalRun.fuel_mono hle (h rv mv hm))
    (fun v ⟨f, hf, hv⟩ => by subst hv; exact hk f hf)
  refine ⟨n + 1, fun rv mv hm => .inr ⟨k, fun σ hok hro hrs hS => ?_⟩⟩
  let f : Nat → BitVec 8 := imgM σ.σ.mem
  have hfD : ∀ p ∈ D, f p.1 = p.2 := fun p hp => hro.2 p (List.mem_append_right _ hp)
  let X : List (Nat × BitVec 8) := A.map fun a => (a, f a)
  have hseg : SegFrom (vsaModel live) [] ((T ++ D) ++ X) sRegs S k rv mv
      (LocalRun (vsaModel live) [] (T ++ D) sRegs S Q n) := by
    refine segFrom_of_runFact (seg_runFact live bs (pinsOf ks R) (ldsOf f) pc0
      (textMRof ((T ++ D) ++ X)) [] k hlen (by rw [hK]; exact hwf) (by rw [hK]; exact hkeys)
      (fun x hx => by rw [hK]; exact hwr x hx) (fun a _ => hcover _ a) ?_) ?_ ?_ ?_ ?_ ?_
    · intro c hok' hfoot
      obtain ⟨_, hMR, _, _⟩ := hfoot
      have hin : ∀ q ∈ (T ++ D) ++ X, (c.σ.mem[q.1]?).getD 0 = q.2 := fun q hq =>
        hMR (q.1, DFrac.discard, q.2) (List.mem_map_of_mem
          (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hq)
      have hT : TextLoaded T c.σ.mem := by
        have h := code_present hok' (textMRof T)
          (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            exact hin p (List.mem_append_left _ (List.mem_append_left _ hp)))
          (fun q hq => by
            obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
            exact hlive p hp)
        intro p hp
        exact h _ (List.mem_map_of_mem (f := fun p : Nat × BitVec 8 => (p.1, DFrac.discard, p.2)) hp)
      have hA : ∀ a ∈ A, imgM c.σ.mem a = f a := fun a ha =>
        hin (a, f a) (List.mem_append_right _ (List.mem_map_of_mem (f := fun a => (a, f a)) ha))
      have := hfacts c.σ.mem hT
      rwa [hdep _ _ hA] at this
    · intro p hp; cases hp
    · intro p hp
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact .inl hq
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact .inl ⟨List.mem_cons_self, hm.pc⟩
      · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
        obtain ⟨h1, h2⟩ := pinsOf_mem hgp hq
        exact .inl ⟨(hks _ h1).1, (hm.regs _ (hks _ h1).1 (hks _ h1).2.1).trans h2⟩
    · intro p hp; cases hp
    · intro rv' mv' h1 h2 _ h4
      refine hn (val f) ⟨f, hfD, rfl⟩ rv' mv' ⟨?_, fun r hr hne => ?_, fun a ha => ?_⟩
      · exact (h1 _ List.mem_cons_self).trans (hpc _)
      · by_cases hkr : r ∈ ks
        · have hr1 := h1 (r, if r = gp then gpV else R r, finReg bs (pinsOf ks R) (ldsOf f) r)
            (List.mem_cons_of_mem _ (List.mem_map_of_mem
              (f := fun p => (p.1, p.2, finReg bs (pinsOf ks R) (ldsOf f) p.1))
              (List.mem_map_of_mem (f := fun k => (k, if k = gp then gpV else R k)) hkr)))
          refine hr1.trans ?_
          by_cases hrr : r = rd
          · subst hrr; rw [upd_same, hval]
          · rw [upd_other _ _ hrr, hR _ r hkr hrr]
        · have hrr : r ≠ rd := fun e => hkr (e ▸ hrd)
          rw [upd_other _ _ hrr]
          refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
          rcases List.mem_cons.mp hp with rfl | hp
          · exact fun e => hne e.symm
          · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
            exact fun e => hkr (e ▸ (pinsOf_mem hgp hq).1)
      · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]
  refine hseg σ hok ⟨hro.1, fun p hp => ?_⟩ hrs hS
  rcases List.mem_append.mp hp with hp | hp
  · exact hro.2 p hp
  · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
    rfl

/-- **An observed ALU step** (`swp_aluRR` without `gp`): `rd` takes `val`,
the PC advances by four. -/
theorem sr_alu {pc : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem}
    (i : Nat) (code : List (BitVec 8)) (rd : Nat) (ks : List Nat) (val : BitVec 64)
    (hstep : AluStep live i (ks.map fun k => (k, DFrac.own 1, R k)) (codeFoot i code) rd val)
    (hcode : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ T)
    (hrd : rd ∈ sRegs) (hks : ∀ k ∈ ks, k ∈ sRegs ∧ k ≠ VsaIris.PC) (hpc : pc = BitVec.ofNat 64 i)
    (hk : SR live T D S Q (BitVec.ofNat 64 (i + 4)) (upd R rd val) Mt) :
    SR live T D S Q pc R Mt := by
  subst hpc
  obtain ⟨n, hn⟩ := hk
  refine ⟨n + 1, fun rv mv hm => .inr ⟨0, segFrom_of_runFact (MW := [])
    (runFact_of_aluStep (old := rv rd) hstep) (fun p hp => ?_)
    (fun p hp => .inl (List.mem_append_left _ (hcode p hp))) ?_
    (fun p hp => by cases hp) ?_⟩⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hp
    exact .inr ⟨(hks k hk).1, hm.regs _ (hks k hk).1 (hks k hk).2⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact .inl ⟨List.mem_cons_self, hm.pc⟩
    · exact .inl ⟨hrd, rfl⟩
  · intro rv' mv' h1 h2 _ h4
    refine hn rv' mv' ⟨h1 _ List.mem_cons_self, fun r hr hne => ?_, fun a ha => ?_⟩
    · by_cases hr1 : r = rd
      · subst hr1
        rw [upd_same]
        exact h1 (r, rv r, val) (by simp)
      · rw [upd_other _ _ hr1]
        refine (h2 r hr fun p hp => ?_).trans (hm.regs r hr hne)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact fun e => hne e.symm
        · exact fun e => hr1 e.symm
    · rw [h4 a ha (fun p hp => by cases hp), hm.img a ha]

end SR

end VsaIris.Sym
