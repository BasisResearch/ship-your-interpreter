import VsaIris.Interp.EnvGetSpans

/-!
# `env_get`, proved (INTERP_DESIGN.md §9 H1)

`envGet_spec : textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ⊢ envGetSpec Wp N`,
for every `MachWP`. The call-free code is the seven spans of
`EnvGetSpans.lean`, each proved first-order by `sx_run`; this file strings
them together at the Iris level:

* the register file is assembled from the ABI entry once
  (`regsOf_entry`) and taken apart at the return (`regsOf_exit`);
* the scan over one frame's names is an induction on the names left, with the
  `strcmp` call taken against `strcmpSpec` (`wp_callW`);
* the walk up the parent chain is a strong induction on the frame address,
  which decreases by `StoreInvariant.parents` (carried by `storeRepr`);
* each frame is opened with the one opener `storeRepr_open` and closed
  unchanged.

The machine's answer is `Store.get?`'s: a frame's scan finds the first
binding named `x` (`FirstMatch`), and the chain's lookup with gas `fa + 1` is
the lookup with any larger gas (`lookup_stable`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.Sym VsaIris.MallocFast
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-! ## The lookup the machine performs -/

/-- `Store.lookup` needs no more gas than the frame address plus one: parents
point to older frames. -/
theorem lookup_stable {st : Store} (hp : StoreParents st) (x : String) :
    ∀ a, a < st.frames.size → ∀ g, a < g → st.lookup g a x = st.lookup (a + 1) a x := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    intro ha g hg
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have hf : st.frames[a]? = some st.frames[a] := Array.getElem?_eq_getElem ha
    simp only [Store.lookup, hf]
    dsimp only [Bind.bind, Option.bind]
    cases hfind : st.frames[a].vars.find? (fun x_1 => x_1.fst == x) with
    | some q => rfl
    | none =>
      cases hpar : st.frames[a].parent with
      | none => rfl
      | some p =>
        have hpa : p < a := hp a ha p hpar
        dsimp only
        have hag : a ≤ g' := by omega
        rw [ih p hpa (Nat.lt_trans hpa ha) g' (Nat.lt_of_lt_of_le hpa hag),
          ih p hpa (Nat.lt_trans hpa ha) a hpa]

/-- The chain answer from frame `a`. -/
def look (st : Store) (a : Addr) (x : String) : Option Value := st.lookup (a + 1) a x

theorem get?_eq_look {st : Store} (hp : StoreParents st) {a : Addr} (ha : a < st.frames.size)
    (x : String) : st.get? a x = look st a x :=
  lookup_stable hp x a ha _ ha

theorem look_hit {st : Store} {a : Addr} {f : Frame} {x : String} {v : Value}
    (hf : st.frames[a]? = some f) (h : FirstMatch f.vars x v) : look st a x = some v := by
  unfold look
  simp [Store.lookup, hf, h.find?_eq_some]

theorem look_root {st : Store} {a : Addr} {f : Frame} {x : String}
    (hf : st.frames[a]? = some f) (h : FrameMiss f.vars x) (hp : f.parent = none) :
    look st a x = none := by
  unfold look
  simp [Store.lookup, hf, h.find?_eq_none, hp]

theorem look_parent {st : Store} (hps : StoreParents st) {a p : Addr} {f : Frame} {x : String}
    (hf : st.frames[a]? = some f) (h : FrameMiss f.vars x) (hp : f.parent = some p) :
    look st a x = look st p x := by
  have ha : a < st.frames.size := by
    rcases Nat.lt_or_ge a st.frames.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hf
  have hfa : st.frames[a] = f := by simpa [Array.getElem?_eq_getElem ha] using hf
  have hpa : p < a := hps a ha p (by rw [hfa]; exact hp)
  unfold look
  simp only [Store.lookup, hf, Option.bind_eq_bind, Option.bind_some, h.find?_eq_none, hp]
  exact lookup_stable hps x p (Nat.lt_trans hpa ha) a hpa

/-! ## Code bytes -/

section Code

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

omit [MachGS hlc GF] in
theorem sepL_of_all {α} (Φ : α → IProp GF) [∀ x, Persistent (Φ x)] :
    ∀ l : List α, (□ ∀ x, ⌜x ∈ l⌝ → Φ x) ⊢ sepL l Φ
  | [] => by iintro _; simp only [sepL_nil]; iempintro
  | y :: ys => by
    rw [sepL_cons]
    iintro #H
    isplitl []
    · iapply H $$ %y %List.mem_cons_self
    · iapply sepL_of_all Φ ys
      imodintro
      iintro %z %hz
      iapply H $$ %z %(List.mem_cons_of_mem _ hz)

/-- A call site's code bytes out of the whole text. -/
theorem instrAt_of_text {text : List (Nat × BitVec 8)} {i : Nat} {code : List (BitVec 8)}
    (h : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ text) :
    textOwn (GF := GF) text ⊢ instrAt i code := by
  unfold textOwn instrAt
  iintro #H
  ihave #Hall := sepL_persist_all (fun p : Nat × BitVec 8 => iprop(p.1 ↦ₘ□ p.2)) text $$ H
  iapply sepL_of_all
  imodintro
  iintro %p %hp
  iapply Hall $$ %(i + p.2, p.1)
    %(h _ (List.mem_map_of_mem (f := fun p : BitVec 8 × Nat => (i + p.2, DFrac.discard, p.1)) hp))

end Code

/-! ## A call to `strcmp` from a span's register file -/

section Call

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

/-- The registers a `strcmp` call touches: `ra`, `a0` and every caller-saved one. -/
def strcmpKs : List Nat := VsaIris.ra :: 10 :: retClob

theorem strcmpKs_nodup : strcmpKs.Nodup := by decide
theorem strcmpKs_sub : ∀ k ∈ strcmpKs, k ∈ gprs := by decide
theorem gprs_nodup : gprs.Nodup := by decide

/-- **`jal strcmp` from a span.** `a0`/`a1` point at the two strings; the
continuation gets the file with `a0` zero exactly on equal strings, `ra` at
the return address, and every register outside `strcmpKs` unchanged. -/
theorem wp_call_strcmp (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    {i : Nat} {code : List (BitVec 8)} (hexec : JalExec (vsaModel live) i code strcmpPC)
    (hi4 : (BitVec.ofNat 64 (i + 4)).toNat % 4 = 0) {R : Nat → BitVec 64} {xi x : String} :
    instrAt i code ∗ strcmpSpec Wp ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 i ∗ regsOf gprs R ∗
      strAt (R 10).toNat xi ∗ strAt (R 11).toNat x ∗
      (∀ R' : Nat → BitVec 64, ⌜(R' 10 = 0#64 ↔ xi = x) ∧ R' 1 = BitVec.ofNat 64 (i + 4) ∧
          ∀ k, k ∉ strcmpKs → R' k = R k⌝ -∗
        VsaIris.PC ↦ᵣ BitVec.ofNat 64 (i + 4) -∗ regsOf gprs R' -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, #Hs, Hpc, HR, #Hxi, #Hx, Hk⟩
  ihave ⟨Hks, Hrest⟩ := regsOf_extract gprs strcmpKs gprs_nodup strcmpKs_nodup strcmpKs_sub R $$ HR
  rw [show strcmpKs = VsaIris.ra :: 10 :: 11 :: 12 :: argClob from rfl, regsOf_cons, regsOf_cons,
    regsOf_cons]
  icases Hks with ⟨Hra, Ha0, Ha1, Hcl⟩
  ihave Hcl := clobbered_of_regsOf _ R $$ Hcl
  unfold strcmpSpec
  ihave Hsp := Hs $$ %(R 10) %(R 11) %xi %x
  iapply wp_callW Wp hexec
  isplitl []
  · iexact Hi
  isplitl []
  · iexact Hsp
  isplitl [Hpc]
  · iexact Hpc
  isplitl [Hra]
  · iexact Hra
  isplitl [Ha0 Ha1 Hcl]
  · iframe Ha0 Ha1 Hcl Hxi Hx
    ipureintro; exact hi4
  iintro Hpc Hra ⟨%res, Ha0, %hres, Hcl⟩
  ihave ⟨%f, Hcl⟩ := regsOf_of_clobbered retClob (by decide) $$ Hcl
  classical
  obtain ⟨R'', hR''⟩ : ∃ R'' : Nat → BitVec 64, R'' = fun k =>
      if k = VsaIris.ra then BitVec.ofNat 64 (i + 4) else if k = 10 then res else f k := ⟨_, rfl⟩
  have e1 : R'' VsaIris.ra = BitVec.ofNat 64 (i + 4) := by simp [hR'']
  have e2 : R'' 10 = res := by simp [hR'', VsaIris.ra]
  have e3 : ∀ k ∈ retClob, R'' k = f k := fun k hk => by
    have h1 : k ≠ VsaIris.ra := by simp [retClob, argClob, VsaIris.ra] at hk ⊢; omega
    have h10 : k ≠ 10 := by simp [retClob, argClob] at hk; omega
    simp [hR'', h1, h10]
  ihave HR := Hrest $$ %R'' [Hra Ha0 Hcl]
  · rw [regsOf_cons, regsOf_cons, e1, e2, show (11 :: 12 :: argClob) = retClob from rfl,
      regsOf_congr e3]
    isplitl [Hra]
    · iexact Hra
    iframe Ha0 Hcl
  have hpure : ((fun k => if k ∈ strcmpKs then R'' k else R k) 10 = 0#64 ↔ xi = x) ∧
      (fun k => if k ∈ strcmpKs then R'' k else R k) 1 = BitVec.ofNat 64 (i + 4) ∧
      ∀ k, k ∉ strcmpKs → (fun k => if k ∈ strcmpKs then R'' k else R k) k = R k := by
    refine ⟨?_, ?_, fun k hk => by dsimp only; rw [ite_eq_right_iff.2 (fun h => absurd h hk)]⟩
    · dsimp only; rw [ite_eq_left_iff.2 (fun h => absurd (by decide) h), e2]; exact hres
    · dsimp only
      rw [ite_eq_left_iff.2 (fun h => absurd (by decide) h), show (1 : Nat) = VsaIris.ra from rfl, e1]
  iapply Hk $$ %(fun k => if k ∈ strcmpKs then R'' k else R k) %hpure Hpc
  rw [show strcmpKs = VsaIris.ra :: 10 :: 11 :: 12 :: argClob from rfl]
  iexact HR

end Call

end VsaIris.Interp
