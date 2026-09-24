import VsaIris.Interp.EnvDefineArms

/-!
# `env_define`'s growth, at the Iris level

`def_grow` (`0x80002b98`): `cap := cap'`, `realloc` the names array, store it,
`realloc` the values array, store it; both non-NULL go on to the append
(`def_append`) at the grown geometry, otherwise to the out-of-memory arm. The
first growth reallocs from NULL (`cap = 0`), later ones from the live arrays:
one proof over the optional old blocks (`wp_call_reallocOpt`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr Vsa.Sim

/-- An array block, absent while `cap = 0`. -/
def obOf (c : Nat) (b : Nat × Nat) : Option (Nat × Nat) := if c = 0 then none else some b

/-- The heap's live list without the old block. -/
def obRest : Option (Nat × Nat) → List (Nat × Nat) → List (Nat × Nat)
  | none, H => H
  | some b, H => H.erase b

theorem Regime.plus_add (ρ : Regime) (a b : Nat) : (ρ.plus a).plus b = ρ.plus (a + b) := by
  cases ρ <;> simp [Regime.plus]; omega

theorem obRest_mem {ob : Option (Nat × Nat)} {H : List (Nat × Nat)}
    (hob : ∀ b, ob = some b → b ∈ H) (e : Nat × Nat) : e ∈ H ↔ e ∈ ob.toList ++ obRest ob H := by
  cases ob with
  | none => simp [obRest]
  | some b =>
    simp only [Option.toList_some, List.singleton_append, obRest]
    exact (List.perm_cons_erase (hob b rfl)).mem_iff

theorem obRest_sub {ob : Option (Nat × Nat)} {H : List (Nat × Nat)} {e : Nat × Nat}
    (he : e ∈ H) (hne : ∀ b, ob = some b → e ≠ b) : e ∈ obRest ob H := by
  cases ob with
  | none => exact he
  | some b => exact (List.mem_erase_of_ne (hne b rfl)).2 he

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
/-- The heap with the old block in front. -/
theorem heapRes_obFront {ρ : Regime} {ob : Option (Nat × Nat)} {H : List (Nat × Nat)}
    (hob : ∀ b, ob = some b → b ∈ H) :
    heapRes (GF := GF) vsaLayoutP vsaRoomB ρ H ⊢
      heapRes vsaLayoutP vsaRoomB ρ (ob.toList ++ obRest ob H) :=
  heapRes_congr (obRest_mem hob)

/-- The owned set without the arrays: the base bytes and the struct block. -/
def growS (s out : Nat) (G : FrameGeom) (a : Nat) : Prop := baseS s out a ∨ InExt G.sblk a

omit I in
/-- **The arrays split off** a frame's owned set. -/
theorem getS_split {s out n : Nat} {G : FrameGeom} {img : Nat → BitVec 8} (f : Nat → BitVec 8)
    (hlay : FrameLayout img G n) (hdisj : ∀ a, frameS G a → ¬ baseS s out a) :
    ownSet (GF := GF) (getS s out G) (fun a => a ↦ₘ f a) ⊢
      ownSet (growS s out G) (fun a => a ↦ₘ f a) ∗ obOwn (obOf G.cap G.nblk) f ∗
        obOwn (obOf G.cap G.vblk) f := by
  by_cases hc : G.cap = 0
  · iintro H
    simp only [obOf, hc, ite_true, obOwn]
    isplitl [H]
    · iapply ownSet_iff _ (fun a => by
        unfold getS growS; rw [frameS_iff]
        simp [BlocksCover, FrameGeom.blocks, hc]) $$ H
    · isplitl [] <;> iempintro
  · have hbl : G.blocks = [G.sblk, G.nblk, G.vblk] := by simp [FrameGeom.blocks, hc]
    have hd := hlay.disjoint
    rw [hbl] at hd
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at hd
    obtain ⟨⟨dsn, dsv⟩, dnv, -⟩ := hd
    have hfN : ∀ a, InExt G.nblk a → frameS G a := fun a h => by
      unfold frameS; exact .inr ⟨hc, .inl h⟩
    have hfV : ∀ a, InExt G.vblk a → frameS G a := fun a h => by
      unfold frameS; exact .inr ⟨hc, .inr h⟩
    iintro H
    simp only [obOf, hc, ite_false, obOwn]
    unfold blockOwnAt
    ihave H := ownSet_iff (T := fun a => growS s out G a ∨ (InExt G.nblk a ∨ InExt G.vblk a)) _
      (fun a => by unfold getS growS frameS; simp only [hc, ne_eq, not_false_eq_true, _root_.true_and, or_assoc])
      $$ H
    ihave ⟨H0, H⟩ := ownSet_unglue _ _ _ (fun a h0 h => by
      unfold growS at h0
      rcases h0 with hb | hs
      · rcases h with hn | hv
        · exact hdisj a (hfN a hn) hb
        · exact hdisj a (hfV a hv) hb
      · rcases h with hn | hv
        · exact dsn a hs hn
        · exact dsv a hs hv) $$ H
    ihave ⟨HN, HV⟩ := ownSet_unglue _ _ _ (fun a hn hv => dnv a hn hv) $$ H
    obtain ⟨pn, nn⟩ := G.nblk
    obtain ⟨pv, nv⟩ := G.vblk
    iframe H0 HN HV

/-- What the rejoined owned set holds. -/
structure GrowJoin (s out : Nat) (G : FrameGeom) (f0 v1 v2 : Nat → BitVec 8) (Mt : Mem) : Prop where
  base : ∀ a, growS s out G a → imgM Mt a = f0 a
  names : ∀ a, InExt G.nblk a → imgM Mt a = v1 a
  vals : ∀ a, InExt G.vblk a → imgM Mt a = v2 a
  dN : ∀ a, growS s out G a → ¬ InExt G.nblk a
  dV : ∀ a, growS s out G a → ¬ InExt G.vblk a
  dNV : ∀ a, InExt G.nblk a → ¬ InExt G.vblk a

omit I in
/-- **Fresh arrays joined** into a frame's owned set, at one tracking memory. -/
theorem getS_join {s out : Nat} {G : FrameGeom} (hc : G.cap ≠ 0) (f0 v1 v2 : Nat → BitVec 8) :
    ownSet (GF := GF) (growS s out G) (fun a => a ↦ₘ f0 a) ∗ blockOwnAt G.nblk.1 G.nblk.2 v1 ∗
        blockOwnAt G.vblk.1 G.vblk.2 v2 ⊢
      ∃ Mt : Mem, ⌜GrowJoin s out G f0 v1 v2 Mt⌝ ∗
        ownSet (getS s out G) (fun a => a ↦ₘ imgM Mt a) := by
  unfold blockOwnAt
  iintro ⟨H0, HN, HV⟩
  ihave ⟨⟨H0, HN⟩, %d0N⟩ := keep_pure (ownSet_disj _ _ f0 v1) $$ [H0 HN]
  · iframe H0 HN
  ihave ⟨⟨H0, HV⟩, %d0V⟩ := keep_pure (ownSet_disj _ _ f0 v2) $$ [H0 HV]
  · iframe H0 HV
  ihave ⟨⟨HN, HV⟩, %dNV⟩ := keep_pure (ownSet_disj _ _ v1 v2) $$ [HN HV]
  · iframe HN HV
  ihave HNV := ownSet_glue _ _ v1 v2 dNV $$ [HN HV]
  · iframe HN HV
  ihave H := ownSet_glue (growS s out G) (fun a => InExt (G.nblk.1, G.nblk.2) a ∨
      InExt (G.vblk.1, G.vblk.2) a) f0 (glue (InExt (G.nblk.1, G.nblk.2)) v1 v2)
    (fun a h0 h => by
      rcases h with h | h
      · exact d0N a h0 h
      · exact d0V a h0 h) $$ [H0 HNV]
  · iframe H0 HNV
  ihave H := ownSet_iff (T := getS s out G) _ (fun a => by
    unfold getS growS frameS
    simp only [hc, ne_eq, not_false_eq_true, _root_.true_and, or_assoc]) $$ H
  ihave ⟨%Mt, %hag, H⟩ := ownSet_tracked _ _ $$ H
  iexists Mt
  iframe H
  ipureintro
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, d0N, d0V, dNV⟩
  · rw [hag a (by
      unfold getS frameS; unfold growS at ha
      rcases ha with h | h
      · exact .inl h
      · exact .inr (.inl h))]
    unfold glue; rw [if_pos ha]
  · rw [hag a (by unfold getS frameS; exact .inr (.inr ⟨hc, .inl ha⟩))]
    have h0 : ¬ growS s out G a := fun h => d0N a h ha
    unfold glue; rw [if_neg h0, if_pos ha]
  · rw [hag a (by unfold getS frameS; exact .inr (.inr ⟨hc, .inr ha⟩))]
    have h0 : ¬ growS s out G a := fun h => d0V a h ha
    have hn : ¬ InExt (G.nblk.1, G.nblk.2) a := fun h => dNV a h ha
    unfold glue; rw [if_neg h0, if_neg hn]

end Own

end VsaIris.Interp
