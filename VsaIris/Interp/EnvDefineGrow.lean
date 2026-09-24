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

theorem Regime.plus_eq_uncounted {ρ : Regime} {c : Nat} (h : ρ.plus c = .uncounted) :
    ρ = .uncounted := by cases ρ <;> simp_all [Regime.plus]

/-- Two entries of a pairwise-disjoint list, one nonempty, differ unless the same entry. -/
theorem ne_of_pairwise_disj {B₁ B₂ bs : List (Nat × Nat)} {b c : Nat × Nat}
    (hd : (B₁ ++ bs ++ B₂).Pairwise ExtDisj) (hb : b ∈ B₁ ∨ b ∈ B₂) (hc : c ∈ bs) (hc0 : 0 < c.2) :
    b ≠ c := by
  rintro rfl
  have hin : InExt b b.1 := ⟨Nat.le_refl _, by omega⟩
  rw [List.pairwise_append, List.pairwise_append] at hd
  rcases hb with hb | hb
  · exact hd.1.2.2 b hb b hc b.1 hin hin
  · exact hd.2.2 b (List.mem_append_right _ hc) b hb b.1 hin hin

theorem obRest_perm {ob : Option (Nat × Nat)} {H : List (Nat × Nat)}
    (hob : ∀ b, ob = some b → b ∈ H) : H.Perm (ob.toList ++ obRest ob H) := by
  cases ob with
  | none => simp [obRest]
  | some b =>
    simp only [Option.toList_some, List.singleton_append, obRest]
    exact List.perm_cons_erase (hob b rfl)

theorem obRest_mem {ob : Option (Nat × Nat)} {H : List (Nat × Nat)}
    (hob : ∀ b, ob = some b → b ∈ H) (e : Nat × Nat) : e ∈ H ↔ e ∈ ob.toList ++ obRest ob H :=
  (obRest_perm hob).mem_iff

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
  heapRes_congr (obRest_perm hob)

/-- The owned set without the arrays: the base bytes and the struct block. -/
def growS (s out : Nat) (G : FrameGeom) (a : Nat) : Prop := baseS s out a ∨ InExt G.sblk a

omit I in
/-- **The arrays split off** a frame's owned set. -/
theorem getS_split {s out n : Nat} {Gf : FrameGeom} {img : Nat → BitVec 8} (f : Nat → BitVec 8)
    (hlay : FrameLayout img Gf n) (hdisj : ∀ a, frameS Gf a → ¬ baseS s out a) :
    ownSet (GF := GF) (getS s out Gf) (fun a => a ↦ₘ f a) ⊢
      ownSet (growS s out Gf) (fun a => a ↦ₘ f a) ∗ obOwn (obOf Gf.cap Gf.nblk) f ∗
        obOwn (obOf Gf.cap Gf.vblk) f := by
  by_cases hc : Gf.cap = 0
  · iintro H
    simp only [obOf, hc, ite_true, obOwn]
    isplitl [H]
    · iapply ownSet_iff _ (fun a => by
        unfold getS growS; rw [frameS_iff]
        simp [BlocksCover, FrameGeom.blocks, hc]) $$ H
    · isplitl [] <;> iempintro
  · have hbl : Gf.blocks = [Gf.sblk, Gf.nblk, Gf.vblk] := by simp [FrameGeom.blocks, hc]
    have hd := hlay.disjoint
    rw [hbl] at hd
    simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
      forall_eq, List.Pairwise.nil, and_true] at hd
    obtain ⟨⟨dsn, dsv⟩, dnv, -⟩ := hd
    have hfN : ∀ a, InExt Gf.nblk a → frameS Gf a := fun a h => by
      unfold frameS; exact .inr ⟨hc, .inl h⟩
    have hfV : ∀ a, InExt Gf.vblk a → frameS Gf a := fun a h => by
      unfold frameS; exact .inr ⟨hc, .inr h⟩
    iintro H
    simp only [obOf, hc, ite_false, obOwn]
    unfold blockOwnAt
    ihave H := ownSet_iff (T := fun a => growS s out Gf a ∨ (InExt Gf.nblk a ∨ InExt Gf.vblk a)) _
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
    obtain ⟨pn, nn⟩ := Gf.nblk
    obtain ⟨pv, nv⟩ := Gf.vblk
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
theorem getS_join {s out : Nat} {Gf : FrameGeom} (hc : Gf.cap ≠ 0) (f0 v1 v2 : Nat → BitVec 8) :
    ownSet (GF := GF) (growS s out Gf) (fun a => a ↦ₘ f0 a) ∗ blockOwnAt Gf.nblk.1 Gf.nblk.2 v1 ∗
        blockOwnAt Gf.vblk.1 Gf.vblk.2 v2 ⊢
      ∃ Mt : Mem, ⌜GrowJoin s out Gf f0 v1 v2 Mt⌝ ∗
        ownSet (getS s out Gf) (fun a => a ↦ₘ imgM Mt a) := by
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
  ihave H := ownSet_glue (growS s out Gf) (fun a => InExt (Gf.nblk.1, Gf.nblk.2) a ∨
      InExt (Gf.vblk.1, Gf.vblk.2) a) f0 (glue (InExt (Gf.nblk.1, Gf.nblk.2)) v1 v2)
    (fun a h0 h => by
      rcases h with h | h
      · exact d0N a h0 h
      · exact d0V a h0 h) $$ [H0 HNV]
  · iframe H0 HNV
  ihave H := ownSet_iff (T := getS s out Gf) _ (fun a => by
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
    have h0 : ¬ growS s out Gf a := fun h => d0N a h ha
    unfold glue; rw [if_neg h0, if_pos ha]
  · rw [hag a (by unfold getS frameS; exact .inr (.inr ⟨hc, .inr ha⟩))]
    have h0 : ¬ growS s out Gf a := fun h => d0V a h ha
    have hn : ¬ InExt (Gf.nblk.1, Gf.nblk.2) a := fun h => dNV a h ha
    unfold glue; rw [if_neg h0, if_neg hn]

/-- The part of a `realloc` outcome besides the heap: NULL (uncounted, the
old block back) or a fresh block holding the old contents. -/
def reallocRest (ρ : Regime) (H1 Hx : List (Nat × Nat)) (ob : Option (Nat × Nat)) (nNew : Nat)
    (old : Nat → BitVec 8) (p' : BitVec 64) : IProp GF :=
  iprop((⌜p' = 0#64 ∧ ρ = .uncounted⌝ ∗ obOwn ob old) ∨
    (⌜FreshBlock vsaLayoutP H1 p'.toNat nNew ∧ p'.toNat % 16 = 0 ∧ Hx = (p'.toNat, nNew) :: H1⌝ ∗
      ∃ v : Nat → BitVec 8, ⌜Copies old v (obPtr ob) p'.toNat (obLen ob)⌝ ∗
        blockOwnAt p'.toNat nNew v))

omit I in
/-- A NULL `realloc` result: uncounted. -/
theorem reallocRest_null {ρ : Regime} {H1 Hx : List (Nat × Nat)} {ob : Option (Nat × Nat)}
    {nNew : Nat} {old : Nat → BitVec 8} {p' : BitVec 64} (hp : p'.toNat = 0) :
    reallocRest (GF := GF) ρ H1 Hx ob nNew old p' ⊢ ⌜ρ = .uncounted⌝ := by
  unfold reallocRest
  iintro (⟨%h, -⟩ | ⟨%hf, -⟩)
  · ipureintro; exact h.2
  · exfalso; exact hf.1.nonzero hp

omit I in
/-- A non-NULL `realloc` result: the fresh block. -/
theorem reallocRest_fresh {ρ : Regime} {H1 Hx : List (Nat × Nat)} {ob : Option (Nat × Nat)}
    {nNew : Nat} {old : Nat → BitVec 8} {p' : BitVec 64} (hp : p'.toNat ≠ 0) :
    reallocRest (GF := GF) ρ H1 Hx ob nNew old p' ⊢
      ⌜FreshBlock vsaLayoutP H1 p'.toNat nNew ∧ p'.toNat % 16 = 0 ∧ Hx = (p'.toNat, nNew) :: H1⌝ ∗
        ∃ v : Nat → BitVec 8, ⌜Copies old v (obPtr ob) p'.toNat (obLen ob)⌝ ∗
          blockOwnAt p'.toNat nNew v := by
  unfold reallocRest
  iintro (⟨%h, -⟩ | ⟨%hf, Hv⟩)
  · exfalso; exact hp (by rw [h.1]; rfl)
  · iframe Hv; ipureintro; exact hf

omit I in
/-- **A `realloc` outcome's heap**, covering the live list it came from. -/
theorem reallocOptRes_heap {ρ : Regime} {H1 : List (Nat × Nat)} {ob : Option (Nat × Nat)}
    {nNew : Nat} {old : Nat → BitVec 8} {p' : BitVec 64} :
    reallocOptRes (GF := GF) ρ H1 ob nNew old p' ⊢
      ∃ Hx, heapRes vsaLayoutP vsaRoomB ρ Hx ∗ ⌜∀ e ∈ H1, e ∈ Hx⌝ ∗
        reallocRest ρ H1 Hx ob nNew old p' := by
  unfold reallocOptRes reallocRest
  iintro (⟨%h, Hh, Hob⟩ | ⟨%hf, Hh, Hv⟩)
  · iexists (ob.toList ++ H1)
    iframe Hh
    isplitl []
    · ipureintro; intro e he; exact List.mem_append_right _ he
    ileft; iframe Hob; ipureintro; exact h
  · iexists ((p'.toNat, nNew) :: H1)
    iframe Hh
    isplitl []
    · ipureintro; intro e he; exact List.mem_cons_of_mem _ he
    iright; iframe Hv; ipureintro; exact ⟨hf.1, hf.2, rfl⟩

/-- The state at the growth (`0x80002b98`): a full frame (`cap = n`), `a5`
the next cap, `a1` its names array's size, `s6` the old names array. -/
structure GrowReady (C : DefCall) (G : FrameGeom) (n : Nat) (img : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  stack : DefStack C.s.toNat C.r (pairVal C.saved) R Mt
  name : R 18 = C.pn
  vp : R 21 = C.vp
  env : (R 20).toNat = G.e
  lay : FrameLayout (imgM Mt) G n
  full : G.cap = n
  img : ∀ a, frameS G a → imgM Mt a = img a
  sepOut : ∀ a, frameS G a → a < C.vp.toNat ∨ C.vp.toNat + 24 ≤ a
  sepStk : ∀ a, frameS G a → a < C.s.toNat - 64 ∨ C.s.toNat ≤ a
  slot : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 → imgM Mt a = C.so a
  cap : R 15 = BitVec.ofNat 64 (nextCap n)
  names : R 11 = BitVec.ofNat 64 (8 * nextCap n)
  arr : R 22 = BitVec.ofNat 64 G.pn

/-- The values array (`24 * cap` bytes) is in the upper half of 32-bit RAM. -/
theorem FrameLayout.vcap_lt {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) : 24 * G.cap < 2 ^ 31 := by
  rcases Nat.eq_zero_or_pos G.cap with h0 | hpos
  · omega
  obtain ⟨-, -, -, h4⟩ := h.arrays_le hpos
  have hw := h.win G.vblk (by simp [FrameGeom.blocks, show G.cap ≠ 0 by omega])
  have := hw.lo; have := hw.hi; have := hw.htif
  unfold htifLo at this
  omega

/-- The frame's three blocks are pairwise apart (with arrays). -/
theorem FrameLayout.apart {img : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) (hc : G.cap ≠ 0) :
    ExtDisj G.sblk G.nblk ∧ ExtDisj G.sblk G.vblk ∧ ExtDisj G.nblk G.vblk := by
  have hd := h.disjoint
  rw [show G.blocks = [G.sblk, G.nblk, G.vblk] by simp [FrameGeom.blocks, hc]] at hd
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true] at hd
  exact ⟨hd.1.1, hd.1.2, hd.2.1⟩

theorem nextCap_even (n : Nat) : nextCap n % 2 = 0 := by unfold nextCap; split <;> omega

theorem roundUp16_32 (c : Nat) : roundUp16 (32 * c) = 8 * c + 24 * c := by
  unfold roundUp16; omega

/-- **The growth** `0x80002b98`: both arrays `realloc`ed to the next cap,
then the append at the grown geometry; NULL from either aborts. -/
theorem def_grow (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hl : ∀ p ∈ envText, live p.1)
    (hlive : AllocLive live) (N : NativeAddrs) {C : DefCall} (hC : C.OK) {ρ : Regime}
    {st : Store} {fa : Addr} {f : Frame} {G : FrameGeom} {img : Nat → BitVec 8}
    {R : Nat → BitVec 64} {Mt : Mem} {H B₁ B₂ : List (Nat × Nat)}
    (hR : GrowReady C G f.vars.length img R Mt) (hf : st.frames[fa]? = some f)
    (hinv : Vsa.Sim.StoreInvariant st) (hmiss : ¬ f.vars.any (·.1 == C.x))
    (hdisj : ∀ a, frameS G a → ¬ baseS C.s.toNat C.vp.toNat a)
    (hBH : ∀ b ∈ B₁ ++ G.blocks ++ B₂, b ∈ H) (hBd : (B₁ ++ G.blocks ++ B₂).Pairwise ExtDisj) :
    textOwn envText ∗ textOwn allocText ∗ gp ↦ᵣ□ gpV ∗ strlenSpec Wp ∗ memcpySpec Wp ∗
      strAt C.pn.toNat C.x ∗ valImg N C.so C.vp.toNat C.v ∗
      VsaIris.PC ↦ᵣ 0x80002b98#64 ∗ regsOf gprs R ∗
      ownSet (getS C.s.toNat C.vp.toNat G) (fun a => a ↦ₘ imgM Mt a) ∗
      stackScratch (C.s - 64#64) allocHeadroom ∗
      heapRes vsaLayoutP vsaRoomB
        (ρ.plus (nameCopyCost C.x + arrayReallocCost (nextCap f.vars.length))) H ∗
      bindings N img G.pn G.pv f.vars ∗ parentAt f.parent G.par ∗ frameAt fa G.e ∗
      frameCloser N st fa B₁ B₂ ∗ defK Wp Φ N C ρ (st.define fa C.x C.v)
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hat, #Hgp, #Hsl, #Hmc, #Hx, #Hv, Hpc, HR, HS, Hscr, Hh, #Hb, #Hp, #HGe, Hclose, HK⟩
  have hs64 : 64 ≤ C.s.toNat := by have := hC.s64; unfold htifLo at this; omega
  have h2 : (R 2).toNat = C.s.toNat - 64 := hR.stack.sp
  have hlay := hR.lay
  have hew := hlay.envWin
  have hsb := hlay.sblk
  have := hew.lo; have := hew.hi; have := hew.htif; have := hew.align
  have hcl := hlay.cap_lt
  have hfull := hR.full
  have hc'lt := lt_nextCap f.vars.length
  have hc'ev := nextCap_even f.vars.length
  have hc'cs : (f.vars.length = 0 ∧ nextCap f.vars.length = 8) ∨
      (0 < f.vars.length ∧ nextCap f.vars.length = 2 * f.vars.length) := by
    unfold nextCap; split <;> omega
  -- the charges: names, values, the name copy
  have hcost : nameCopyCost C.x + arrayReallocCost (nextCap f.vars.length) =
      nameCopyCost C.x + 24 * nextCap f.vars.length + 8 * nextCap f.vars.length := by
    unfold arrayReallocCost; rw [roundUp16_32]; omega
  rw [hcost, ← Regime.plus_add, ← Regime.plus_add]
  -- the arrays off the owned set
  ihave ⟨H0, HN, HV⟩ := getS_split (imgM Mt) hlay hdisj $$ HS
  have hS0 : ∀ a, G.e ≤ a → a < G.e + 32 → growS C.s.toNat C.vp.toNat G a :=
    fun a h1 h2 => .inr ⟨by omega, by omega⟩
  -- `cap := cap'`, `a0 := names`
  iapply wp_span Wp (def_grow1 hl (S := growS C.s.toNat C.vp.toNat G) (R := R) (Mt := Mt) hew
    hR.env hS0)
  iframe Ht Hgp Hpc HR H0
  iintro %pc1 %R1 %Mt1 %⟨rfl, rfl, h10, hk1⟩ Hpc HR H0
  -- `realloc(names, 8 * cap')`
  have hobN : ∀ b, obOf G.cap G.nblk = some b → b ∈ H := fun b hb => by
    by_cases h0 : G.cap = 0
    · simp [obOf, h0] at hb
    · simp only [obOf, h0, ite_false, Option.some.injEq] at hb
      subst hb
      exact hBH _ (List.mem_append_left _ (List.mem_append_right _
        (by simp [FrameGeom.blocks, h0])))
  have hpn : (R1 10).toNat = obPtr (obOf G.cap G.nblk) := by
    rw [h10, hR.arr]
    by_cases h0 : G.cap = 0
    · simp only [obOf, h0, ite_true, obPtr]; rw [(hlay.empty h0).1]; rfl
    · simp only [obOf, h0, ite_false, obPtr]
      have ha := (hlay.arrays (by omega)).1
      have hw := hlay.win G.nblk (by simp [FrameGeom.blocks, h0])
      rw [ha] at hw ⊢
      have := hw.hi; simp only at this ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen1 : obLen (obOf G.cap G.nblk) < 8 * nextCap f.vars.length := by
    by_cases h0 : G.cap = 0
    · simp only [obOf, h0, ite_true, obLen]; omega
    · simp only [obOf, h0, ite_false, obLen]; rw [(hlay.arrays (by omega)).1]; simp only; omega
  have hsp1 : SpOKA (R1 2) := def_spOK hC (by rw [hk1 2 (by decide)]; exact h2)
  rw [← def_sp hC (show (R1 2).toNat = C.s.toNat - 64 by rw [hk1 2 (by decide)]; exact h2)]
  iapply wp_call_reallocOpt hlive Wp (i := 0x80002ba0)
    (jalx_80002ba0 live fun p hp => hl _ (env_code_80002ba0 p hp)) (by decide)
    ((ρ.plus (nameCopyCost C.x)).plus (24 * nextCap f.vars.length)) (obRest (obOf G.cap G.nblk) H)
    (obOf G.cap G.nblk) (8 * nextCap f.vars.length) (imgM Mt) (8 * nextCap f.vars.length)
    ⟨by omega, by unfold roundUp16; omega⟩ (by omega) hpn
    (by rw [hk1 11 (by decide), hR.names]) hsp1 hlen1
  isplitl []
  · iapply instrAt_of_text env_code_80002ba0 $$ Ht
  iframe Hat Hgp Hpc HR Hscr HN
  isplitl [Hh]
  · iapply heapRes_obFront hobN $$ Hh
  iintro %R2 %p1 %⟨h10p, -, hk2⟩ Hpc HR Hscr Hres1
  rw [show BitVec.ofNat 64 (0x80002ba0 + 4) = 0x80002ba4#64 from rfl]
  ihave ⟨%Hx, Hh, %hHx, Hrest1⟩ := reallocOptRes_heap $$ Hres1
  have e2 : ∀ k, k = 2 ∨ k = 8 ∨ k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R2 k = R k :=
    fun k hk => by
      have ha : k ∉ VsaIris.ra :: 10 :: vsaClob := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hb : k ≠ 10 := by rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hk2 k ha, hk1 k hb]
  -- `names := a0`, `a0 := vals`, `a1 := 24 * cap'`
  have hcap1 : imgLE (imgM (writeLog Mt [(G.e + 4, 4, R 15)])) (G.e + 4) 4 =
      nextCap f.vars.length := by
    rw [imgLE4_store, hR.cap, BitVec.toNat_ofNat]; omega
  have hpv1 : imgLE (imgM (writeLog Mt [(G.e + 4, 4, R 15)])) (G.e + 16) 8 = G.pv := by
    rw [← hlay.vals]
    exact imgLE_congr fun i hi => imgM_store_miss _ _ (by omega)
  iapply wp_span Wp (def_grow2 hl (S := growS C.s.toNat C.vp.toNat G) (R := R2)
    (Mt := writeLog Mt [(G.e + 4, 4, R 15)]) hew (by rw [e2 20 (by omega)]; exact hR.env) hS0
    (by omega) hcap1 hpv1)
  iframe Ht Hgp Hpc HR H0
  iintro %pc3 %R3 %Mt2 %⟨rfl, rfl, h10v, h11v, h15v, hk3⟩ Hpc HR H0
  -- `realloc(vals, 24 * cap')`
  have hvcl := hlay.vcap_lt
  have hobV : ∀ b, obOf G.cap G.vblk = some b → b ∈ obRest (obOf G.cap G.nblk) H := fun b hb => by
    by_cases h0 : G.cap = 0
    · simp [obOf, h0] at hb
    · simp only [obOf, h0, ite_false, Option.some.injEq] at hb
      subst hb
      obtain ⟨-, -, dnv⟩ := hlay.apart h0
      have hn0 : 0 < G.nblk.2 := by rw [(hlay.arrays (by omega)).1]; simp only; omega
      refine obRest_sub (hBH _ (List.mem_append_left _ (List.mem_append_right _
        (by simp [FrameGeom.blocks, h0])))) fun b hb heq => ?_
      simp only [obOf, h0, ite_false, Option.some.injEq] at hb
      subst hb
      exact dnv G.nblk.1 ⟨Nat.le_refl _, by omega⟩ (by rw [heq]; exact ⟨Nat.le_refl _, by omega⟩)
  have hpv : (R3 10).toNat = obPtr (obOf G.cap G.vblk) := by
    rw [h10v]
    by_cases h0 : G.cap = 0
    · simp only [obOf, h0, ite_true, obPtr]; rw [(hlay.empty h0).2]; rfl
    · simp only [obOf, h0, ite_false, obPtr]
      have ha := (hlay.arrays (by omega)).2
      have hw := hlay.win G.vblk (by simp [FrameGeom.blocks, h0])
      rw [ha] at hw ⊢
      have := hw.hi; simp only at this ⊢
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hlen2 : obLen (obOf G.cap G.vblk) < 24 * nextCap f.vars.length := by
    by_cases h0 : G.cap = 0
    · simp only [obOf, h0, ite_true, obLen]; omega
    · simp only [obOf, h0, ite_false, obLen]; rw [(hlay.arrays (by omega)).2]; simp only; omega
  have h32 : R3 2 = R1 2 := by rw [hk3 2 (by decide) (by decide) (by decide), e2 2 (by omega), hk1 2 (by decide)]
  have hsp3 : SpOKA (R3 2) := by rw [h32]; exact hsp1
  rw [← h32]
  iapply wp_call_reallocOpt hlive Wp (i := 0x80002bbc)
    (jalx_80002bbc live fun p hp => hl _ (env_code_80002bbc p hp)) (by decide)
    (ρ.plus (nameCopyCost C.x)) (obRest (obOf G.cap G.vblk) Hx)
    (obOf G.cap G.vblk) (24 * nextCap f.vars.length) (imgM Mt) (24 * nextCap f.vars.length)
    ⟨by omega, by unfold roundUp16; omega⟩ (by omega) hpv h11v hsp3 hlen2
  isplitl []
  · iapply instrAt_of_text env_code_80002bbc $$ Ht
  iframe Hat Hgp Hpc HR Hscr HV
  isplitl [Hh]
  · iapply heapRes_obFront (fun b hb => hHx b (hobV b hb)) $$ Hh
  iintro %R4 %p2 %⟨h10q, -, hk4⟩ Hpc HR Hscr Hres2
  rw [show BitVec.ofNat 64 (0x80002bbc + 4) = 0x80002bc0#64 from rfl]
  ihave ⟨%Hy, Hh, %hHy, Hrest2⟩ := reallocOptRes_heap $$ Hres2
  -- `vals := a0`, and the test
  have e4 : ∀ k, k = 2 ∨ k = 8 ∨ k = 9 ∨ k = 18 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R4 k = R k :=
    fun k hk => by
      have ha : k ∉ VsaIris.ra :: 10 :: vsaClob := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      have hb : k ≠ 10 ∧ k ≠ 11 ∧ k ≠ 15 := by
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hk4 k ha, hk3 k hb.1 hb.2.1 hb.2.2, e2 k hk]
  have hp1i : imgLE (imgM (writeLog (writeLog Mt [(G.e + 4, 4, R 15)]) [(G.e + 8, 8, R2 10)]))
      (G.e + 8) 8 = p1.toNat := by
    rw [← imgW_toNat, ← ldv_ld_img, ldv_store_hit, h10p]
  iapply wp_span Wp (def_grow3 hl (S := growS C.s.toNat C.vp.toNat G) (R := R4)
    (Mt := writeLog (writeLog Mt [(G.e + 4, 4, R 15)]) [(G.e + 8, 8, R2 10)]) hew
    (by rw [e4 20 (by omega)]; exact hR.env) hS0 hp1i)
  iframe Ht Hgp Hpc HR H0
  iintro %pc5 %R5 %Mt3 %⟨rfl, hk5, hcase⟩ Hpc HR H0
  -- the struct stores miss everything but the three fields
  have hmiss3 : ∀ a, (a < G.e + 4 ∨ G.e + 24 ≤ a) →
      imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)]) [(G.e + 8, 8, R2 10)])
        [(G.e + 16, 8, R4 10)]) a = imgM Mt a := fun a ha => by
    rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by omega)]
  have hstr : ∀ a, (a < G.e + 4 ∨ G.e + 24 ≤ a) → frameS G (G.e + 4) := fun _ _ => by
    unfold frameS InExt; left; omega
  have hsepO := hR.sepOut (G.e + 4) (hstr 0 (.inl (by omega)))
  have hsepO' := hR.sepOut (G.e + 23) (by unfold frameS InExt; left; omega)
  have hsepS := hR.sepStk (G.e + 4) (hstr 0 (.inl (by omega)))
  have hsepS' := hR.sepStk (G.e + 23) (by unfold frameS InExt; left; omega)
  have hslot3 : ∀ a, C.vp.toNat ≤ a → a < C.vp.toNat + 24 →
      imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)]) [(G.e + 8, 8, R2 10)])
        [(G.e + 16, 8, R4 10)]) a = C.so a := fun a h1 h2 => by
    rw [hmiss3 a (by omega)]; exact hR.slot a h1 h2
  have h52 : R5 2 = R3 2 := by
    rw [hk5 2 (by decide), e4 2 (by omega), ← e2 2 (by omega), hk3 2 (by decide) (by decide) (by decide)]
  have h52n : (R5 2).toNat = C.s.toNat - 64 := by
    rw [hk5 2 (by decide), e4 2 (by omega)]; exact h2
  rcases hcase with ⟨hp1z, hp2z, rfl⟩ | ⟨hz, rfl⟩
  · -- both arrays grown: the append at the grown geometry
    have hp2n : p2.toNat ≠ 0 := fun h => hp2z (by rw [h10q]; exact BitVec.eq_of_toNat_eq h)
    ihave ⟨%⟨hf1, hal1, hHx1⟩, %v1, %hcp1, HB1⟩ := reallocRest_fresh hp1z $$ Hrest1
    ihave ⟨%⟨hf2, hal2, hHy2⟩, %v2, %hcp2, HB2⟩ := reallocRest_fresh hp2n $$ Hrest2
    obtain ⟨-, hf1lo, hf1hi, hf1d⟩ := hf1.destruct
    obtain ⟨-, hf2lo, hf2hi, hf2d⟩ := hf2.destruct
    have hf1lo' : Vsa.Sim.DlHeap.heapStart ≤ p1.toNat := hf1lo
    have hf1hi' : p1.toNat + 8 * nextCap f.vars.length ≤ Vsa.Sim.DlHeap.heapEnd := hf1hi
    have hf2lo' : Vsa.Sim.DlHeap.heapStart ≤ p2.toNat := hf2lo
    have hf2hi' : p2.toNat + 24 * nextCap f.vars.length ≤ Vsa.Sim.DlHeap.heapEnd := hf2hi
    simp only [Vsa.Sim.DlHeap.heapStart, Vsa.Sim.DlHeap.heapEnd] at hf1lo' hf1hi' hf2lo' hf2hi'
    let G' : FrameGeom := ⟨G.e, nextCap f.vars.length, p1.toNat, p2.toNat, G.par, G.sblk,
      (p1.toNat, 8 * nextCap f.vars.length), (p2.toNat, 24 * nextCap f.vars.length)⟩
    have hc' : G'.cap ≠ 0 := by show nextCap f.vars.length ≠ 0; omega
    -- the struct's fields after the three stores
    have hcnt3 : imgLE (imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)])
        [(G.e + 8, 8, R2 10)]) [(G.e + 16, 8, R4 10)])) G.e 4 = f.vars.length := by
      rw [← hlay.count]; exact imgLE_congr fun i hi => hmiss3 _ (by omega)
    have hpar3 : imgLE (imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)])
        [(G.e + 8, 8, R2 10)]) [(G.e + 16, 8, R4 10)])) (G.e + 24) 8 = G.par := by
      rw [← hlay.parent]; exact imgLE_congr fun i hi => hmiss3 _ (by omega)
    have hcap3 : imgLE (imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)])
        [(G.e + 8, 8, R2 10)]) [(G.e + 16, 8, R4 10)])) (G.e + 4) 4 = nextCap f.vars.length := by
      rw [← hcap1]
      exact imgLE_congr fun i hi => by
        rw [imgM_store_miss _ _ (by omega), imgM_store_miss _ _ (by omega)]
    have hnam3 : imgLE (imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)])
        [(G.e + 8, 8, R2 10)]) [(G.e + 16, 8, R4 10)])) (G.e + 8) 8 = p1.toNat := by
      rw [← hp1i]
      exact imgLE_congr fun i hi => by rw [imgM_store_miss _ _ (by omega)]
    have hval3 : imgLE (imgM (writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)])
        [(G.e + 8, 8, R2 10)]) [(G.e + 16, 8, R4 10)])) (G.e + 16) 8 = p2.toNat := by
      rw [← imgW_toNat, ← ldv_ld_img, ldv_store_hit, h10q]
    generalize hM3 : writeLog (writeLog (writeLog Mt [(G.e + 4, 4, R 15)])
        [(G.e + 8, 8, R2 10)]) [(G.e + 16, 8, R4 10)] = Mt3 at *
    ihave H0 := ownSet_iff (S := growS C.s.toNat C.vp.toNat G) (T := growS C.s.toNat C.vp.toNat G') _
      (fun a => Iff.rfl) $$ H0
    ihave ⟨%Mt4, %hJ, HS⟩ := getS_join (s := C.s.toNat) (out := C.vp.toNat) (Gf := G') hc'
      (imgM Mt3) v1 v2 $$ [H0 HB1 HB2]
    · iframe H0 HB1 HB2
    have hst4 : ∀ a, G.e ≤ a → a < G.e + 32 → imgM Mt4 a = imgM Mt3 a := fun a h1 h2 =>
      hJ.base a (.inr (show InExt G.sblk a from ⟨by omega, by omega⟩))
    have hsf : ∀ o w, o + w ≤ 32 → imgLE (imgM Mt4) (G.e + o) w = imgLE (imgM Mt3) (G.e + o) w :=
      fun o w h => imgLE_congr fun i hi => hst4 _ (by omega) (by omega)
    have hbl' : G'.blocks = [G.sblk, (p1.toNat, 8 * nextCap f.vars.length),
        (p2.toNat, 24 * nextCap f.vars.length)] := by
      simp only [FrameGeom.blocks, hc', ite_false]; rfl
    have hcapc : G.cap = capFor f.vars.length := hlay.cap_canon
    have hlay' : AppLayout (imgM Mt4) G' f.vars.length :=
      { e_ne := hlay.e_ne
        sblk := hlay.sblk
        count := by have := hsf 0 4 (by omega); simp only [Nat.add_zero] at this; rw [this]; exact hcnt3
        cap := by rw [hsf 4 4 (by omega)]; exact hcap3
        names := by rw [hsf 8 8 (by omega)]; exact hnam3
        vals := by rw [hsf 16 8 (by omega)]; exact hval3
        parent := by rw [hsf 24 8 (by omega)]; exact hpar3
        room := hc'lt
        arrays := ⟨rfl, rfl⟩
        disjoint := by
          rw [hbl']
          refine List.pairwise_cons.2 ⟨fun b hb => ?_, List.pairwise_cons.2 ⟨fun b hb => ?_,
            List.pairwise_singleton _ _⟩⟩
          · simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hb
            rcases hb with rfl | rfl
            · exact fun a ha => hJ.dN a (.inr ha)
            · exact fun a ha => hJ.dV a (.inr ha)
          · simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hb
            subst hb; exact hJ.dNV
        win := by
          rw [hbl']
          intro b hb
          simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hb
          rcases hb with rfl | rfl | rfl
          · exact hlay.win _ (by simp [FrameGeom.blocks])
          · exact ⟨by simp only; omega, by simp only; omega, by simp only; unfold htifLo; omega,
              by simp only; omega⟩
          · exact ⟨by simp only; omega, by simp only; omega, by simp only; unfold htifLo; omega,
              by simp only; omega⟩
        e_align := hlay.e_align
        cap_next := by
          rcases growthCost_eq f.vars.length with ⟨-, h2, -⟩ | ⟨h1, -, -⟩
          · exact h2.symm
          · omega }
    have hnon : 0 < f.vars.length → G.cap ≠ 0 := fun h => by omega
    have hoN : ∀ k, k < f.vars.length → ∀ o, o < 8 →
        imgM Mt4 (G'.pn + 8 * k + o) = img (G.pn + 8 * k + o) := fun k hk o ho => by
      have hc0 := hnon (by omega)
      have ha := (hlay.arrays (by omega)).1
      rw [hJ.names _ (show InExt (p1.toNat, 8 * nextCap f.vars.length) (p1.toNat + 8 * k + o) from
        ⟨by simp only; omega, by simp only; omega⟩)]
      have := hcp1 (8 * k + o) (by simp only [obOf, hc0, ite_false, obLen]; rw [ha]; simp only; omega)
      simp only [obOf, hc0, ite_false, obPtr] at this
      rw [show G'.pn + 8 * k + o = p1.toNat + (8 * k + o) by show p1.toNat + _ + _ = _; omega, this,
        ha]
      simp only
      rw [show G.pn + (8 * k + o) = G.pn + 8 * k + o by omega]
      exact hR.img _ (frameS_name hlay hk ho)
    have hoV : ∀ k, k < f.vars.length → ∀ o, o < 24 →
        imgM Mt4 (G'.pv + 24 * k + o) = img (G.pv + 24 * k + o) := fun k hk o ho => by
      have hc0 := hnon (by omega)
      have ha := (hlay.arrays (by omega)).2
      rw [hJ.vals _ (show InExt (p2.toNat, 24 * nextCap f.vars.length) (p2.toNat + 24 * k + o) from
        ⟨by simp only; omega, by simp only; omega⟩)]
      have := hcp2 (24 * k + o) (by simp only [obOf, hc0, ite_false, obLen]; rw [ha]; simp only; omega)
      simp only [obOf, hc0, ite_false, obPtr] at this
      rw [show G'.pv + 24 * k + o = p2.toNat + (24 * k + o) by show p2.toNat + _ + _ = _; omega, this,
        ha]
      simp only
      rw [show G.pv + (24 * k + o) = G.pv + 24 * k + o by omega]
      exact hR.img _ (frameS_val hlay hk ho)
    have hfr' : ∀ a, frameS G' a → InExt G.sblk a ∨ InExt (p1.toNat, 8 * nextCap f.vars.length) a ∨
        InExt (p2.toNat, 24 * nextCap f.vars.length) a := fun a h => by
      unfold frameS at h
      rcases h with h | ⟨-, h | h⟩
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr h)
    have hdisj' : ∀ a, frameS G' a → ¬ baseS C.s.toNat C.vp.toNat a := fun a h hb => by
      rcases hfr' a h with h | h | h
      · exact hdisj a (by unfold frameS; exact .inl h) hb
      · exact hJ.dN a (.inl hb) h
      · exact hJ.dV a (.inl hb) h
    have hAR : AppReady C G G' f.vars.length img R5 Mt4 :=
      { stack := hR.stack.congr (by rw [hk5 2 (by decide), e4 2 (by omega)]) (fun a h1 h2 => by
            rw [hJ.base a (.inl (.inl ⟨h1, h2⟩)), hmiss3 a (by omega)]) hs64
        name := by rw [hk5 18 (by decide), e4 18 (by omega)]; exact hR.name
        vp := by rw [hk5 21 (by decide), e4 21 (by omega)]; exact hR.vp
        env := by rw [hk5 20 (by decide), e4 20 (by omega)]; exact hR.env
        lay := hlay'
        e := rfl
        par := rfl
        oldNames := hoN
        oldVals := hoV
        sepOut := fun a h => by
          rcases hfr' a h with h | h | h
          · exact hR.sepOut a (by unfold frameS; exact .inl h)
          · refine Classical.byContradiction fun hc => ?_
            exact hJ.dN a (.inl (.inr ⟨by omega, by omega⟩)) h
          · refine Classical.byContradiction fun hc => ?_
            exact hJ.dV a (.inl (.inr ⟨by omega, by omega⟩)) h
        sepStk := fun a h => by
          rcases hfr' a h with h | h | h
          · exact hR.sepStk a (by unfold frameS; exact .inl h)
          · refine Classical.byContradiction fun hc => ?_
            exact hJ.dN a (.inl (.inl ⟨by omega, by omega⟩)) h
          · refine Classical.byContradiction fun hc => ?_
            exact hJ.dV a (.inl (.inl ⟨by omega, by omega⟩)) h
        slot := fun a h1 h2 => by rw [hJ.base a (.inl (.inr ⟨h1, h2⟩))]; exact hslot3 a h1 h2 }
    -- the grown frame's blocks are live
    have hstep : ∀ e, e ∈ obRest (obOf G.cap G.nblk) H →
        (∀ b, obOf G.cap G.vblk = some b → e ≠ b) → e ∈ Hy := fun e he h2 => by
      rw [hHy2]; exact List.mem_cons_of_mem _ (obRest_sub (hHx e he) h2)
    have hBH' : ∀ b ∈ B₁ ++ G'.blocks ++ B₂, b ∈ Hy := by
      intro b hb
      rw [hbl'] at hb
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, _root_.or_false] at hb
      have hv0 : ∀ c, obOf G.cap G.vblk = some c → c ∈ G.blocks ∧ 0 < c.2 := fun c hc => by
        by_cases h0 : G.cap = 0
        · simp [obOf, h0] at hc
        · simp only [obOf, h0, ite_false, Option.some.injEq] at hc
          subst hc
          refine ⟨by simp [FrameGeom.blocks, h0], ?_⟩
          rw [(hlay.arrays (by omega)).2]; simp only; omega
      have hn0 : ∀ c, obOf G.cap G.nblk = some c → c ∈ G.blocks ∧ 0 < c.2 := fun c hc => by
        by_cases h0 : G.cap = 0
        · simp [obOf, h0] at hc
        · simp only [obOf, h0, ite_false, Option.some.injEq] at hc
          subst hc
          refine ⟨by simp [FrameGeom.blocks, h0], ?_⟩
          rw [(hlay.arrays (by omega)).1]; simp only; omega
      rcases hb with (hb | hb | hb | hb) | hb
      · -- another frame's block
        exact hstep b (obRest_sub (hBH b (List.mem_append_left _ (List.mem_append_left _ hb)))
          fun c hc => ne_of_pairwise_disj hBd (.inl hb) (hn0 c hc).1 (hn0 c hc).2)
          fun c hc => ne_of_pairwise_disj hBd (.inl hb) (hv0 c hc).1 (hv0 c hc).2
      · -- the struct block
        subst hb
        have hs0 : 0 < G.sblk.2 := by omega
        have hsin : G.sblk ∈ B₁ ++ G.blocks ++ B₂ :=
          List.mem_append_left _ (List.mem_append_right _ (by simp [FrameGeom.blocks]))
        refine hstep _ (obRest_sub (hBH _ hsin) fun c hc heq => ?_) fun c hc heq => ?_
        · by_cases h0 : G.cap = 0
          · simp [obOf, h0] at hc
          · simp only [obOf, h0, ite_false, Option.some.injEq] at hc
            subst hc
            exact (hlay.apart h0).1 G.sblk.1 ⟨Nat.le_refl _, by omega⟩
              (by rw [← heq]; exact ⟨Nat.le_refl _, by omega⟩)
        · by_cases h0 : G.cap = 0
          · simp [obOf, h0] at hc
          · simp only [obOf, h0, ite_false, Option.some.injEq] at hc
            subst hc
            exact (hlay.apart h0).2.1 G.sblk.1 ⟨Nat.le_refl _, by omega⟩
              (by rw [← heq]; exact ⟨Nat.le_refl _, by omega⟩)
      · -- the new names array
        subst hb
        rw [hHy2]
        refine List.mem_cons_of_mem _ (obRest_sub (by rw [hHx1]; exact List.mem_cons_self)
          fun c hc heq => ?_)
        have hcin : c ∈ obRest (obOf G.cap G.nblk) H := hobV c hc
        have hcp0 := (hv0 c hc).2
        exact hf1d c hcin p1.toNat ⟨Nat.le_refl _, by simp only; omega⟩
          (by rw [← heq]; exact ⟨Nat.le_refl _, by simp only; omega⟩)
      · -- the new values array
        subst hb; rw [hHy2]; exact List.mem_cons_self
      · exact hstep b (obRest_sub (hBH b (List.mem_append_right _ hb))
          fun c hc => ne_of_pairwise_disj hBd (.inr hb) (hn0 c hc).1 (hn0 c hc).2)
          fun c hc => ne_of_pairwise_disj hBd (.inr hb) (hv0 c hc).1 (hv0 c hc).2
    rw [show R3 2 = C.s - 64#64 from h52.symm.trans (def_sp hC h52n)]
    iapply def_append Wp hl (allocSpecs live hlive) N hC hAR hf hinv hmiss hdisj' hBH'
    iframe Ht Hat Hgp Hsl Hmc Hx Hv Hpc HR HS Hscr Hh Hb Hp HGe Hclose HK
  · -- NULL from either `realloc`: out of memory
    ihave %hρ : ⌜ρ = .uncounted⌝ $$ [Hrest1 Hrest2]
    · rcases hz with hz | hz
      · ihave %h := reallocRest_null hz $$ Hrest1
        ipureintro
        exact Regime.plus_eq_uncounted (Regime.plus_eq_uncounted h)
      · ihave %h := reallocRest_null (by rw [← h10q, hz]; rfl) $$ Hrest2
        ipureintro
        exact Regime.plus_eq_uncounted h
    subst hρ
    unfold growS
    ihave ⟨HB, -⟩ := ownSet_unglue (baseS C.s.toNat C.vp.toNat) (InExt G.sblk) _ (fun a hb hs =>
      hdisj a (by unfold frameS; exact .inl hs) hb) $$ H0
    rw [show R3 2 = C.s - 64#64 from h52.symm.trans (def_sp hC h52n)]
    iapply def_oom Wp N hC (st' := st.define fa C.x C.v) (H := Hy) (R := R5) rfl h52n hslot3
    simp only [Regime.plus_uncounted]
    iframe Hv Hpc HR HB Hscr Hh HK

end Own

end VsaIris.Interp
