import VsaIris.Interp.Repr

/-!
# The store: one opener, allocation, discard, two-owner facts (package R)

* `storeRepr_open`: the ONE frame opener every `env_*` spec uses (xv6iris
  `claude-notes/spec-modules.md`, "Simultaneous borrows of a sealed bundle
  need ONE opener"); `storeRepr_open_define` specializes the closer to
  `Store.define`.
* `storeRepr_allocFrame` (`env_new`) and `storeRepr_allocClosure` (`EX_FN`):
  the ghost maps grow by a persistent fragment.
* `ownImg_persist`/`strAt_of_owned`: discard exclusively written bytes to
  read-only ones, AFTER the write (INTERP_DESIGN.md §10.6).
* Two owners (§10.7): the store's blocks are pairwise disjoint and off the
  allocator's footprint (`storeRepr_blocks_off_heap`).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProofMode
open VsaIris
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

section Store

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable (N : NativeAddrs)

/-! ## The frame list -/

theorem framesOwn_length :
    ∀ (i : Nat) (fs : List Frame) (Bs : List (List (Nat × Nat))),
      framesOwn (GF := GF) N i fs Bs ⊢ ⌜fs.length = Bs.length⌝
  | _, [], [] => by iintro _; ipureintro; rfl
  | i, _ :: fs, _ :: Bs => by
    rw [framesOwn_cons]
    iintro ⟨-, H⟩
    ihave %h := framesOwn_length (i + 1) fs Bs $$ H
    ipureintro; simp [h]
  | _, [], _ :: _ => by rw [framesOwn_nil_cons]; exact false_elim
  | _, _ :: _, [] => by rw [framesOwn_cons_nil]; exact false_elim

/-- Split off frame `i + k`, with the closer that puts back any frame. -/
theorem framesOwn_open :
    ∀ (k i : Nat) (fs : List Frame) (Bs : List (List (Nat × Nat))) (f : Frame),
      fs[k]? = some f →
      framesOwn (GF := GF) N i fs Bs ⊢ ∃ bl, ⌜Bs[k]? = some bl⌝ ∗ frameOwn N (i + k) f bl ∗
        (∀ f' bl', frameOwn N (i + k) f' bl' -∗ framesOwn N i (fs.set k f') (Bs.set k bl'))
  | _, _, [], _, _, h => by simp at h
  | _, _, _ :: _, [], _, _ => by rw [framesOwn_cons_nil]; exact false_elim
  | 0, i, g :: fs, bl :: Bs, f, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    rw [framesOwn_cons]
    iintro ⟨Hf, Hr⟩
    iexists bl
    isplitr
    · ipureintro; rfl
    simp only [Nat.add_zero]
    iframe Hf
    iintro %f' %bl' Hf'
    simp only [List.set_cons_zero, framesOwn_cons]
    iframe Hf' Hr
  | k + 1, i, g :: fs, bl :: Bs, f, h => by
    simp only [List.getElem?_cons_succ] at h
    rw [framesOwn_cons]
    iintro ⟨Hg, Hr⟩
    ihave ⟨%bl₀, %hb, Hf, Hc⟩ := framesOwn_open k (i + 1) fs Bs f h $$ Hr
    iexists bl₀
    isplitr
    · ipureintro; simpa using hb
    rw [show i + (k + 1) = i + 1 + k by omega]
    iframe Hf
    iintro %f' %bl' Hf'
    simp only [List.set_cons_succ, framesOwn_cons]
    iframe Hg
    iapply Hc $$ %f' %bl' Hf'

/-- A list with `l[k]? = some x` is `take k ++ x :: drop (k+1)`. -/
theorem list_split_at {α} {l : List α} {k : Nat} {x : α} (h : l[k]? = some x) :
    l = l.take k ++ x :: l.drop (k + 1) := by
  have hk : k < l.length := by
    rcases Nat.lt_or_ge k l.length with hk | hk
    · exact hk
    · simp [List.getElem?_eq_none hk] at h
  have hx : l[k] = x := by simpa [List.getElem?_eq_getElem hk] using h
  conv => lhs; rw [← List.take_append_drop k l, List.drop_eq_getElem_cons hk, hx]

/-! ## The one opener -/

/-- **The frame opener.** Frame `fa` comes out with its blocks `bl`, the rest
of the store's blocks around it; the closer takes back any frame `f'` at the
same address with any blocks `bl'`, for any store `s'` that differs from `s`
only at frame `fa`. -/
theorem storeRepr_open {s : Store} {B : List (Nat × Nat)} {fa : Addr} {f : Frame}
    (hf : s.frames[fa]? = some f) :
    storeRepr (GF := GF) N s B ⊢ ∃ bl B₁ B₂, ⌜B = B₁ ++ bl ++ B₂⌝ ∗ frameOwn N fa f bl ∗
      (∀ (s' : Store) (f' : Frame) (bl' : List (Nat × Nat)),
        ⌜s'.closures = s.closures ∧ s'.frames.toList = s.frames.toList.set fa f'⌝ -∗
        frameOwn N fa f' bl' -∗ storeRepr N s' (B₁ ++ bl' ++ B₂)) := by
  unfold storeRepr
  iintro ⟨%mf, %mc, %Bs, Hf, Hc, %⟨hmaps, hB, hbb⟩, Hfr, #Hcl⟩
  have hf' : s.frames.toList[fa]? = some f := by rw [Array.getElem?_toList]; exact hf
  ihave ⟨%bl, %hbl, Hfa, Hclose⟩ := framesOwn_open N fa 0 s.frames.toList Bs f hf' $$ Hfr
  simp only [Nat.zero_add]
  iexists bl, (Bs.take fa).flatten, (Bs.drop (fa + 1)).flatten
  isplitr
  · ipureintro
    rw [hB]
    exact (congrArg List.flatten (list_split_at hbl)).trans (by simp)
  iframe Hfa
  iintro %s' %f' %bl' %⟨hcl, hfr⟩ Hfa'
  ihave Hfr' := Hclose $$ %f' %bl' Hfa'
  iexists mf, mc, Bs.set fa bl'
  rw [← hfr, ← hcl]
  iframe Hf Hc Hfr' Hcl
  ipureintro
  have hsize : s'.frames.size = s.frames.size := by
    rw [← Array.length_toList, ← Array.length_toList, hfr, List.length_set]
  refine ⟨⟨fun k => by rw [hsize]; exact hmaps.frames k,
    fun k => by rw [hcl]; exact hmaps.closures k, hmaps.clos_inj⟩, ?_, ?_⟩
  · have hlt : fa < Bs.length := by
      rcases Nat.lt_or_ge fa Bs.length with h | h
      · exact h
      · simp [List.getElem?_eq_none h] at hbl
    simp [List.set_eq_take_append_cons_drop, hlt]
  · intro a cd h; rw [hcl] at h; exact hbb a cd h

/-- The frame `env_define` leaves (`Store.define`'s update of one frame). -/
def defineFrame (f : Frame) (x : String) (v : Value) : Frame :=
  { f with vars := if f.vars.any (·.1 == x) then (f.vars.map fun p => if p.1 == x then (x, v) else p)
                   else f.vars ++ [(x, v)] }

instance : Inhabited Frame := ⟨⟨none, []⟩⟩

/-- `Store.define` changes only the defined frame. -/
theorem define_frames_toList {s : Store} {fa : Addr} {f : Frame} (hf : s.frames[fa]? = some f)
    (x : String) (v : Value) :
    (s.define fa x v).frames.toList = s.frames.toList.set fa (defineFrame f x v) := by
  unfold Store.define
  rw [Array.toList_modify, List.modify_eq_set]
  have hf' : s.frames.toList[fa]? = some f := by rw [Array.getElem?_toList]; exact hf
  rw [hf']
  rfl

/-- The opener with the closer specialized to `env_define`'s semantic update. -/
theorem storeRepr_open_define {s : Store} {B : List (Nat × Nat)} {fa : Addr} {f : Frame}
    (hf : s.frames[fa]? = some f) (x : String) (v : Value) :
    storeRepr (GF := GF) N s B ⊢ ∃ bl B₁ B₂, ⌜B = B₁ ++ bl ++ B₂⌝ ∗ frameOwn N fa f bl ∗
      (∀ bl' : List (Nat × Nat), frameOwn N fa (defineFrame f x v) bl' -∗
        storeRepr N (s.define fa x v) (B₁ ++ bl' ++ B₂)) := by
  iintro H
  ihave ⟨%bl, %B₁, %B₂, %hB, Hfa, Hc⟩ := storeRepr_open N hf $$ H
  iexists bl, B₁, B₂
  iframe Hfa
  isplitr
  · ipureintro; exact hB
  iintro %bl' Hfa'
  iapply Hc $$ %(s.define fa x v) %_ %bl' %⟨rfl, define_frames_toList hf x v⟩ Hfa'

/-! ## Address lookups -/

omit I in
/-- A persistent list element can be read without consuming the list. -/
theorem sepL_persist_all {α} (Φ : α → IProp GF) [∀ x, Persistent (Φ x)] :
    ∀ l : List α, sepL l Φ ⊢ □ ∀ x, ⌜x ∈ l⌝ → Φ x
  | [] => by
    iintro _
    imodintro
    iintro %x %hx
    cases hx
  | y :: ys => by
    rw [sepL_cons]
    iintro ⟨#Hy, Hys⟩
    ihave #Hys := sepL_persist_all Φ ys $$ Hys
    imodintro
    iintro %x %hx
    rcases List.mem_cons.mp hx with rfl | hx
    · iexact Hy
    · iapply Hys $$ %x %hx

/-- A frame address fragment names an allocated frame. -/
theorem storeRepr_frameAt {s : Store} {B : List (Nat × Nat)} {fa e : Nat} :
    storeRepr (GF := GF) N s B ∗ frameAt fa e ⊢ ⌜fa < s.frames.size⌝ := by
  unfold storeRepr frameAt
  iintro ⟨⟨%mf, %mc, %Bs, Hf, -, %⟨hmaps, -⟩, -⟩, He⟩
  ihave %h := ghost_map_lookup $$ Hf He
  ipureintro
  exact (hmaps.frames fa).1 (by simp [h])

/-- A closure address fragment names an allocated closure. -/
theorem storeRepr_closAt {s : Store} {B : List (Nat × Nat)} {ca p : Nat} :
    storeRepr (GF := GF) N s B ∗ closAt ca p ⊢ ⌜ca < s.closures.size⌝ := by
  unfold storeRepr closAt
  iintro ⟨⟨%mf, %mc, %Bs, -, Hc, %⟨hmaps, -⟩, -⟩, He⟩
  ihave %h := ghost_map_lookup $$ Hc He
  ipureintro
  exact (hmaps.closures ca).1 (by simp [h])

theorem closuresOwn_get :
    ∀ (i : Nat) (cs : List ClosureData) (k : Nat) (cd : ClosureData), cs[k]? = some cd →
      closuresOwn (GF := GF) i cs ⊢ closOwn (i + k) cd
  | _, [], _, _, h => by simp at h
  | i, c :: cs, 0, cd, h => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at h
    subst h
    unfold closuresOwn
    iintro ⟨H, -⟩
    iexact H
  | i, c :: cs, k + 1, cd, h => by
    simp only [List.getElem?_cons_succ] at h
    unfold closuresOwn
    iintro ⟨-, H⟩
    rw [show i + (k + 1) = i + 1 + k by omega]
    iapply closuresOwn_get (i + 1) cs k cd h $$ H

/-- Every closure of the store is readable, persistently, without opening. -/
theorem storeRepr_closure {s : Store} {B : List (Nat × Nat)} {ca : Addr} {cd : ClosureData}
    (h : s.closures[ca]? = some cd) :
    storeRepr (GF := GF) N s B ⊢ closOwn ca cd := by
  unfold storeRepr
  iintro ⟨%mf, %mc, %Bs, -, -, -, -, Hcl⟩
  have h' : s.closures.toList[ca]? = some cd := by rw [Array.getElem?_toList]; exact h
  have := closuresOwn_get (GF := GF) 0 s.closures.toList ca cd h'
  rw [Nat.zero_add] at this
  iapply this $$ Hcl

/-! ## The empty store and allocation -/

/-- The empty store over the two freshly allocated (empty) maps. -/
theorem storeRepr_empty :
    ghost_map_auth (GF := GF) I.frameName (DFrac.own 1) (∅ : NatMap Nat) ∗
      ghost_map_auth I.closName (DFrac.own 1) (∅ : NatMap Nat) ⊢
      storeRepr N ⟨#[], #[]⟩ [] := by
  unfold storeRepr
  iintro ⟨Hf, Hc⟩
  iexists ∅, ∅, []
  iframe Hf Hc
  rw [show (⟨#[], #[]⟩ : Store).frames.toList = [] from rfl,
    show (⟨#[], #[]⟩ : Store).closures.toList = [] from rfl, framesOwn_nil, closuresOwn_nil]
  isplitr
  · ipureintro
    refine ⟨⟨fun k => by simp [get?_empty], fun k => by simp [get?_empty], ?_⟩, rfl, ?_⟩
    · intro a b p ha; simp [get?_empty] at ha
    · intro a cd h; simp at h
  isplitl []
  · iempintro
  · iempintro

theorem framesOwn_snoc (i : Nat) (fs : List Frame) (Bs : List (List (Nat × Nat)))
    (f : Frame) (bl : List (Nat × Nat)) (hlen : fs.length = Bs.length) :
    framesOwn (GF := GF) N i fs Bs ∗ frameOwn N (i + fs.length) f bl ⊢
      framesOwn N i (fs ++ [f]) (Bs ++ [bl]) := by
  induction fs generalizing i Bs with
  | nil =>
    cases Bs with
    | nil =>
      simp only [List.nil_append, framesOwn_cons, framesOwn_nil, List.length_nil, Nat.add_zero]
      iintro ⟨-, H⟩
      iframe H
    | cons _ _ => simp at hlen
  | cons g fs ih =>
    cases Bs with
    | nil => simp at hlen
    | cons b Bs =>
      simp only [List.cons_append, framesOwn_cons, List.length_cons] at hlen ⊢
      iintro ⟨⟨Hg, Hr⟩, Hf⟩
      iframe Hg
      rw [show i + (fs.length + 1) = i + 1 + fs.length by omega]
      iapply ih (i + 1) Bs (by omega)
      iframe Hr Hf

/-- **Frame allocation** (`env_new`): a frame body at a fresh `Env*` joins the
store as frame `s.frames.size`, whose address fragment is handed out. -/
theorem storeRepr_allocFrame {s s' : Store} {B : List (Nat × Nat)} {f : Frame} {Gm : FrameGeom}
    (hfr : s'.frames.toList = s.frames.toList ++ [f]) (hcl : s'.closures = s.closures) :
    storeRepr (GF := GF) N s B ∗ frameBody N f Gm ⊢
      |==> (storeRepr N s' (B ++ Gm.blocks) ∗ frameAt s.frames.size Gm.e) := by
  unfold storeRepr
  iintro ⟨⟨%mf, %mc, %Bs, Hf, Hc, %⟨hmaps, hB, hbb⟩, Hfr, #Hcl⟩, Hbody⟩
  have hnone : PartialMap.get? mf s.frames.size = none := by
    cases h : PartialMap.get? mf s.frames.size with
    | none => rfl
    | some _ => have := (hmaps.frames s.frames.size).1 (by simp [h]); omega
  unfold frameAt
  imod ghost_map_insert_persist (GF := GF) (γ := I.frameName) s.frames.size Gm.e hnone $$ Hf
    with ⟨Hf, #He⟩
  ihave %hlen := framesOwn_length N 0 s.frames.toList Bs $$ Hfr
  imodintro
  iframe He
  iexists PartialMap.insert mf s.frames.size Gm.e, mc, Bs ++ [Gm.blocks]
  rw [hfr, hcl]
  iframe Hf Hc Hcl
  isplitr
  · ipureintro
    have hsize : s'.frames.size = s.frames.size + 1 := by
      rw [← Array.length_toList, ← Array.length_toList, hfr]; simp
    refine ⟨⟨fun k => ?_, fun k => by rw [hcl]; exact hmaps.closures k, hmaps.clos_inj⟩,
      by rw [hB]; simp, fun a cd h => by rw [hcl] at h; exact hbb a cd h⟩
    rw [hsize, Iris.Std.LawfulPartialMap.get?_insert]
    by_cases hk : s.frames.size = k
    · subst hk; simp
    · simp only [hk, ite_false, hmaps.frames k]; omega
  iapply framesOwn_snoc N 0 s.frames.toList Bs f Gm.blocks hlen
  iframe Hfr
  rw [Nat.zero_add, Array.length_toList]
  unfold frameOwn frameAt
  iexists Gm
  iframe He Hbody
  ipureintro; rfl

/-! ## Discarding written bytes to read-only ones -/

omit I in
theorem mem_persist (a : Nat) (b : BitVec 8) : (a ↦ₘ b) ⊢@{IProp GF} |==> a ↦ₘ□ b := by
  unfold memPointsTo
  iintro H
  iapply ghost_map_elem_persist $$ H

omit I in
theorem sepL_persist_bytes (img : Nat → BitVec 8) :
    ∀ l : List Nat, sepL (GF := GF) l (fun a => a ↦ₘ img a) ⊢ |==> sepL l (fun a => a ↦ₘ□ img a)
  | [] => by simp only [sepL_nil]; iintro H; imodintro; iexact H
  | x :: xs => by
    rw [sepL_cons, sepL_cons]
    iintro ⟨Hx, Hxs⟩
    imod mem_persist x (img x) $$ Hx with Hx
    imod sepL_persist_bytes img xs $$ Hxs with Hxs
    imodintro
    iframe Hx Hxs

omit I in
/-- **Discard.** Exclusively owned bytes become read-only forever. Used AFTER
the last write (INTERP_DESIGN.md §10.6): a string buffer once copied, a
closure object once filled, the `jmp_buf` once `setjmp` ran. -/
theorem ownImg_persist (S : Nat → Prop) (img : Nat → BitVec 8) :
    ownImg (GF := GF) S img ⊢ |==> roImg S img := by
  unfold ownImg ownSet roImg
  iintro ⟨%l, %⟨_, hmem⟩, Hl⟩
  imod sepL_persist_bytes img l $$ Hl with Hl
  ihave #Hall := sepL_persist_all (fun a => iprop(a ↦ₘ□ img a)) l $$ Hl
  imodintro
  imodintro
  iintro %k %hk
  iapply Hall $$ %k %((hmem k).2 hk)

omit I in
/-- A freshly written C string, discarded. -/
theorem strAt_of_owned {p : Nat} {s : String} {img : Nat → BitVec 8} (h : CStrImg img p s) :
    ownImg (GF := GF) (InExt (p, s.toList.length + 1)) img ⊢ |==> strAt p s := by
  iintro H
  imod ownImg_persist _ img $$ H with H
  imodintro
  unfold strAt
  iexists img
  iframe H
  ipureintro; exact h

omit I in
/-- A read-only byte and an exclusively owned image do not share an address. -/
theorem roImg_ownImg_off {S T : Nat → Prop} {img img' : Nat → BitVec 8} {a : Nat}
    (ha : S a) : roImg (GF := GF) S img ∗ ownImg T img' ⊢ ⌜¬ T a⌝ := by
  unfold roImg ownImg ownSet
  iintro ⟨#HS, %l, %⟨_, hmem⟩, Hl⟩
  ihave Ha := HS $$ %a %ha
  iintro %hT
  have hal : a ∈ l := (hmem a).2 hT
  ihave %hn := (show ∀ l : List Nat, a ∈ l → (a ↦ₘ□ img a) ∗ sepL l (fun k => k ↦ₘ img' k) ⊢@{IProp GF}
      ⌜False⌝ from by
    intro l
    induction l with
    | nil => intro h; cases h
    | cons y ys ih =>
      intro h
      rw [sepL_cons]
      rcases List.mem_cons.mp h with rfl | h
      · iintro ⟨Ha, Hy, -⟩
        ihave %hne := memRO_excl_ne a a (img a) (img' a) $$ [Ha Hy]
        · iframe Ha Hy
        ipureintro; exact hne rfl
      · iintro ⟨Ha, -, Hys⟩
        iapply ih h $$ [Ha Hys]
        iframe Ha Hys) l hal $$ [Ha Hl]
  · iframe Ha Hl
  ipureintro; exact hn

/-- Every existing closure object is off a block the caller owns exclusively,
so its pointer is not the block's start. -/
theorem closuresOwn_fresh {p : Nat} {img : Nat → BitVec 8} {mc : NatMap Nat} :
    ∀ (i : Nat) (cs : List ClosureData),
      closuresOwn (GF := GF) i cs ∗ ghost_map_auth I.closName (DFrac.own 1) mc ∗
        ownImg (InExt (p, 16)) img ⊢
      ⌜∀ k, k < cs.length → ∀ q, PartialMap.get? mc (i + k) = some q → q ≠ p⌝
  | _, [] => by iintro _; ipureintro; intro k hk; simp at hk
  | i, cd :: cs => by
    rw [closuresOwn_cons]
    iintro ⟨⟨#Hcd, #Hcs⟩, Hmc, Hown⟩
    ihave %hcs := closuresOwn_fresh (i + 1) cs $$ [Hcs Hmc Hown]
    · iframe Hcs Hmc Hown
    unfold closOwn
    icases Hcd with ⟨%p', %q', %e', %img', #Hat, %⟨hp', -⟩, #Hro, -⟩
    ihave %hoff := roImg_ownImg_off (S := InExt (p', 16)) (a := p') (by unfold InExt; simp) $$ [Hro Hown]
    · iframe Hro Hown
    unfold closAt
    ihave %hlk := ghost_map_lookup $$ Hmc Hat
    ipureintro
    intro k hk q hq
    cases k with
    | zero =>
      rw [Nat.add_zero, hlk] at hq
      cases hq
      intro hpp
      subst hpp
      exact hoff (by unfold InExt; simp)
    | succ k =>
      exact hcs k (by simp at hk; omega) q (by rw [show i + 1 + k = i + (k + 1) by omega]; exact hq)

theorem closuresOwn_snoc (i : Nat) (cs : List ClosureData) (cd : ClosureData) :
    closuresOwn (GF := GF) i cs ∗ closOwn (i + cs.length) cd ⊢ closuresOwn i (cs ++ [cd]) := by
  induction cs generalizing i with
  | nil =>
    simp only [List.nil_append, closuresOwn_cons, closuresOwn_nil, List.length_nil, Nat.add_zero]
    iintro ⟨-, H⟩
    iframe H
  | cons c cs ih =>
    simp only [List.cons_append, closuresOwn_cons, List.length_cons]
    iintro ⟨⟨Hc, Hr⟩, Hd⟩
    iframe Hc
    rw [show i + (cs.length + 1) = i + 1 + cs.length by omega]
    iapply ih (i + 1)
    iframe Hr Hd

/-- **Closure allocation** (`EX_FN`): a filled 16-byte closure object is
discarded to read-only and joins the store as closure `s.closures.size`.
Its pointer is fresh against every existing closure by ownership
(`closuresOwn_fresh`), which maintains `StoreMaps.clos_inj`. -/
theorem storeRepr_allocClosure {s s' : Store} {B : List (Nat × Nat)} {cd : ClosureData}
    {p q e : Nat} {img : Nat → BitVec 8}
    (hcl : s'.closures.toList = s.closures.toList ++ [cd]) (hfr : s'.frames = s.frames)
    (hp : p ≠ 0) (he : e ≠ 0) (hq : imgLE img p 8 = q) (he' : imgLE img (p + 8) 8 = e)
    (hbody : Stmt.stackNeedList cd.body ≤ perCallBudget ∧
      Stmt.bodiesBoundList perCallBudget cd.body = true) :
    storeRepr (GF := GF) N s B ∗ ownImg (InExt (p, 16)) img ∗
        astE q (.fn cd.name cd.params cd.body) ∗ frameAt cd.env e ⊢
      |==> (storeRepr N s' B ∗ closAt s.closures.size p) := by
  unfold storeRepr
  iintro ⟨⟨%mf, %mc, %Bs, Hf, Hc, %⟨hmaps, hB, hbb⟩, Hfr, #Hcl⟩, Hown, #Hast, #Henv⟩
  ihave ⟨⟨-, Hc, Hown⟩, %hfresh⟩ := keep_pure (closuresOwn_fresh 0 s.closures.toList) $$ [Hc Hown]
  · iframe Hcl Hc Hown
  have hnone : PartialMap.get? mc s.closures.size = none := by
    cases h : PartialMap.get? mc s.closures.size with
    | none => rfl
    | some _ => have := (hmaps.closures s.closures.size).1 (by simp [h]); omega
  imod ghost_map_insert_persist (GF := GF) (γ := I.closName) s.closures.size p hnone $$ Hc
    with ⟨Hc, #Hat⟩
  imod ownImg_persist _ img $$ Hown with #Hro
  imodintro
  unfold closAt
  iframe Hat
  iexists mf, PartialMap.insert mc s.closures.size p, Bs
  rw [hcl, hfr]
  iframe Hf Hc Hfr
  have hsize : s'.closures.size = s.closures.size + 1 := by
    rw [← Array.length_toList, ← Array.length_toList, hcl]; simp
  isplitr
  · ipureintro
    refine ⟨⟨fun k => by rw [hfr]; exact hmaps.frames k, fun k => ?_, ?_⟩, hB, ?_⟩
    · rw [hsize, Iris.Std.LawfulPartialMap.get?_insert]
      by_cases hk : s.closures.size = k
      · subst hk; simp
      · simp only [hk, ite_false, hmaps.closures k]; omega
    · intro a b r ha hb
      rw [Iris.Std.LawfulPartialMap.get?_insert] at ha hb
      have hdom : ∀ k r, PartialMap.get? mc k = some r → r ≠ p := fun k r hk => by
        have hlt := (hmaps.closures k).1 (by simp [hk])
        exact hfresh k (by rw [Array.length_toList]; exact hlt) r (by rw [Nat.zero_add]; exact hk)
      by_cases ha' : s.closures.size = a
      · rw [ite_eq_left ha'] at ha
        cases ha
        by_cases hb' : s.closures.size = b
        · exact ha'.symm.trans hb'
        · rw [ite_eq_right hb'] at hb
          exact absurd rfl (hdom b _ hb)
      · rw [ite_eq_right ha'] at ha
        by_cases hb' : s.closures.size = b
        · rw [ite_eq_left hb'] at hb
          cases hb
          exact absurd rfl (hdom a _ ha)
        · rw [ite_eq_right hb'] at hb
          exact hmaps.clos_inj a b r ha hb
    · intro a cd' h
      rw [← Array.getElem?_toList, hcl] at h
      by_cases ha : a < s.closures.toList.length
      · rw [List.getElem?_append_left ha, Array.getElem?_toList] at h
        exact hbb a cd' h
      · rw [List.getElem?_append_right (by omega)] at h
        obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp h
        simp only [List.length_singleton] at hlt
        have hcd : cd' = cd := by
          rw [← heq]
          simp
        subst hcd
        exact hbody
  iapply closuresOwn_snoc 0 s.closures.toList cd
  iframe Hcl
  rw [Nat.zero_add, Array.length_toList]
  unfold closOwn closAt
  iexists p, q, e, img
  iframe Hat Hro Hast Henv
  ipureintro
  exact ⟨hp, he, hq, he'⟩

/-! ## Two owners (INTERP_DESIGN.md §10.7) -/

omit I in
/-- Two exclusively owned images join into one over the union. -/
theorem ownImg_join (S T : Nat → Prop) (f g : Nat → BitVec 8) :
    ownImg (GF := GF) S f ∗ ownImg T g ⊢
      ∃ h, ownImg (fun a => S a ∨ T a) h ∗ ⌜∀ a, S a → ¬ T a⌝ := by
  iintro ⟨HS, HT⟩
  ihave ⟨⟨HS, HT⟩, %hd⟩ := keep_pure (ownSet_disj S T f g) $$ [HS HT]
  · iframe HS HT
  classical
  iexists (fun a => if S a then f a else g a)
  isplitl [HS HT]
  · iapply ownSet_join S T _ hd
    isplitl [HS]
    · iapply ownSet_congr (Φ := fun a => a ↦ₘ f a) (fun a ha => by simp [ha]) $$ HS
    · iapply ownSet_congr (Φ := fun a => a ↦ₘ g a) (fun a ha => by simp [show ¬ S a from fun hs => hd a hs ha]) $$ HT
  · ipureintro; exact hd

omit G in
theorem blocksCover_append (bl bl' : List (Nat × Nat)) (a : Nat) :
    BlocksCover (bl ++ bl') a ↔ BlocksCover bl a ∨ BlocksCover bl' a := by
  unfold BlocksCover
  simp only [List.mem_append]
  constructor
  · rintro ⟨b, hb | hb, ha⟩
    · exact .inl ⟨b, hb, ha⟩
    · exact .inr ⟨b, hb, ha⟩
  · rintro (⟨b, hb, ha⟩ | ⟨b, hb, ha⟩)
    · exact ⟨b, .inl hb, ha⟩
    · exact ⟨b, .inr hb, ha⟩

/-- A frame owns every byte of its blocks, which are pairwise disjoint. -/
theorem frameOwn_cover (fa : Addr) (f : Frame) (bl : List (Nat × Nat)) :
    frameOwn (GF := GF) N fa f bl ⊢
      ∃ img, ownImg (BlocksCover bl) img ∗ ⌜bl.Pairwise ExtDisj⌝ := by
  unfold frameOwn frameBody
  iintro ⟨%Gm, %hbl, -, %img, %hlay, Hown, -⟩
  subst hbl
  iexists img
  iframe Hown
  ipureintro; exact hlay.disjoint

/-- All frames together own the bytes of all their blocks, pairwise disjoint. -/
theorem framesOwn_cover :
    ∀ (i : Nat) (fs : List Frame) (Bs : List (List (Nat × Nat))),
      framesOwn (GF := GF) N i fs Bs ⊢
        ∃ img, ownImg (BlocksCover Bs.flatten) img ∗ ⌜Bs.flatten.Pairwise ExtDisj⌝
  | _, [], [] => by
    iintro _
    iexists (fun _ => 0)
    isplitl []
    · unfold ownImg ownSet
      iexists []
      simp only [sepL_nil]
      isplitl []
      · ipureintro; exact ⟨List.nodup_nil, fun a => by simp [BlocksCover]⟩
      · iempintro
    · ipureintro; simp
  | _, [], _ :: _ => by rw [framesOwn_nil_cons]; exact false_elim
  | _, _ :: _, [] => by rw [framesOwn_cons_nil]; exact false_elim
  | i, f :: fs, bl :: Bs => by
    rw [framesOwn_cons]
    iintro ⟨Hf, Hr⟩
    ihave ⟨%img1, H1, %hp1⟩ := frameOwn_cover N i f bl $$ Hf
    ihave ⟨%img2, H2, %hp2⟩ := framesOwn_cover (i + 1) fs Bs $$ Hr
    ihave ⟨%img, H, %hd⟩ := ownImg_join _ _ img1 img2 $$ [H1 H2]
    · iframe H1 H2
    iexists img
    isplitl [H]
    · iapply ownSet_iff _ (fun a => by rw [List.flatten_cons, blocksCover_append]) $$ H
    · ipureintro
      rw [List.flatten_cons, List.pairwise_append]
      refine ⟨hp1, hp2, fun b hb b' hb' a ha ha' => hd a ⟨b, hb, ha⟩ ⟨b', hb', ha'⟩⟩

/-- The store's blocks are pairwise disjoint. -/
theorem storeRepr_blocks_disjoint {s : Store} {B : List (Nat × Nat)} :
    storeRepr (GF := GF) N s B ⊢ ⌜B.Pairwise ExtDisj⌝ := by
  unfold storeRepr
  iintro ⟨%mf, %mc, %Bs, -, -, %⟨-, hB, -⟩, Hfr, -⟩
  ihave ⟨%img, -, %h⟩ := framesOwn_cover N 0 s.frames.toList Bs $$ Hfr
  ipureintro; rw [hB]; exact h

/-- **Store vs heap.** No byte of a store block is in the allocator's
footprint: every store block is covered by live extents (with `B ⊆ H`, its
own entry). A store owning a block the allocator also owns is refuted. -/
theorem storeRepr_blocks_off_heap {s : Store} {B : List (Nat × Nat)} {L : DlLayout}
    {H : List (Nat × Nat)} :
    storeRepr (GF := GF) N s B ∗ isHeap L H ⊢ ⌜∀ b ∈ B, ∀ a, InExt b a → ¬ heapFoot L H a⌝ := by
  unfold storeRepr isHeap
  iintro ⟨⟨%mf, %mc, %Bs, -, -, %⟨-, hB, -⟩, Hfr, -⟩, %img, -, Hheap⟩
  ihave ⟨%img', Hown, -⟩ := framesOwn_cover N 0 s.frames.toList Bs $$ Hfr
  ihave %hd := ownSet_disj _ _ img' img $$ [Hown Hheap]
  · iframe Hown Hheap
  ipureintro
  intro b hb a ha
  exact hd a ⟨b, hB ▸ hb, ha⟩

/-- The same at the level of the world, for either regime. -/
theorem world_blocks_off_heap {N : NativeAddrs} {L : DlLayout} {Room : RoomPred} {inp : Nat}
    {ρ : Regime} {st : St} {d : Nat} :
    world (GF := GF) N L Room inp ρ st d ⊢
      ∃ (H B : List (Nat × Nat)), ⌜(∀ b ∈ B, b ∈ H) ∧ B.Pairwise ExtDisj ∧
        ∀ b ∈ B, ∀ a, InExt b a → ¬ heapFoot L H a⌝ := by
  unfold world worldE
  iintro ⟨%H, %B, Hh, Hs, -, -, -, %hBH⟩
  ihave Hh := heapRes_isHeap L Room ρ H $$ Hh
  ihave ⟨Hs, %hdisj⟩ := keep_pure (storeRepr_blocks_disjoint N) $$ Hs
  ihave %hoff := storeRepr_blocks_off_heap N $$ [Hs Hh]
  · iframe Hs Hh
  iexists H, B
  ipureintro
  exact ⟨hBH, hdisj, hoff⟩

end Store

end VsaIris.Interp
