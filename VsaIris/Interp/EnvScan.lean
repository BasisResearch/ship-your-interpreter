import VsaIris.Interp.EnvScanCore

/-!
# The scan and the parent chain of `env_get`/`env_set`, at the Iris level

`env_get` and `env_set` are one code shape at two addresses (`EnvScanCore.lean`):
a prologue, a walk up the parent chain, in each frame a scan of the names
with a `strcmp` call per name, and a hit arm that differs (copy the value out,
or write it in). A `ScanSite` records one address's PCs and its first-order
spans (`EnvGetSpans.lean`, generated `EnvSetSpans.lean`); the lemmas here are
proved once over it:

* `scan_frame`: one frame's scan, an induction on the names left, taking the
  `strcmp` call against `strcmpSpec`; it ends at the frame's end or at the hit
  PC with the first match;
* `scan_tail`, `scan_chain`: the walk up the chain, a strong induction on the
  frame address (parents are older, `StoreInvariant.parents`); each frame is
  opened with `storeRepr_open`, closed unchanged on a miss, and handed open to
  the hit continuation;
* `scan_entry`: the ABI entry — the register file (`regsOf_entry`), the stack
  frame and value slot, the prologue span — into the chain;
* `scan_exit`: the ABI return from a span's register file.

The chain carries its path from the start frame (`ChainFrom`: each step a
frame without the name), from which `env_get` reads `Store.get?`
(`ChainFrom.look`) and `env_set` reads `Store.set?`.
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

/-! ## One frame's scan -/

section Scan

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

omit I in
/-- An element of a persistent list over `zipIdx`. -/
theorem sepL_zipIdx_get {α} (Φ : α × Nat → IProp GF) [∀ x, Persistent (Φ x)] (l : List α)
    {i : Nat} (hi : i < l.length) : sepL l.zipIdx Φ ⊢ Φ (l[i], i) := by
  iintro H
  ihave #Hall := sepL_persist_all Φ l.zipIdx $$ H
  iapply Hall $$ %(l[i], i) %(by rw [List.mem_zipIdx_iff_getElem?]; simp)

/-- Binding `i` of a frame: its name string and its value's meaning. -/
theorem bindings_get (N : NativeAddrs) (img : Nat → BitVec 8) (pn pv : Nat)
    (vars : List (String × Value)) {i : Nat} (hi : i < vars.length) :
    bindings (GF := GF) N img pn pv vars ⊢
      strAt (imgLE img (pn + 8 * i) 8) vars[i].1 ∗ valImg N img (pv + 24 * i) vars[i].2 := by
  unfold bindings
  exact sepL_zipIdx_get _ vars hi

/-- The constants of one `env_get` call: entry `sp`, return address, the
name, the output slot, the callee-saved values. -/
structure GetCall where
  s : BitVec 64
  r : BitVec 64
  pn : BitVec 64
  out : BitVec 64
  x : String
  saved : List (Nat × BitVec 64)
  /-- The value slot's bytes at the entry. -/
  so : Nat → BitVec 8

/-- What the entry guarantees about a call's constants. -/
structure GetCall.OK (C : GetCall) : Prop where
  sp : EnvSp C.s envGetNeed
  slot : SlotWin C.out.toNat
  ra : C.r.toNat % 4 = 0
  saved : C.saved.map Prod.fst = getSaved
  sep : C.out.toNat + 24 ≤ C.s.toNat - 64 ∨ C.s.toNat ≤ C.out.toNat

/-- The state inside frame `G` (image `img`, `n` bindings) between spans. -/
structure InFrame (C : GetCall) (G : FrameGeom) (n : Nat) (img : Nat → BitVec 8)
    (R : Nat → BitVec 64) (Mt : Mem) : Prop where
  stack : GetStack C.s.toNat C.r (pairVal C.saved) R Mt
  name : R 19 = C.pn
  out : R 21 = C.out
  env : (R 20).toNat = G.e
  lay : FrameLayout (imgM Mt) G n
  img : ∀ a, frameS G a → imgM Mt a = img a
  sepOut : ∀ a, frameS G a → a < C.out.toNat ∨ C.out.toNat + 24 ≤ a
  sepStk : ∀ a, frameS G a → a < C.s.toNat - 64 ∨ C.s.toNat ≤ a
  slot : ∀ a, C.out.toNat ≤ a → a < C.out.toNat + 24 → imgM Mt a = C.so a

/-- The frame state reads only `sp`, `s3`, `s4`, `s5`, `s6`. -/
theorem InFrame.regs {C : GetCall} {G : FrameGeom} {n : Nat} {img : Nat → BitVec 8}
    {R R' : Nat → BitVec 64} {Mt : Mem} (h : InFrame C G n img R Mt) (hs : 64 ≤ C.s.toNat)
    (hk : ∀ k, k = 2 ∨ k = 19 ∨ k = 20 ∨ k = 21 ∨ k = 22 → R' k = R k) :
    InFrame C G n img R' Mt where
  stack := h.stack.congr (hk 2 (by omega)) (hk 22 (by omega)) (fun _ _ _ => rfl) hs
  name := (hk 19 (by omega)).trans h.name
  out := (hk 21 (by omega)).trans h.out
  env := by rw [hk 20 (by omega)]; exact h.env
  lay := h.lay
  img := h.img
  sepOut := h.sepOut
  sepStk := h.sepStk
  slot := h.slot

theorem take_succ_all {l : List (String × Value)} {i : Nat} {x : String} (hi : i < l.length)
    (h : ∀ p ∈ l.take i, p.1 ≠ x) (hne : l[i].1 ≠ x) : ∀ p ∈ l.take (i + 1), p.1 ≠ x := by
  intro p hp
  rw [List.take_succ, List.getElem?_eq_getElem hi] at hp
  simp only [Option.toList_some, List.mem_append, List.mem_singleton] at hp
  rcases hp with hp | rfl
  · exact h p hp
  · exact hne

/-- A word of an image agreeing with another on its bytes. -/
theorem imgW_agree {f g : Nat → BitVec 8} {a : Nat} (h : ∀ j, j < 8 → f (a + j) = g (a + j)) :
    imgW f a = imgW g a := by
  unfold imgW; rw [imgLE_congr h]

/-- Two intervals, one of which misses every byte of the other, are apart. -/
theorem interval_apart {a n b m : Nat} (hn : 0 < n) (hm : 0 < m)
    (h : ∀ c, b ≤ c → c < b + m → c < a ∨ a + n ≤ c) : a + n ≤ b ∨ b + m ≤ a := by
  apply Classical.byContradiction
  intro hc
  have := h (max a b) (by omega) (by omega)
  omega

end Scan


/-! ## Opening and closing a frame -/

section Frames

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- The frame layout reads only the frame's bytes. -/
theorem FrameLayout.congr {img img' : Nat → BitVec 8} {G : FrameGeom} {n : Nat}
    (h : FrameLayout img G n) (hag : ∀ a, frameS G a → img' a = img a) : FrameLayout img' G n := by
  have hs := h.sblk
  have e : ∀ o w, o + w ≤ 32 → imgLE img' (G.e + o) w = imgLE img (G.e + o) w := fun o w how =>
    imgLE_congr fun j hj => hag _ (by unfold frameS InExt; exact .inl ⟨by omega, by omega⟩)
  exact { h with
    count := by have := e 0 4 (by omega); simp at this; rw [this]; exact h.count
    cap := by rw [e 4 4 (by omega)]; exact h.cap
    names := by rw [e 8 8 (by omega)]; exact h.names
    vals := by rw [e 16 8 (by omega)]; exact h.vals
    parent := by rw [e 24 8 (by omega)]; exact h.parent }

/-- The store's pure part. -/
theorem storeRepr_pure (N : NativeAddrs) (s : Store) (B : List (Nat × Nat)) :
    storeRepr (GF := GF) N s B ⊢ ⌜Vsa.Sim.StoreInvariant s⌝ := by
  unfold storeRepr
  iintro ⟨%mf, %mc, %Bs, -, -, %hp, -, -⟩
  ipureintro; exact hp.inv

/-- **Open one frame for reading**: its image comes out, and the same image
closes it again (the store unchanged). -/
theorem storeRepr_openRead (N : NativeAddrs) {s : Store} {B : List (Nat × Nat)} {fa e : Nat} :
    storeRepr (GF := GF) N s B ∗ frameAt fa e ⊢
      ∃ (f : Frame) (Gm : FrameGeom) (img : Nat → BitVec 8),
        ⌜s.frames[fa]? = some f ∧ Gm.e = e ∧ FrameLayout img Gm f.vars.length ∧
          Vsa.Sim.StoreInvariant s⌝ ∗
        ownImg (BlocksCover Gm.blocks) img ∗ bindings N img Gm.pn Gm.pv f.vars ∗
        parentAt f.parent Gm.par ∗ (ownImg (BlocksCover Gm.blocks) img -∗ storeRepr N s B) := by
  iintro ⟨Hs, #He⟩
  ihave ⟨Hs, %hinv⟩ := keep_pure (storeRepr_pure N s B) $$ Hs
  ihave ⟨⟨Hs, -⟩, %hlt⟩ := keep_pure (storeRepr_frameAt N (s := s) (B := B) (fa := fa) (e := e))
    $$ [Hs He]
  · iframe Hs He
  have hf : s.frames[fa]? = some s.frames[fa] := Array.getElem?_eq_getElem hlt
  ihave ⟨%bl, %B₁, %B₂, %hB, Hf, Hc⟩ := storeRepr_open N hf $$ Hs
  unfold frameOwn frameBody
  icases Hf with ⟨%Gm, %hbl, #HGe, %img, %hlay, Hown, #Hb, #Hp⟩
  ihave %hGe := frameAt_agree fa Gm.e e $$ [HGe He]
  · iframe HGe He
  iexists s.frames[fa], Gm, img
  iframe Hown Hb Hp
  isplitr
  · ipureintro; exact ⟨hf, hGe, hlay, hinv⟩
  iintro Hown
  rw [hB, hbl]
  iapply Hc $$ %s %(s.frames[fa]) %Gm.blocks
    %⟨rfl, by rw [← Array.getElem_toList (h := hlt)]; exact (List.set_getElem_self _).symm, hinv⟩
  iexists Gm
  iframe HGe
  isplitr
  · ipureintro; rfl
  iexists img
  iframe Hown Hb Hp
  ipureintro; exact hlay

omit I in
/-- **Join a frame's blocks** to `env_get`'s own bytes, at one tracking memory. -/
theorem get_join (s out : Nat) (Gm : FrameGeom) (Mt : Mem) (img : Nat → BitVec 8) :
    ownSet (GF := GF) (baseS s out) (fun a => a ↦ₘ imgM Mt a) ∗ ownImg (BlocksCover Gm.blocks) img ⊢
      ∃ Mt' : Mem, ⌜(∀ a, baseS s out a → imgM Mt' a = imgM Mt a) ∧
          (∀ a, frameS Gm a → imgM Mt' a = img a) ∧ (∀ a, frameS Gm a → ¬ baseS s out a)⌝ ∗
        ownSet (getS s out Gm) (fun a => a ↦ₘ imgM Mt' a) := by
  iintro ⟨HB, HF⟩
  ihave ⟨⟨HB, HF⟩, %hd⟩ := keep_pure (ownSet_disj (baseS s out) (BlocksCover Gm.blocks) (imgM Mt) img)
    $$ [HB HF]
  · iframe HB HF
  ihave H := ownSet_glue _ _ (imgM Mt) img hd $$ [HB HF]
  · iframe HB HF
  ihave H := ownSet_iff (T := getS s out Gm) _ (fun a => by
    unfold getS; rw [frameS_iff]) $$ H
  ihave ⟨%Mt', %hag, H⟩ := ownSet_tracked _ _ $$ H
  iexists Mt'
  iframe H
  ipureintro
  refine ⟨fun a ha => ?_, fun a ha => ?_, fun a ha hb => hd a hb ((frameS_iff Gm a).1 ha)⟩
  · rw [hag a (.inl ha)]; simp [glue, ha]
  · have hb : ¬ baseS s out a := fun hb => hd a hb ((frameS_iff Gm a).1 ha)
    rw [hag a (.inr ha)]; simp [glue, hb]

omit I in
/-- **Split a frame's blocks** back off, at the frame's own image. -/
theorem get_split {s out : Nat} {Gm : FrameGeom} {Mt : Mem} {img : Nat → BitVec 8}
    (hd : ∀ a, frameS Gm a → ¬ baseS s out a) (himg : ∀ a, frameS Gm a → imgM Mt a = img a) :
    ownSet (GF := GF) (getS s out Gm) (fun a => a ↦ₘ imgM Mt a) ⊢
      ownSet (baseS s out) (fun a => a ↦ₘ imgM Mt a) ∗ ownImg (BlocksCover Gm.blocks) img := by
  iintro H
  unfold getS
  ihave ⟨HB, HF⟩ := ownSet_unglue (baseS s out) (frameS Gm) _ (fun a hb hf => hd a hf hb) $$ H
  iframe HB
  ihave HF := ownSet_congr (Ψ := fun a => a ↦ₘ img a) (fun a ha => by rw [himg a ha]) $$ HF
  iapply ownSet_iff _ (fun a => frameS_iff Gm a) $$ HF

end Frames

/-! ## A site: one address of the scan code -/

/-- **One address of the scan code**: its PCs, its `jal strcmp` site, and its
first-order spans (`EnvGetSpans.lean` for `env_get`, the generated
`EnvSetSpans.lean` for `env_set`). The hit arm is not part of it. -/
structure ScanSite (live : Nat → Prop) where
  entry : BitVec 64
  head : BitVec 64
  scan : BitVec 64
  jal : Nat
  jcode : List (BitVec 8)
  hit : BitVec 64
  tail : BitVec 64
  epi : BitVec 64
  jexec : JalExec (vsaModel live) jal jcode strcmpPC
  jtext : ∀ p ∈ codeFoot jal jcode, (p.1, p.2.2) ∈ envText
  jal4 : (BitVec.ofNat 64 (jal + 4)).toNat % 4 = 0
  sEntry : ∀ {s out : Nat} {r : BitVec 64} {sv R : Nat → BitVec 64} {so : Nat → BitVec 8}
    {Mt : Mem}, htifLo + 16 + 64 ≤ s → s ≤ 0x100000000 → s % 16 = 0 → GetEntry s r sv R →
    (∀ a, (R 12).toNat ≤ a → a < (R 12).toNat + 24 → imgM Mt a = so a) →
    ((R 12).toNat + 24 ≤ s - 64 ∨ s ≤ (R 12).toNat) →
    Span live (baseS s out) entry R Mt
      (fun pc' R' Mt' => pc' = head ∧ GetHead s r sv so (R 10) (R 11) (R 12) R' Mt')
  sHead : ∀ {s out n : Nat} {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem},
    FrameLayout (imgM Mt) G n → (R 20).toNat = G.e →
    Span live (getS s out G) head R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧
        ((n = 0 ∧ pc' = tail ∧ ∀ k, k ≠ 18 → R' k = R k) ∨
         (0 < n ∧ pc' = scan ∧ HeadScan G n R R')))
  sLoad : ∀ {s out n i : Nat} {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem},
    FrameLayout (imgM Mt) G n → i < n → (R 9).toNat = G.pn + 8 * i →
    Span live (getS s out G) scan R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧ pc' = BitVec.ofNat 64 jal ∧
        R' 10 = imgW (imgM Mt) (G.pn + 8 * i) ∧ R' 11 = R 19 ∧
        ∀ k, k ≠ 10 → k ≠ 11 → R' k = R k)
  sCmp : ∀ {s out n i : Nat} {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem},
    i < n → n < 2 ^ 31 → R 8 = BitVec.ofNat 64 i → R 18 = BitVec.ofNat 64 n →
    Span live (getS s out G) (BitVec.ofNat 64 (jal + 4)) R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧
        ((R 10 ≠ 0#64 ∧ i + 1 < n ∧ pc' = scan ∧ CmpNext i R R') ∨
         (R 10 ≠ 0#64 ∧ i + 1 = n ∧ pc' = tail ∧ CmpNext i R R') ∨
         (R 10 = 0#64 ∧ pc' = hit ∧ R' = R)))
  sParent : ∀ {s out n : Nat} {G : FrameGeom} {R : Nat → BitVec 64} {Mt : Mem},
    FrameLayout (imgM Mt) G n → (R 20).toNat = G.e →
    Span live (getS s out G) tail R Mt
      (fun pc' R' Mt' => Mt' = Mt ∧ (∀ k, k ≠ 10 → k ≠ 20 → R' k = R k) ∧
        ((G.par ≠ 0 ∧ pc' = head ∧ R' 20 = BitVec.ofNat 64 G.par) ∨
         (G.par = 0 ∧ pc' = epi ∧ R' 10 = 0#64)))
  sEpi : ∀ {s out : Nat} {G : FrameGeom} {r : BitVec 64} {sv R : Nat → BitVec 64} {Mt : Mem},
    htifLo + 16 + 64 ≤ s → s ≤ 0x100000000 → r.toNat % 4 = 0 → GetStack s r sv R Mt →
    Span live (getS s out G) epi R Mt
      (fun pc' R' Mt' => pc' = r ∧ Mt' = Mt ∧ GetRet s r sv (R 10) R')

/-- The first match `j` of a frame, as `FirstMatch`. -/
theorem firstMatch_of_index {vars : List (String × Value)} {x : String} {v : Value} {j : Nat}
    (hj : vars[j]? = some (x, v)) (hne : ∀ p ∈ vars.take j, p.1 ≠ x) : FirstMatch vars x v := by
  have hlt : j < vars.length := by
    rcases Nat.lt_or_ge j vars.length with h | h
    · exact h
    · simp [List.getElem?_eq_none h] at hj
  refine ⟨vars.take j, vars.drop (j + 1), ?_, hne⟩
  have hvj : vars[j] = (x, v) := by simpa [List.getElem?_eq_getElem hlt] using hj
  conv => lhs; rw [← List.take_append_drop j vars, List.drop_eq_getElem_cons hlt]
  rw [hvj]

/-! ## The chain's path -/

/-- The frames the walk reaches from `fa` looking for `x`: `fa`, and the
parent of every reached frame without `x`. -/
inductive ChainFrom (st : Store) (x : String) (fa : Addr) : Addr → Prop where
  | refl : ChainFrom st x fa fa
  | step {a p : Addr} {f : Frame} : ChainFrom st x fa a → st.frames[a]? = some f →
      FrameMiss f.vars x → f.parent = some p → ChainFrom st x fa p

/-- Along the path, the lookup does not change. -/
theorem ChainFrom.look {st : Store} (hps : StoreParents st) {x : String} {fa a : Addr}
    (h : ChainFrom st x fa a) : look st fa x = look st a x := by
  induction h with
  | refl => rfl
  | step _ hf hm hp ih => exact ih.trans (look_parent hps hf hm hp)

section Open

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- **Open one frame**, keeping `storeRepr_open`'s closer for any frame. -/
theorem storeRepr_openAt (N : NativeAddrs) {s : Store} {B : List (Nat × Nat)} {fa e : Nat} :
    storeRepr (GF := GF) N s B ∗ frameAt fa e ⊢
      ∃ (f : Frame) (Gm : FrameGeom) (img : Nat → BitVec 8) (B₁ B₂ : List (Nat × Nat)),
        ⌜s.frames[fa]? = some f ∧ Gm.e = e ∧ FrameLayout img Gm f.vars.length ∧
          Vsa.Sim.StoreInvariant s ∧ B = B₁ ++ Gm.blocks ++ B₂⌝ ∗
        ownImg (BlocksCover Gm.blocks) img ∗ bindings N img Gm.pn Gm.pv f.vars ∗
        parentAt f.parent Gm.par ∗ frameAt fa Gm.e ∗
        (∀ (s' : Store) (f' : Frame) (bl' : List (Nat × Nat)),
          ⌜s'.closures = s.closures ∧ s'.frames.toList = s.frames.toList.set fa f' ∧
            Vsa.Sim.StoreInvariant s'⌝ -∗
          frameOwn N fa f' bl' -∗ storeRepr N s' (B₁ ++ bl' ++ B₂)) := by
  iintro ⟨Hs, #He⟩
  ihave ⟨Hs, %hinv⟩ := keep_pure (storeRepr_pure N s B) $$ Hs
  ihave ⟨⟨Hs, -⟩, %hlt⟩ := keep_pure (storeRepr_frameAt N (s := s) (B := B) (fa := fa) (e := e))
    $$ [Hs He]
  · iframe Hs He
  have hf : s.frames[fa]? = some s.frames[fa] := Array.getElem?_eq_getElem hlt
  ihave ⟨%bl, %B₁, %B₂, %hB, Hf, Hc⟩ := storeRepr_open N hf $$ Hs
  unfold frameOwn frameBody
  icases Hf with ⟨%Gm, %hbl, #HGe, %img, %hlay, Hown, #Hb, #Hp⟩
  ihave %hGe := frameAt_agree fa Gm.e e $$ [HGe He]
  · iframe HGe He
  iexists s.frames[fa], Gm, img, B₁, B₂
  iframe Hown Hb Hp HGe Hc
  ipureintro; exact ⟨hf, hGe, hlay, hinv, hbl ▸ hB⟩

/-- **Close a frame unchanged.** -/
theorem storeRepr_closeSame (N : NativeAddrs) {s : Store} {fa : Addr} {f : Frame}
    {Gm : FrameGeom} {img : Nat → BitVec 8} {B₁ B₂ : List (Nat × Nat)}
    (hf : s.frames[fa]? = some f) (hinv : Vsa.Sim.StoreInvariant s)
    (hlay : FrameLayout img Gm f.vars.length) :
    (∀ (s' : Store) (f' : Frame) (bl' : List (Nat × Nat)),
        ⌜s'.closures = s.closures ∧ s'.frames.toList = s.frames.toList.set fa f' ∧
          Vsa.Sim.StoreInvariant s'⌝ -∗
        frameOwn N fa f' bl' -∗ storeRepr N s' (B₁ ++ bl' ++ B₂)) ∗
      ownImg (BlocksCover Gm.blocks) img ∗ bindings N img Gm.pn Gm.pv f.vars ∗
      parentAt f.parent Gm.par ∗ frameAt fa Gm.e ⊢
      storeRepr (GF := GF) N s (B₁ ++ Gm.blocks ++ B₂) := by
  have hlt : fa < s.frames.size := by
    rcases Nat.lt_or_ge fa s.frames.size with h | h
    · exact h
    · simp [Array.getElem?_eq_none h] at hf
  have hfa : s.frames[fa] = f := by simpa [Array.getElem?_eq_getElem hlt] using hf
  iintro ⟨Hc, Hown, #Hb, #Hp, #HGe⟩
  iapply Hc $$ %s %f %Gm.blocks
    %⟨rfl, by rw [← hfa, ← Array.getElem_toList (h := hlt)]; exact (List.set_getElem_self _).symm,
      hinv⟩
  unfold frameOwn frameBody
  iexists Gm
  iframe HGe
  isplitr
  · ipureintro; rfl
  iexists img
  iframe Hown Hb Hp
  ipureintro; exact hlay

end Open

section ScanLoop

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- A name slot of the frame is its own bytes: in the names block. -/
theorem frameS_name {img : Nat → BitVec 8} {G : FrameGeom} {n i j : Nat}
    (h : FrameLayout img G n) (hi : i < n) (hj : j < 8) : frameS G (G.pn + 8 * i + j) := by
  obtain ⟨hcap, h1, h2, -, -, -, -⟩ := h.slot hi
  unfold frameS InExt
  exact .inr ⟨hcap, .inl ⟨by omega, by omega⟩⟩

theorem frameS_val {img : Nat → BitVec 8} {G : FrameGeom} {n i j : Nat}
    (h : FrameLayout img G n) (hi : i < n) (hj : j < 24) : frameS G (G.pv + 24 * i + j) := by
  obtain ⟨hcap, -, -, h1, h2, -, -⟩ := h.slot hi
  unfold frameS InExt
  exact .inr ⟨hcap, .inr ⟨by omega, by omega⟩⟩

/-- **One frame's scan**, from name `i` on. It ends at the frame's end
(`Sx.tail`, every name differs from `x`) or at the hit (`Sx.hit`) with the
first match `j`. -/
theorem scan_frame (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (Sx : ScanSite live) (N : NativeAddrs) (C : GetCall) (hC : C.OK)
    {f : Frame} {G : FrameGeom} {img : Nat → BitVec 8} :
    ∀ m i R Mt, f.vars.length - i = m → i < f.vars.length →
      (∀ p ∈ f.vars.take i, p.1 ≠ C.x) →
      R 8 = BitVec.ofNat 64 i → (R 9).toNat = G.pn + 8 * i →
      R 18 = BitVec.ofNat 64 f.vars.length → InFrame C G f.vars.length img R Mt →
      textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗ strAt C.pn.toNat C.x ∗
        bindings N img G.pn G.pv f.vars ∗ VsaIris.PC ↦ᵣ Sx.scan ∗ regsOf gprs R ∗
        ownSet (getS C.s.toNat C.out.toNat G) (fun a => a ↦ₘ imgM Mt a) ∗
        ((∀ R' Mt', ⌜InFrame C G f.vars.length img R' Mt' ∧ FrameMiss f.vars C.x⌝ -∗
            VsaIris.PC ↦ᵣ Sx.tail -∗ regsOf gprs R' -∗
            ownSet (getS C.s.toNat C.out.toNat G) (fun a => a ↦ₘ imgM Mt' a) -∗ Wp.W Φ) ∧
         (∀ (j : Nat) (v : Value) R' Mt', ⌜f.vars[j]? = some (C.x, v) ∧
            (∀ p ∈ f.vars.take j, p.1 ≠ C.x) ∧ InFrame C G f.vars.length img R' Mt' ∧
            R' 8 = BitVec.ofNat 64 j⌝ -∗
            VsaIris.PC ↦ᵣ Sx.hit -∗ regsOf gprs R' -∗
            ownSet (getS C.s.toNat C.out.toNat G) (fun a => a ↦ₘ imgM Mt' a) -∗ Wp.W Φ))
      ⊢ Wp.W Φ := by
  intro m
  induction m with
  | zero => intro i R Mt hm hi; omega
  | succ m ih =>
    intro i R Mt hm hi hne h8 h9 h18 hF
    iintro ⟨#Ht, #Hgp, #Hcmp, #Hx, #Hb, Hpc, HR, HS, HKK⟩
    iapply wp_span Wp (Sx.sLoad (s := C.s.toNat) (out := C.out.toNat) hF.lay hi h9)
    iframe Ht Hgp Hpc HR HS
    iintro %pc1 %R1 %Mt1 %⟨rfl, rfl, h10, h11, hk1⟩ Hpc HR HS
    ihave ⟨#Hname, #Hval⟩ := bindings_get N img G.pn G.pv f.vars hi $$ Hb
    have hname : (R1 10).toNat = imgLE img (G.pn + 8 * i) 8 := by
      rw [h10, imgW_toNat]
      exact imgLE_congr fun j hj => hF.img _ (frameS_name hF.lay hi hj)
    iapply wp_call_strcmp Wp Sx.jexec Sx.jal4 (xi := (f.vars[i]).1) (x := C.x)
    isplitl []
    · iapply instrAt_of_text Sx.jtext $$ Ht
    iframe Hcmp Hpc HR
    isplitl []
    · rw [hname]; iexact Hname
    isplitl []
    · rw [h11, hF.name]; iexact Hx
    iintro %R2 %⟨hres, h1, hk2⟩ Hpc HR
    have k2 : ∀ k, k ∉ strcmpKs → k ≠ 10 → k ≠ 11 → R2 k = R k := fun k hk h10 h11 =>
      (hk2 k hk).trans (hk1 k h10 h11)
    have h8' : R2 8 = BitVec.ofNat 64 i := (k2 8 (by decide) (by decide) (by decide)).trans h8
    have h18' : R2 18 = BitVec.ofNat 64 f.vars.length :=
      (k2 18 (by decide) (by decide) (by decide)).trans h18
    have hn := hF.lay.count_lt
    iapply wp_span Wp (Sx.sCmp (s := C.s.toNat) (out := C.out.toNat) (G := G) hi hn h8' h18')
    iframe Ht Hgp Hpc HR HS
    iintro %pc3 %R3 %Mt3 %⟨rfl, hcase⟩ Hpc HR HS
    have hs64 : 64 ≤ C.s.toNat := by have := hC.sp.lo; unfold htifLo at this; omega
    rcases hcase with ⟨hne0, hlt, rfl, hnx⟩ | ⟨hne0, heq, rfl, hnx⟩ | ⟨heq0, rfl, hR3⟩
    · -- the next name
      have hxi : (f.vars[i]).1 ≠ C.x := fun h => hne0 (hres.2 h)
      have k3 : ∀ k, k ∉ strcmpKs → k ≠ 10 → k ≠ 11 → k ≠ 8 → k ≠ 9 → R3 k = R k :=
        fun k hk h10 h11 h8 h9 => (hnx.keep k h8 h9).trans (k2 k hk h10 h11)
      obtain ⟨-, -, hn2, -, -, hnw, -⟩ := hF.lay.slot hi
      have h9' : (R3 9).toNat = G.pn + 8 * (i + 1) := by
        rw [hnx.cur, k2 9 (by decide) (by decide) (by decide), BitVec.toNat_add, h9]
        have := hnw.hi; simp; omega
      iapply ih (i + 1) R3 _ (by omega) hlt (take_succ_all hi hne hxi) hnx.idx h9'
        ((hnx.keep 18 (by decide) (by decide)).trans h18')
        (hF.regs hs64 fun k hk => by
          rcases hk with rfl | rfl | rfl | rfl | rfl <;>
            exact k3 _ (by decide) (by decide) (by decide) (by decide) (by decide))
      iframe Ht Hgp Hcmp Hx Hb Hpc HR HS HKK
    · -- the frame is exhausted
      have hxi : (f.vars[i]).1 ≠ C.x := fun h => hne0 (hres.2 h)
      have k3 : ∀ k, k ∉ strcmpKs → k ≠ 10 → k ≠ 11 → k ≠ 8 → k ≠ 9 → R3 k = R k :=
        fun k hk h10 h11 h8 h9 => (hnx.keep k h8 h9).trans (k2 k hk h10 h11)
      have hmiss : FrameMiss f.vars C.x := by
        intro p hp
        have := take_succ_all hi hne hxi
        rw [List.take_of_length_le (by omega)] at this
        exact this p hp
      ihave Kex := and_elim_l $$ HKK
      iapply Kex $$ %R3 %_ %⟨hF.regs hs64 fun k hk => by
          rcases hk with rfl | rfl | rfl | rfl | rfl <;>
            exact k3 _ (by decide) (by decide) (by decide) (by decide) (by decide), hmiss⟩ Hpc HR HS
    · -- the hit
      subst hR3
      have hx : (f.vars[i]).1 = C.x := hres.1 heq0
      ihave Khit := and_elim_r $$ HKK
      iapply Khit $$ %i %((f.vars[i]).2) %R3 %_ %⟨?_, hne, hF.regs hs64 fun k hk => by
          rcases hk with rfl | rfl | rfl | rfl | rfl <;>
            exact k2 _ (by decide) (by decide) (by decide), h8'⟩ Hpc HR HS
      rw [List.getElem?_eq_getElem hi, show f.vars[i] = (C.x, (f.vars[i]).2) from Prod.ext hx rfl]

end ScanLoop


section Info

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

/-- A frame address names an allocated frame at a nonzero `Env*`. -/
theorem storeRepr_frameInfo (N : NativeAddrs) {s : Store} {B : List (Nat × Nat)} {fa e : Nat} :
    storeRepr (GF := GF) N s B ∗ frameAt fa e ⊢
      storeRepr N s B ∗ ⌜e ≠ 0 ∧ fa < s.frames.size ∧ Vsa.Sim.StoreInvariant s⌝ := by
  iintro ⟨Hs, #He⟩
  ihave ⟨%f, %Gm, %img, %⟨hf, hGe, hlay, hinv⟩, Hown, -, -, Hclose⟩ := storeRepr_openRead N $$ [Hs He]
  · iframe Hs He
  ihave Hs := Hclose $$ Hown
  iframe Hs
  ipureintro
  refine ⟨hGe ▸ hlay.e_ne, ?_, hinv⟩
  rcases Nat.lt_or_ge fa s.frames.size with h | h
  · exact h
  · simp [Array.getElem?_eq_none h] at hf

omit I in
/-- `blockOwn` at some image. -/
theorem blockOwn_img (p n : Nat) :
    blockOwn (GF := GF) p n ⊢ ∃ f : Nat → BitVec 8, ownSet (InExt (p, n)) (fun a => a ↦ₘ f a) :=
  ownSet_fn _

end Info


/-! ## The parent chain -/

section Chain

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

/-- The closer of an open frame (`storeRepr_openAt`). -/
abbrev frameCloser (N : NativeAddrs) (st : Store) (fa : Addr) (B₁ B₂ : List (Nat × Nat)) :
    IProp GF :=
  iprop(∀ (s' : Store) (f' : Frame) (bl' : List (Nat × Nat)),
    ⌜s'.closures = st.closures ∧ s'.frames.toList = st.frames.toList.set fa f' ∧
      Vsa.Sim.StoreInvariant s'⌝ -∗ frameOwn N fa f' bl' -∗ storeRepr N s' (B₁ ++ bl' ++ B₂))

/-- The return after the whole chain missed: `a0 = 0`, the store unchanged. -/
def scanMissK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (C : GetCall) (st : Store) (B : List (Nat × Nat)) (fa : Addr) : IProp GF :=
  iprop(∀ (R' : Nat → BitVec 64) (Mt' : Mem) (fa'' : Addr) (f'' : Frame),
    ⌜GetRet C.s.toNat C.r (pairVal C.saved) 0#64 R' ∧ ChainFrom st C.x fa fa'' ∧
      st.frames[fa'']? = some f'' ∧ FrameMiss f''.vars C.x ∧ f''.parent = none ∧
      ∀ a, C.out.toNat ≤ a → a < C.out.toNat + 24 → imgM Mt' a = C.so a⌝ -∗
    VsaIris.PC ↦ᵣ C.r -∗ regsOf gprs R' -∗
    ownSet (baseS C.s.toNat C.out.toNat) (fun a => a ↦ₘ imgM Mt' a) -∗ storeRepr N st B -∗ Wp.W Φ)

/-- The hit: frame `fa'` open at its first match `j`, parked at the site's hit PC. -/
def scanHitK (Sx : ScanSite live) (Wp : MachWP (GF := GF) (vsaModel live))
    (Φ : Nat × String → IProp GF) (N : NativeAddrs) (C : GetCall) (st : Store)
    (B : List (Nat × Nat)) (fa : Addr) : IProp GF :=
  iprop(∀ (fa' : Addr) (f : Frame) (Gm : FrameGeom) (img : Nat → BitVec 8) (j : Nat) (v : Value)
      (R : Nat → BitVec 64) (Mt : Mem) (B₁ B₂ : List (Nat × Nat)),
    ⌜ChainFrom st C.x fa fa' ∧ st.frames[fa']? = some f ∧ f.vars[j]? = some (C.x, v) ∧
      (∀ p ∈ f.vars.take j, p.1 ≠ C.x) ∧ InFrame C Gm f.vars.length img R Mt ∧
      R 8 = BitVec.ofNat 64 j ∧ B = B₁ ++ Gm.blocks ++ B₂ ∧ Vsa.Sim.StoreInvariant st ∧
      FrameLayout img Gm f.vars.length ∧ (∀ a, frameS Gm a → ¬ baseS C.s.toNat C.out.toNat a)⌝ -∗
    VsaIris.PC ↦ᵣ Sx.hit -∗ regsOf gprs R -∗
    ownSet (getS C.s.toNat C.out.toNat Gm) (fun a => a ↦ₘ imgM Mt a) -∗
    bindings N img Gm.pn Gm.pv f.vars -∗ parentAt f.parent Gm.par -∗ frameAt fa' Gm.e -∗
    frameCloser N st fa' B₁ B₂ -∗ Wp.W Φ)

/-- The scan code from the head of frame `fa'` of the chain. -/
def ScanChainAt (Sx : ScanSite live) (Wp : MachWP (GF := GF) (vsaModel live))
    (Φ : Nat × String → IProp GF) (N : NativeAddrs) (C : GetCall) (st : Store)
    (B : List (Nat × Nat)) (fa fa' : Addr) : Prop :=
  ∀ (R : Nat → BitVec 64) (Mt : Mem) (e' : BitVec 64), ChainFrom st C.x fa fa' →
    GetHead C.s.toNat C.r (pairVal C.saved) C.so e' C.pn C.out R Mt →
    (textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗ strAt C.pn.toNat C.x ∗ frameAt fa' e'.toNat ∗
      VsaIris.PC ↦ᵣ Sx.head ∗ regsOf gprs R ∗
      ownSet (baseS C.s.toNat C.out.toNat) (fun a => a ↦ₘ imgM Mt a) ∗ storeRepr N st B ∗
      (scanMissK Wp Φ N C st B fa ∧ scanHitK Sx Wp Φ N C st B fa) ⊢ Wp.W Φ)

/-- **After a frame's scan found nothing**: on to the parent, or return 0 at
the root. -/
theorem scan_tail (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (Sx : ScanSite live) (N : NativeAddrs) (C : GetCall) (hC : C.OK)
    {st : Store} {B : List (Nat × Nat)} {fa fa' : Addr} {f : Frame} {Gm : FrameGeom}
    {img : Nat → BitVec 8} {B₁ B₂ : List (Nat × Nat)}
    (ih : ∀ p, p < fa' → ScanChainAt Sx Wp Φ N C st B fa p)
    (hpath : ChainFrom st C.x fa fa') (hf : st.frames[fa']? = some f)
    (hinv : Vsa.Sim.StoreInvariant st) (hB : B = B₁ ++ Gm.blocks ++ B₂)
    (hlay : FrameLayout img Gm f.vars.length) (hmiss : FrameMiss f.vars C.x)
    (hdisj : ∀ a, frameS Gm a → ¬ baseS C.s.toNat C.out.toNat a)
    {R : Nat → BitVec 64} {Mt : Mem} (hF : InFrame C Gm f.vars.length img R Mt) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗ strAt C.pn.toNat C.x ∗
      bindings N img Gm.pn Gm.pv f.vars ∗ parentAt f.parent Gm.par ∗ frameAt fa' Gm.e ∗
      frameCloser N st fa' B₁ B₂ ∗
      VsaIris.PC ↦ᵣ Sx.tail ∗ regsOf gprs R ∗
      ownSet (getS C.s.toNat C.out.toNat Gm) (fun a => a ↦ₘ imgM Mt a) ∗
      (scanMissK Wp Φ N C st B fa ∧ scanHitK Sx Wp Φ N C st B fa)
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hgp, #Hcmp, #Hx, #Hb, #Hp, #HGe, Hclose, Hpc, HR, HS, HK⟩
  have hs64 : 64 ≤ C.s.toNat := by have := hC.sp.lo; unfold htifLo at this; omega
  iapply wp_span Wp (Sx.sParent (s := C.s.toNat) (out := C.out.toNat) hF.lay hF.env)
  iframe Ht Hgp Hpc HR HS
  iintro %pc1 %R1 %Mt1 %⟨rfl, hk, hcase⟩ Hpc HR HS
  rcases hcase with ⟨hpar, rfl, h20⟩ | ⟨hpar, rfl, h10⟩
  · -- the parent frame
    ihave HB := get_split hdisj hF.img $$ HS
    icases HB with ⟨HB, HF⟩
    ihave Hst := storeRepr_closeSame N hf hinv hlay $$ [Hclose HF]
    · iframe Hclose HF Hb Hp HGe
    rw [← hB]
    cases hfp : f.parent with
    | none =>
      unfold parentAt
      iexfalso
      icases Hp with %h
      exact absurd h hpar
    | some pa =>
      unfold parentAt
      icases Hp with ⟨-, #Hpa⟩
      have hpa : pa < fa' := by
        have ha : fa' < st.frames.size := by
          rcases Nat.lt_or_ge fa' st.frames.size with h | h
          · exact h
          · simp [Array.getElem?_eq_none h] at hf
        have hfa : st.frames[fa'] = f := by simpa [Array.getElem?_eq_getElem ha] using hf
        exact hinv.parents fa' ha pa (by rw [hfa]; exact hfp)
      have hparlt : Gm.par < 2 ^ 64 := by rw [← hlay.parent]; exact imgLE_lt _ _ 8
      iapply ih pa hpa R1 _ (BitVec.ofNat 64 Gm.par) (.step hpath hf hmiss hfp)
        ⟨hF.stack.congr (hk 2 (by decide) (by decide)) (hk 22 (by decide) (by decide))
          (fun _ _ _ => rfl) hs64, (hk 19 (by decide) (by decide)).trans hF.name, h20,
          (hk 21 (by decide) (by decide)).trans hF.out, hF.slot⟩
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hparlt]
      iframe Ht Hgp Hcmp Hx Hpa Hpc HR HB Hst HK
  · -- the root: return 0
    have hstk : GetStack C.s.toNat C.r (pairVal C.saved) R1 Mt1 :=
      hF.stack.congr (hk 2 (by decide) (by decide)) (hk 22 (by decide) (by decide))
        (fun _ _ _ => rfl) hs64
    iapply wp_span Wp (Sx.sEpi (out := C.out.toNat) (G := Gm) hC.sp.lo hC.sp.hi hC.ra hstk)
    iframe Ht Hgp Hpc HR HS
    iintro %pc2 %R2 %Mt2 %⟨rfl, rfl, hret⟩ Hpc HR HS
    ihave HB := get_split hdisj hF.img $$ HS
    icases HB with ⟨HB, HF⟩
    ihave Hst := storeRepr_closeSame N hf hinv hlay $$ [Hclose HF]
    · iframe Hclose HF Hb Hp HGe
    rw [← hB]
    cases hfp : f.parent with
    | some pa =>
      unfold parentAt
      iexfalso
      icases Hp with ⟨%h, -⟩
      exact absurd hpar h
    | none =>
      ihave Kmiss := and_elim_l $$ HK
      unfold scanMissK
      iapply Kmiss $$ %R2 %_ %fa' %f
        %⟨by rw [h10] at hret; exact hret, hpath, hf, hmiss, hfp, hF.slot⟩ Hpc HR HB Hst

/-- **The parent chain**: the scan code from any frame's head, by strong
induction on the frame address (parents are older). -/
theorem scan_chain (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (Sx : ScanSite live) (N : NativeAddrs) (C : GetCall) (hC : C.OK)
    {st : Store} {B : List (Nat × Nat)} {fa : Addr} :
    ∀ fa', ScanChainAt Sx Wp Φ N C st B fa fa' := by
  intro fa'
  induction fa' using Nat.strongRecOn with
  | ind fa' ih =>
  intro R Mt e' hpath hhead
  have hs64 : 64 ≤ C.s.toNat := by have := hC.sp.lo; unfold htifLo at this; omega
  iintro ⟨#Ht, #Hgp, #Hcmp, #Hx, #Hfa, Hpc, HR, HS, Hst, HK⟩
  ihave ⟨%f, %Gm, %img, %B₁, %B₂, %⟨hf, hGe, hlay, hinv, hB⟩, Hown, #Hb, #Hp, #HGe, Hclose⟩ :=
    storeRepr_openAt N $$ [Hst Hfa]
  · iframe Hst Hfa
  ihave ⟨%Mt1, %⟨hbase, himg, hdisj⟩, HS⟩ := get_join _ _ Gm Mt img $$ [HS Hown]
  · iframe HS Hown
  have hF : InFrame C Gm f.vars.length img R Mt1 :=
    { stack := hhead.stack.congr rfl rfl (fun a h1 h2 => hbase a (.inl ⟨h1, h2⟩)) hs64
      name := hhead.name
      out := hhead.out
      env := by rw [hhead.frame, hGe]
      lay := hlay.congr himg
      img := himg
      sepOut := fun a ha => by
        have := hdisj a ha; unfold baseS at this; omega
      sepStk := fun a ha => by
        have := hdisj a ha; unfold baseS at this; omega
      slot := fun a h1 h2 => (hbase a (.inr ⟨h1, h2⟩)).trans (hhead.slot a h1 h2) }
  iapply wp_span Wp (Sx.sHead (s := C.s.toNat) (out := C.out.toNat) hF.lay hF.env)
  iframe Ht Hgp Hpc HR HS
  iintro %pc1 %R1 %Mt2 %⟨rfl, hcase⟩ Hpc HR HS
  rcases hcase with ⟨hn0, rfl, hk⟩ | ⟨hpos, rfl, hsc⟩
  · -- an empty frame
    have hnil : f.vars = [] := List.eq_nil_of_length_eq_zero hn0
    iapply scan_tail Wp Sx N C hC ih hpath hf hinv hB hlay (by rw [hnil]; intro p hp; cases hp) hdisj
      (hF.regs hs64 fun k hk' => hk k (by omega))
    iframe Ht Hgp Hcmp Hx Hb Hp HGe Hclose Hpc HR HS HK
  · -- scan the names
    obtain ⟨-, -, hn2, -, -, hnw, -⟩ := hF.lay.slot hpos
    iapply scan_frame Wp Sx N C hC f.vars.length 0 R1 _ (by omega) hpos (by simp) hsc.idx
      (by rw [hsc.cur, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := hnw.hi; omega)]; simp)
      hsc.cnt (hF.regs hs64 fun k hk' => hsc.keep k (by omega) (by omega) (by omega))
    iframe Ht Hgp Hcmp Hx Hb Hpc HR HS
    isplit
    · iintro %R' %Mt' %⟨hF', hmiss⟩ Hpc HR HS
      iapply scan_tail Wp Sx N C hC ih hpath hf hinv hB hlay hmiss hdisj hF'
      iframe Ht Hgp Hcmp Hx Hb Hp HGe Hclose Hpc HR HS HK
    · iintro %j %v %R' %Mt' %⟨hj, hne, hF', h8⟩ Hpc HR HS
      ihave Khit := and_elim_r $$ HK
      unfold scanHitK
      iapply Khit $$ %fa' %f %Gm %img %j %v %R' %Mt' %B₁ %B₂
        %⟨hpath, hf, hj, hne, hF', h8, hB, hinv, hlay, hdisj⟩ Hpc HR HS Hb Hp HGe Hclose

end Chain

/-! ## The ABI entry and return -/

section Abi

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
  {live : Nat → Prop}

omit I in
/-- **The return's registers** out of a span's file. -/
theorem scan_exit_regs {s r : BitVec 64} {saved : List (Nat × BitVec 64)}
    (hsv : saved.map Prod.fst = getSaved) {R' : Nat → BitVec 64} {res : BitVec 64}
    (hret : GetRet s.toNat r (pairVal saved) res R') :
    regsOf (GF := GF) gprs R' ⊢
      VsaIris.ra ↦ᵣ r ∗ (10 : Nat) ↦ᵣ res ∗ VsaIris.sp ↦ᵣ s ∗ savedOwn saved ∗ clobbered retClob := by
  have hperm' : (([(VsaIris.ra, r), (10, res), (VsaIris.sp, s)] ++ saved).map Prod.fst ++
      retClob).Perm gprs := by
    simp only [List.map_append, List.map_cons, List.map_nil, hsv]; decide
  have hfix : ∀ p ∈ [(VsaIris.ra, r), (10, res), (VsaIris.sp, s)] ++ saved, R' p.1 = p.2 := by
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl | rfl
      · exact hret.ra
      · exact hret.a0
      · show R' 2 = s
        rw [hret.sp]; exact BitVec.eq_of_toNat_eq (by simp)
    · rw [hret.saved p.1 (by rw [← hsv]; exact List.mem_map_of_mem hp),
        pairVal_of_mem saved (by rw [hsv]; decide) p hp]
  iintro HR
  ihave Hregs := regsOf_exit gprs _ retClob hperm' R' hfix $$ HR
  icases Hregs with ⟨Hfix, Hcl⟩
  unfold savedOwn
  ihave ⟨H5, Hsv⟩ := (sepL_append _ _ _).1 $$ Hfix
  simp only [sepL_cons, sepL_nil]
  icases H5 with ⟨Hra, Ha0, Hsp, -⟩
  iframe Hra Ha0 Hsp Hsv Hcl

omit I in
/-- **The return's bytes**: the stack frame back as scratch, and the slot. -/
theorem scan_exit_bytes {s out : Nat} {Mt : Mem} (hs64 : 64 ≤ s)
    (hsep : out + 24 ≤ s - 64 ∨ s ≤ out) :
    ownSet (GF := GF) (baseS s out) (fun a => a ↦ₘ imgM Mt a) ⊢
      blockOwn (s - 64) 64 ∗ ownSet (InExt (out, 24)) (fun a => a ↦ₘ imgM Mt a) := by
  iintro HB
  ihave HB := ownSet_iff (T := fun a => InExt (s - 64, 64) a ∨ InExt (out, 24) a) _
    (fun a => by simp only [baseS, InExt]; omega) $$ HB
  ihave ⟨Hstk, Hout⟩ := ownSet_unglue _ _ _ (fun a h1 h2 => by
    simp only [InExt] at h1 h2; omega) $$ HB
  iframe Hout
  unfold blockOwn
  iapply ownSet_forget $$ Hstk

/-- **The ABI entry** of `env_get`/`env_set`: the register file, the stack
frame and the value slot, the prologue span, then the chain from `fa`. -/
theorem scan_entry (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (Sx : ScanSite live) (N : NativeAddrs) {st : Store} {B : List (Nat × Nat)} {fa : Addr}
    {x : String} {e pn out s r : BitVec 64} {saved : List (Nat × BitVec 64)}
    {fo : Nat → BitVec 8} (hsv : saved.map Prod.fst = getSaved) (hr : r.toNat % 4 = 0)
    (hsp : EnvSp s envGetNeed) (hslot : SlotWin out.toNat) :
    textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗ VsaIris.PC ↦ᵣ Sx.entry ∗ VsaIris.ra ↦ᵣ r ∗
      (10 : Nat) ↦ᵣ e ∗ (11 : Nat) ↦ᵣ pn ∗ (12 : Nat) ↦ᵣ out ∗ VsaIris.sp ↦ᵣ s ∗
      clobbered argClob ∗ savedOwn saved ∗ stackScratch s envGetNeed ∗ frameAt fa e.toNat ∗
      strAt pn.toNat x ∗ ownSet (InExt (out.toNat, 24)) (fun a => a ↦ₘ fo a) ∗ storeRepr N st B ∗
      (scanMissK Wp Φ N ⟨s, r, pn, out, x, saved, fo⟩ st B fa ∧
        scanHitK Sx Wp Φ N ⟨s, r, pn, out, x, saved, fo⟩ st B fa)
    ⊢ Wp.W Φ := by
  iintro ⟨#Ht, #Hgp, #Hcmp, Hpc, Hra, Ha0, Ha1, Ha2, Hsp, Hcl, Hsv, Hstk, #Hfa, #Hx, Hout, Hst, HK⟩
  ihave ⟨Hst, %⟨hene, hfalt, hinv⟩⟩ := storeRepr_frameInfo N $$ [Hst Hfa]
  · iframe Hst Hfa
  have hs64 : 64 ≤ s.toNat := by have := hsp.lo; unfold htifLo envGetNeed at this; omega
  unfold stackScratch
  ihave ⟨%fs, Hstk⟩ := blockOwn_img _ _ $$ Hstk
  ihave ⟨⟨Hstk, Hout⟩, %hdo⟩ := keep_pure (ownSet_disj _ _ fs fo) $$ [Hstk Hout]
  · iframe Hstk Hout
  have hsep : out.toNat + 24 ≤ s.toNat - 64 ∨ s.toNat ≤ out.toNat := by
    have := interval_apart (a := out.toNat) (n := 24) (b := s.toNat - envGetNeed)
      (m := envGetNeed) (by omega) (by unfold envGetNeed; omega) fun c h1 h2 => by
        have := hdo c ⟨h1, h2⟩
        unfold InExt at this; omega
    unfold envGetNeed at this; omega
  ihave HB := ownSet_glue _ _ fs fo hdo $$ [Hstk Hout]
  · iframe Hstk Hout
  ihave HB := ownSet_iff (T := baseS s.toNat out.toNat) _ (fun a => by
    unfold baseS InExt envGetNeed; omega) $$ HB
  ihave ⟨%Mt0, %hag, HB⟩ := ownSet_tracked _ _ $$ HB
  have hperm : (([(VsaIris.ra, r), (10, e), (11, pn), (12, out), (VsaIris.sp, s)] ++ saved).map
      Prod.fst ++ argClob).Perm gprs := by
    simp only [List.map_append, List.map_cons, List.map_nil, hsv]; decide
  ihave ⟨%R0, %hR0, HR⟩ := regsOf_entry gprs _ argClob hperm gprs_nodup $$ [Hra Ha0 Ha1 Ha2 Hsp Hsv Hcl]
  · iframe Hcl
    unfold savedOwn
    iapply (sepL_append _ _ _).2
    isplitr [Hsv]
    · simp only [sepL_cons, sepL_nil]
      isplitl [Hra]
      · iexact Hra
      iframe Ha0 Ha1 Ha2
      isplitl [Hsp]
      · iexact Hsp
      iempintro
    · iexact Hsv
  have hR : ∀ k v, (k, v) ∈ [(VsaIris.ra, r), (10, e), (11, pn), (12, out), (VsaIris.sp, s)] ++
      saved → R0 k = v := fun k v h => hR0 (k, v) h
  have hsvR : ∀ k ∈ getSaved, R0 k = pairVal saved k := fun k hk => by
    rw [← hsv] at hk
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hk
    rw [hR0 p (List.mem_append_right _ hp), pairVal_of_mem saved (by rw [hsv]; decide) p hp]
  let C : GetCall := ⟨s, r, pn, out, x, saved, fo⟩
  have hC : C.OK := ⟨hsp, hslot, hr, hsv, hsep⟩
  have hentry : GetEntry s.toNat r (pairVal saved) R0 :=
    ⟨by rw [hR 10 e (by simp)]; intro h; exact hene (by rw [h]; rfl),
     by rw [show (2 : Nat) = VsaIris.sp from rfl, hR VsaIris.sp s (by simp)],
     hR VsaIris.ra r (by simp), hsvR⟩
  have hso : ∀ a, (R0 12).toNat ≤ a → a < (R0 12).toNat + 24 → imgM Mt0 a = fo a :=
    fun a h1 h2 => by
      rw [hR 12 out (by simp)] at h1 h2
      have hns : ¬ InExt (s.toNat - envGetNeed, envGetNeed) a := by
        unfold InExt envGetNeed; omega
      rw [hag a (by unfold baseS; omega)]
      simp [glue, hns]
  iapply wp_span Wp (Sx.sEntry (out := out.toNat) hsp.lo hsp.hi hsp.align hentry hso
    (by rw [hR 12 out (by simp)]; exact hsep))
  iframe Ht Hgp Hpc HR HB
  iintro %pc1 %R1 %Mt1 %⟨rfl, hhead⟩ Hpc HR HB
  rw [hR 10 e (by simp), hR 11 pn (by simp), hR 12 out (by simp)] at hhead
  iapply scan_chain Wp Sx N C hC fa R1 Mt1 e .refl hhead
  iframe Ht Hgp Hcmp Hx Hfa Hpc HR HB Hst HK

end Abi

end VsaIris.Interp
