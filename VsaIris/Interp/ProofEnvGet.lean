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
(`0x80002cc4`, every name differs from `x`) or returns with the first match
copied out. -/
theorem get_scan (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (hl : ∀ p ∈ envText, live p.1) (N : NativeAddrs) (C : GetCall) (hC : C.OK)
    {f : Frame} {G : FrameGeom} {img : Nat → BitVec 8} :
    ∀ m i R Mt, f.vars.length - i = m → i < f.vars.length →
      (∀ p ∈ f.vars.take i, p.1 ≠ C.x) →
      R 8 = BitVec.ofNat 64 i → (R 9).toNat = G.pn + 8 * i →
      R 18 = BitVec.ofNat 64 f.vars.length → InFrame C G f.vars.length img R Mt →
      textOwn envText ∗ gp ↦ᵣ□ gpV ∗ strcmpSpec Wp ∗ strAt C.pn.toNat C.x ∗
        bindings N img G.pn G.pv f.vars ∗ VsaIris.PC ↦ᵣ 0x80002c60#64 ∗ regsOf gprs R ∗
        ownSet (getS C.s.toNat C.out.toNat G) (fun a => a ↦ₘ imgM Mt a) ∗
        ((∀ R' Mt', ⌜InFrame C G f.vars.length img R' Mt' ∧ FrameMiss f.vars C.x⌝ -∗
            VsaIris.PC ↦ᵣ 0x80002cc4#64 -∗ regsOf gprs R' -∗
            ownSet (getS C.s.toNat C.out.toNat G) (fun a => a ↦ₘ imgM Mt' a) -∗ Wp.W Φ) ∗
         (∀ R' Mt' (v : Value), ⌜GetRet C.s.toNat C.r (pairVal C.saved) 1#64 R' ∧
            FirstMatch f.vars C.x v ∧ ∀ a, frameS G a → imgM Mt' a = img a⌝ -∗
            VsaIris.PC ↦ᵣ C.r -∗ regsOf gprs R' -∗
            ownSet (getS C.s.toNat C.out.toNat G) (fun a => a ↦ₘ imgM Mt' a) -∗
            valImg N (imgM Mt') C.out.toNat v -∗ Wp.W Φ))
      ⊢ Wp.W Φ := by
  intro m
  induction m with
  | zero => intro i R Mt hm hi; omega
  | succ m ih =>
    intro i R Mt hm hi hne h8 h9 h18 hF
    iintro ⟨#Ht, #Hgp, #Hcmp, #Hx, #Hb, Hpc, HR, HS, Kex, Khit⟩
    iapply wp_span Wp (get_load hl hF.lay hi h9)
    iframe Ht Hgp Hpc HR HS
    iintro %pc1 %R1 %Mt1 %⟨rfl, rfl, h10, h11, hk1⟩ Hpc HR HS
    ihave ⟨#Hname, #Hval⟩ := bindings_get N img G.pn G.pv f.vars hi $$ Hb
    have hname : (R1 10).toNat = imgLE img (G.pn + 8 * i) 8 := by
      rw [h10, imgW_toNat]
      exact imgLE_congr fun j hj => hF.img _ (frameS_name hF.lay hi hj)
    rw [show (0x80002c68#64 : BitVec 64) = BitVec.ofNat 64 0x80002c68 from rfl]
    iapply wp_call_strcmp Wp (jalx_80002c68 live (fun p hp => hl _ (env_code_80002c68 p hp)))
      (by decide) (xi := (f.vars[i]).1) (x := C.x)
    isplitl []
    · iapply instrAt_of_text env_code_80002c68 $$ Ht
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
    rw [show BitVec.ofNat 64 (0x80002c68 + 4) = 0x80002c6c#64 from rfl]
    iapply wp_span Wp (get_cmp hl (s := C.s.toNat) (out := C.out.toNat) (G := G) hi hn h8' h18')
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
      iframe Ht Hgp Hcmp Hx Hb Hpc HR HS Kex Khit
    · -- the frame is exhausted
      have hxi : (f.vars[i]).1 ≠ C.x := fun h => hne0 (hres.2 h)
      have k3 : ∀ k, k ∉ strcmpKs → k ≠ 10 → k ≠ 11 → k ≠ 8 → k ≠ 9 → R3 k = R k :=
        fun k hk h10 h11 h8 h9 => (hnx.keep k h8 h9).trans (k2 k hk h10 h11)
      have hmiss : FrameMiss f.vars C.x := by
        intro p hp
        have := take_succ_all hi hne hxi
        rw [List.take_of_length_le (by omega)] at this
        exact this p hp
      iapply Kex $$ %R3 %_ %⟨hF.regs hs64 fun k hk => by
          rcases hk with rfl | rfl | rfl | rfl | rfl <;>
            exact k3 _ (by decide) (by decide) (by decide) (by decide) (by decide), hmiss⟩ Hpc HR HS
    · -- the hit: copy `vals[i]` out, return 1
      subst hR3
      have hx : (f.vars[i]).1 = C.x := hres.1 heq0
      obtain ⟨hcap, -, -, hv1, hv2, -, hvw⟩ := hF.lay.slot hi
      have hdv : C.out.toNat + 24 ≤ G.pv ∨ G.vblk.1 + G.vblk.2 ≤ C.out.toNat := by
        have := interval_apart (a := C.out.toNat) (n := 24) (b := G.vblk.1) (m := G.vblk.2)
          (by omega) (by omega) fun c h1 h2 => hF.sepOut c (by
            unfold frameS InExt; exact .inr ⟨hcap, .inr ⟨h1, h2⟩⟩)
        exact this.imp (fun h => hv1 ▸ h) id
      have hwo : 0x80000000 ≤ C.out.toNat ∧ C.out.toNat + 24 ≤ 0x100000000 ∧
          htifLo + 16 ≤ C.out.toNat ∧ C.out.toNat % 8 = 0 :=
        ⟨hC.slot.lo, hC.slot.hi, hC.slot.htif, hC.slot.align⟩
      have h20 : (R3 20).toNat = G.e := by
        rw [k2 20 (by decide) (by decide) (by decide)]; exact hF.env
      have h21 : (R3 21).toNat = C.out.toNat := by
        rw [k2 21 (by decide) (by decide) (by decide), hF.out]
      have hsp := hC.sp
      have hspan := get_hit hl (G := G) hsp.lo hsp.hi hC.ra
        (hF.stack.congr (k2 2 (by decide) (by decide) (by decide))
          (k2 22 (by decide) (by decide) (by decide)) (fun _ _ _ => rfl) hs64)
        hF.lay hi h8' h20 h21 hwo hdv hC.sep
      iapply wp_span Wp hspan
      iframe Ht Hgp Hpc HR HS
      iintro %pc4 %R4 %Mt4 %⟨rfl, hret, hco⟩ Hpc HR HS
      have himg : ∀ a, frameS G a → imgM Mt4 a = img a := fun a ha =>
        (hco.frame a (hF.sepOut a ha)).trans (hF.img a ha)
      iapply Khit $$ %R4 %Mt4 %((f.vars[i]).2) %⟨hret, ?_, himg⟩ Hpc HR HS
      · refine ⟨f.vars.take i, f.vars.drop (i + 1), ?_, hne⟩
        conv => lhs; rw [← List.take_append_drop i f.vars, List.drop_eq_getElem_cons hi]
        rw [show f.vars[i] = (C.x, (f.vars[i]).2) from Prod.ext hx rfl]
      · have w : ∀ o, o + 8 ≤ 24 → ldv .ld Mt4 (C.out.toNat + o) =
            ldv .ld Mt3 (G.pv + 24 * i + o) → imgW (imgM Mt4) (C.out.toNat + o) =
              imgW img (G.pv + 24 * i + o) := fun o ho h => by
          rw [← ldv_ld_img, h, ldv_ld_img]
          exact imgW_agree fun j hj => by
            have := hF.img _ (frameS_val hF.lay hi (j := o + j) (by omega))
            rwa [show G.pv + 24 * i + (o + j) = G.pv + 24 * i + o + j by omega] at this
        unfold valImg
        rw [show C.out.toNat = C.out.toNat + 0 from rfl, w 0 (by omega) hco.w0,
          w 8 (by omega) hco.w1, w 16 (by omega) hco.w2]
        iexact Hval

end ScanLoop

end VsaIris.Interp
