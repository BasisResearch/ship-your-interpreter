import Vsa.Compiler.SimParams

/-!
# Function entry

From the closure's code address with the closure in `a2`, the arguments at
`a3` and their count in `a4`: the arity and depth checks, the stack frame with
the saved return address and frame, the fresh frame for the function's layout
below the closure's frame, and the parameters.
-/

namespace Vsa.Compiler

open Vsa.Sim Vsa.While LeanRV64DExecutable.Functions

theorem sext_negN (n : Nat) (h1 : 0 < n) (h2 : n ≤ 2048) :
    (sign_extend (BitVec.ofInt 12 (-(n : Int))) : BitVec 64) = BitVec.ofNat 64 (2 ^ 64 - n) := by
  rw [sext12_ofInt _ (by omega) (by omega)]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofInt]
  omega

/-- The checks and the call of `newframe` at the start of a function. -/
def fnHead (L : List String) (params : List String) (fs pos : Nat) : List Ins :=
  [mvi t0 params.length] ++ errUnlessEq a4 t0 (pos + 1) ++
    [mvi t0 1000, Br .lt depR t0 (pos + 4) (pos + 6), J (pos + 5) errPos,
     addi depR depR 1, addi spR spR (-(fs : Int)), .sd ra spR, addi t6 spR 8, .sd envR t6,
     .ld a6 a2, mvi a5 L.length, Call (pos + 13) nfPos]

theorem fnPre_eq (L : List String) (params : List String) (fs pos : Nat) :
    fnPre L params fs pos = fnHead L params fs pos ++ paramCopies L 0 params ++ [mv envR a4] := rfl

theorem fnHead_length (L : List String) (params : List String) (fs pos : Nat) :
    (fnHead L params fs pos).length = 14 := rfl

theorem paramCopies_length (L : List String) : ∀ (j : Nat) (ps : List String),
    (paramCopies L j ps).length = 8 * ps.length
  | _, [] => rfl
  | j, x :: xs => by simp [paramCopies, paramCopies_length L (j + 1) xs, paramCopy]; omega

/-- Where the body of a function starts. -/
def fnBody (params : List String) (q : Nat) : Nat := q + 14 + 8 * params.length + 1

theorem fnPre_length (L : List String) (params : List String) (fs q : Nat) :
    q + (fnPre L params fs q).length = fnBody params q := by
  simp [fnPre_eq, fnHead_length, paramCopies_length, fnBody]; omega

/-- The view after entering a function frame of layout `L`. -/
def View.enter (V : View) (L : List String) : View :=
  { V with F := V.F ++ [(V.hF, L)], hF := V.hF + 8 + 16 * L.length }

/-- The store at a function body's start. -/
def entryStore (s : Store) (cd : ClosureData) (vs : List Value) : Store :=
  (cd.params.zip vs).foldl (fun t p => t.define s.frames.size p.1 p.2) (s.allocFrame (some cd.env)).1

/-- The function body is entered. -/
structure Entered (code : List Ins) (T : List String) (V : View) (st : St) (d : Nat) (cd : ClosureData)
    (Γc : List (List String)) (vs : List Value) (sp fs' q : Nat) (r e : BitVec 64) (A B : AM) : Prop where
  pc : B.pc = pcOf (fnBody cd.params q)
  ms : MS code T (V.enter (frameNames cd.params cd.body)) ⟨entryStore st.store cd vs, st.out⟩ (d + 1)
    st.store.frames.size (frameNames cd.params cd.body :: Γc) (sp - fs') fs' B
  ra : rdW B.mem (sp - fs') = r
  env : rdW B.mem (sp - fs' + 8) = e
  stack : Agree A.mem B.mem sp stackHi
  obj : ObjAgree A.mem B.mem V.h
  grow : VGrow V st.store (V.enter (frameNames cd.params cd.body)) (entryStore st.store cd vs)

theorem fnCode_eq (T : List String) (Γc : List (List String)) (params : List String) (body : List Stmt)
    (q : Nat) : fnCode T Γc params body q =
      fnHead (frameNames params body) params (frameSize body) q ++ paramCopies (frameNames params body) 0 params ++
        [mv envR a4] ++
      (gseq T (fnCtx (frameNames params body :: Γc) (fnBody params q +
        (gseq T (fnCtx (frameNames params body :: Γc) 0) (fnBody params q) body).length + 2)) (fnBody params q) body ++
      fnPost (frameSize body)) := by
  unfold fnCode
  simp only [fnPre_length]
  rw [fnPre_eq]
  simp only [List.append_assoc]

theorem addName_nodup {l : List String} (h : l.Nodup) (x : String) : (addName l x).Nodup := by
  unfold addName
  split
  · exact h
  · next hx => exact List.nodup_append.mpr ⟨h, by simp, fun a ha b hb e => by
      simp at hb; subst hb; subst e; exact hx ha⟩

theorem addNames_nodup : ∀ (xs : List String) {l : List String}, l.Nodup → (addNames l xs).Nodup
  | [], _, h => h
  | x :: xs, _, h => addNames_nodup xs (addName_nodup h x)

theorem mem_addName {l : List String} {x y : String} (h : y ∈ l ∨ y = x) : y ∈ addName l x := by
  unfold addName
  split
  · next hx =>
    rcases h with h | rfl
    · exact h
    · exact hx
  · rcases h with h | rfl
    · exact List.mem_append_left _ h
    · simp

theorem mem_addNames : ∀ (xs : List String) {l : List String} {y : String}, y ∈ l ∨ y ∈ xs → y ∈ addNames l xs
  | [], _, _, h => by
    rcases h with h | h
    · exact h
    · simp at h
  | x :: xs, _, _, h => by
    apply mem_addNames xs
    rcases h with h | h
    · exact .inl (mem_addName (.inl h))
    · simp only [List.mem_cons] at h
      rcases h with rfl | h
      · exact .inl (mem_addName (.inr rfl))
      · exact .inr h

theorem frameNames_nodup (pre : List String) (ss : List Stmt) : (frameNames pre ss).Nodup :=
  addNames_nodup _ List.nodup_nil

theorem mem_frameNames_pre {pre : List String} {ss : List Stmt} {x : String} (h : x ∈ pre) :
    x ∈ frameNames pre ss := mem_addNames _ (.inr (List.mem_append_left _ h))

theorem ChainL.push {F : FrMap} {s : Store} {b a : Addr} {Γ : List (List String)} (hc : ChainL F s b Γ)
    {fr : Frame} (hfr : s.frames[a]? = some fr) (hpar : fr.parent = some b) {f : Nat} {L : List String}
    (hF : F[a]? = some (f, L)) : ChainL F s a (L :: Γ) := by
  cases hc with
  | top h1 h2 h3 => exact .cons hfr hpar hF (.top h1 h2 h3)
  | cons h1 h2 h3 h4 => exact .cons hfr hpar hF (.cons h1 h2 h3 h4)

theorem View.fa_append {V : View} {a : Addr} {q : Nat × List String} (ha : a < V.F.length) :
    parOf (V.F ++ [q]) (some a) = V.fa a := by
  simp [View.fa, parOf, List.getElem?_append_left ha]

/-- Closure code survives frame growth with the same closures. -/
theorem CloCode.grow {code : List Ins} {T : List String} {V V' : View} {s s' : Store} {m m' : Mem}
    (hc : CloCode code T V s m) (hok : CloOK V.H s m V.h) (hag : ObjAgree m m' V.h) (hg : Grows V.F s V'.F s')
    (hH : V'.H = V.H) (hcl : s'.closures = s.closures)
    (hfa : ∀ b, (∃ fr, s.frames[b]? = some fr) → V'.fa b = V.fa b) : CloCode code T V' s' m' := by
  intro a cd p ha hp
  rw [hcl] at ha; rw [hH] at hp
  obtain ⟨q, Γc, h1, h2, h3, h4, h5, h6⟩ := hc.transport hok hag a cd p ha hp
  have := ChainL.frame h3
  exact ⟨q, Γc, by rw [hfa _ this]; exact h1, h2, h3.grow hg, h4, h5, h6⟩

section
variable {code : List Ins} {T : List String} (hR : RTLoaded code)
include hR

theorem run_entry {V : View} {st : St} {d : Nat} {env : Addr} {Γ : List (List String)} {sp fs k : Nat}
    {A : AM} (hm : MS code T V st d env Γ sp fs A) {a : Addr} {cd : ClosureData} {p q : Nat}
    {Γc : List (List String)} {vs : List Value} (hcd : st.store.closures[a]? = some cd) (hp : V.H[a]? = some p)
    (henvw : rdW A.mem p = BitVec.ofNat 64 (V.fa cd.env)) (hchain : ChainL V.F st.store cd.env Γc)
    (hseg : Seg code q (fnCode T Γc cd.params cd.body q))
    (hP : PosOK (q + (fnCode T Γc cd.params cd.body q).length)) (hwf : WfFn T Γc cd.params cd.body)
    (hlen : vs.length = cd.params.length) (hd : d < maxCallDepth) (hA : A.pc = pcOf q) {r : BitVec 64}
    (h1 : Has A.regs ra r) (h12 : Has A.regs a2 (BitVec.ofNat 64 p))
    (h13 : Has A.regs a3 (BitVec.ofNat 64 (sp + 16 + 16 * (k + 1))))
    (h14 : Has A.regs a4 (BitVec.ofNat 64 vs.length)) (hargs : InTmps V.H A.mem V.h sp (k + 1) vs)
    (htmp : 16 + 16 * (k + 1 + vs.length) ≤ fs) (hmax : vs.length ≤ maxArgs) :
    Reaches code A (fun B => (B.pc = pcOf errPos ∧
        frameEnd < V.hF + 8 + 16 * (frameNames cd.params cd.body).length) ∨
      Entered code T V st d cd Γc vs sp (frameSize cd.body) q r (BitVec.ofNat 64 (V.fa env)) A B) := by
  obtain ⟨hwL, hwT, hwB⟩ := hwf
  obtain ⟨dA, cA, hco⟩ := hm.rel.clo.obj a cd p hcd hp
  have hco1 := hco.lo
  have hco2 := hco.hi
  have hco3 := hco.al
  have hptr := hm.img.ptr.hi
  have hfs : frameSize cd.body ≤ 1936 := by unfold frameSize; omega
  have hfs0 : 16 ≤ frameSize cd.body := by unfold frameSize; omega
  have hfs16 : frameSize cd.body % 16 = 0 := by unfold frameSize; omega
  have hst := hm.stk
  have hb := hst.bounds
  have hdep := hst.depth
  have hroom := hst.room
  have hmc : maxCallDepth = 1000 := rfl
  have hM : maxFS = 2048 := rfl
  have hL : stackLo = 0xE0000000 := rfl
  have hH : stackHi = 0x100000000 := rfl
  have ht : tohostAddr = 0x8001ad00 := rfl
  have hma : maxArgs = 32 := rfl
  have hsp2 : stackLo + maxFS ≤ sp := by
    have : maxFS ≤ (maxCallDepth - d) * maxFS := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hspfs : frameSize cd.body ≤ sp := by omega
  have hfb : fnBody cd.params q = q + 14 + 8 * cd.params.length + 1 := rfl
  have hPb : PosOK (fnBody cd.params q) := posOK_le hP (by
    rw [fnCode_eq]; simp only [List.length_append, fnHead_length, paramCopies_length, List.length_singleton]
    omega)
  rw [fnCode_eq] at hseg
  obtain ⟨sPre, sBody⟩ := hseg.append
  obtain ⟨sPre, sMv⟩ := sPre.append
  obtain ⟨sH, sPc⟩ := sPre.append
  simp only [fnHead_length, List.length_append, paramCopies_length] at sPc sMv
  obtain ⟨pc0, L0, m0, o0⟩ := A
  simp only at hA; subst hA
  have k1 := has_mem h1 (by decide); have e1 := srcVal_of_has h1
  have k12 := has_mem h12 (by decide); have e12 := srcVal_of_has h12
  have k14 := has_mem h14 (by decide); have e14 := srcVal_of_has h14
  have k2 := has_mem hm.hsp (by decide); have e2 := srcVal_of_has hm.hsp
  have k9 := has_mem hm.henv (by decide); have e9 := srcVal_of_has hm.henv
  have k24 := has_mem hm.hdep (by decide); have e24 := srcVal_of_has hm.hdep
  simp only [ra, a2, a4, spR, envR, depR] at k1 e1 k12 e12 k14 e14 k2 e2 k9 e9 k24 e24
  apply run_jumps hR.fits sH
  wp_simp [fnHead, errUnlessEq, k14, e14, BitVec.ofInt_natCast, hlen]
  rw [show q + 1 + 2 = q + 3 from rfl]
  have hd' : d < 1000 := hd
  apply run_jumps hR.fits (sH.drop 3)
  wp_simp [fnHead, errUnlessEq, k24, e24, toInt_ofNat_small d (by omega), hd']
  rw [show q + 4 + 2 = q + 6 from rfl]
  have hsp' : sp - frameSize cd.body + frameSize cd.body = sp := by omega
  have n1 : (BitVec.ofNat 64 (sp - frameSize cd.body)).toNat = sp - frameSize cd.body := toNat_ofNat_lt (by omega)
  have n2 : (BitVec.ofNat 64 (sp - frameSize cd.body + 8)).toNat = sp - frameSize cd.body + 8 :=
    toNat_ofNat_lt (by omega)
  have hob : objBase = 0x90000000 := rfl
  have hoe : objEnd = 0xE0000000 := rfl
  have n3 : (BitVec.ofNat 64 p).toNat = p := toNat_ofNat_lt (by omega)
  have t1 : sp - frameSize cd.body ≠ tohostAddr := by omega
  have t2 : sp - frameSize cd.body + 8 ≠ tohostAddr := by omega
  have o1 : StOK (sp - frameSize cd.body) := by unfold StOK; omega
  have o2 : StOK (sp - frameSize cd.body + 8) := by unfold StOK; omega
  have l3 : LdOK p := by unfold LdOK; omega
  have hrp : rdW (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
      (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) p = BitVec.ofNat 64 (V.fa cd.env) := by
    rw [rdW_upd (by omega) (by omega), if_neg (by omega), rdW_upd (by omega) (by omega), if_neg (by omega)]
    exact henvw
  have hLl : (frameNames cd.params cd.body).length < 2048 := by omega
  have s6 := sH.drop 6
  simp only [fnHead, errUnlessEq, List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero] at s6
  rw [if_pos (by omega)]
  have hsub : 18446744073709551616 - (18446744073709551616 - frameSize cd.body) = frameSize cd.body := by omega
  apply run_jumps hR.fits s6
  wp_simp [fnHead, errUnlessEq, k1, e1, k2, e2, k9, e9, k12, e12, k24, e24, hsub, BitVec.ofInt_natCast,
    sext_negN (frameSize cd.body) (by omega) (by omega), n1, n2, n3, t1, t2, o1, o2, l3, hrp]
  -- the fresh frame
  have hq14 : PosOK (q + 14) := posOK_le hPb (by omega)
  have hlo := hm.rel.lo
  have htopF := hm.rel.top
  have hfe : frameEnd = 0x90000000 := rfl
  have hfbase : frameBase = 0x80100000 := rfl
  have hfal := hm.hfal
  refine ex_bind (run_nf hR.fits hR.nf (n := (frameNames cd.params cd.body).length) (by reg_simp [])
    (by reg_simp []; rfl) (by reg_simp []; exact hm.hf) (by reg_simp []) (pcOf_aligned hq14)
    ⟨hlo, hfal, htopF⟩ (by omega)) ?_
  rintro ⟨pc3, L3, m3, o3⟩ (⟨hpc3, hroomF, hm3, ho3, g14, g23, hk3⟩ | ⟨hpc3, hov⟩)
  rotate_left
  · exact reach_here (.inl ⟨hpc3, hov⟩)
  simp only at hpc3 hroomF hm3 ho3 g14 g23 hk3
  subst hpc3 hm3 ho3
  have hag2 : Agree m0 (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
      (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) frameBase V.hF := fun b h1' h2' h3' => by
    rw [rdW_upd (by omega) h3', if_neg (by omega), rdW_upd (by omega) h3', if_neg (by omega)]
  have hob2 : ObjAgree m0 (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
      (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) V.h := fun b h3' h1' h2' => by
    rw [rdW_upd (by omega) h3', if_neg (by omega), rdW_upd (by omega) h3', if_neg (by omega)]
  have hs2 := hm.rel.transport hag2 hob2 (Nat.le_refl _)
  obtain ⟨fr0, hfr0⟩ := hchain.frame
  have henvlt : cd.env < st.store.frames.size := (Array.getElem?_eq_some_iff.mp hfr0).1
  obtain ⟨hs3, hg3, -, hF3, hout3, hlow3⟩ := hs2.alloc_frame (par := some cd.env)
    (L := frameNames cd.params cd.body) (fun b hb => by cases hb; exact henvlt) hfal hlo hroomF
    (frameNames_nodup _ _) hwL
  have hob3 := hob2.trans (hout3.obj (h := V.h) hroomF) (Nat.le_refl _)
  have hrd3 : ∀ b, b % 8 = 0 → sp ≤ b → rdW (tagsW (applyW (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
      (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) (V.hF, 8, BitVec.ofNat 64 (parOf V.F
      (some cd.env)))) (V.hF + 8) (frameNames cd.params cd.body).length) b = rdW m0 b := by
    intro b hb hb'
    have hb2 : (sp - frameSize cd.body + 8) % 8 = 0 := by omega
    have hb1 : (sp - frameSize cd.body) % 8 = 0 := by omega
    rw [hout3 b hb (.inr (by omega)),
      rdW_upd (a := sp - frameSize cd.body + 8) hb2 hb, if_neg (by omega),
      rdW_upd (a := sp - frameSize cd.body) hb1 hb, if_neg (by omega)]
  have hvargs : ∀ i (hi : i < vs.length), VRepr V.H (tagsW (applyW (applyW (applyW m0
      (sp - frameSize cd.body, 8, r)) (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env)))
      (V.hF, 8, BitVec.ofNat 64 (parOf V.F (some cd.env)))) (V.hF + 8) (frameNames cd.params cd.body).length) V.h
      (vs[i]'hi) (rdW (tagsW (applyW (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
      (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) (V.hF, 8, BitVec.ofNat 64 (parOf V.F
      (some cd.env)))) (V.hF + 8) (frameNames cd.params cd.body).length) (sp + 16 + 16 * (k + 1) + 16 * (0 + i)))
      (rdW (tagsW (applyW (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
      (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) (V.hF, 8, BitVec.ofNat 64 (parOf V.F
      (some cd.env)))) (V.hF + 8) (frameNames cd.params cd.body).length) (sp + 16 + 16 * (k + 1) + 16 * (0 + i) + 8)) := by
    intro i hi
    have := hargs i hi
    unfold InTmp at this
    rw [hrd3 _ (by omega) (by omega), hrd3 _ (by omega) (by omega)]
    rw [show sp + 16 + 16 * (k + 1) + 16 * (0 + i) = sp + 16 + 16 * (k + 1 + i) by omega]
    exact this.mono hob3 (Nat.le_refl _)
  refine ex_bind (run_params hR hF3 (argp := sp + 16 + 16 * (k + 1)) (by omega) (by omega) cd.params vs 0 _ _ L3 _
    (q + 14) hlen.symm (by omega) (by have := hm.stk.top; omega) sPc (hk3.has (by decide) (by reg_simp []; exact h13))
    g14 hs3 ⟨⟨some cd.env, []⟩, by simp [Store.allocFrame]⟩ (fun x hx => mem_frameNames_pre hx) hvargs) ?_
  rintro ⟨pc4, L4, m4, o4⟩ ⟨hpc4, ho4, hk4, pp⟩
  simp only at hpc4 ho4 hk4 pp; subst hpc4 ho4
  have g14' := hk4.has (by decide) g14
  have k14' := has_mem g14' (by decide); have e14' := srcVal_of_has g14'
  simp only [a4] at k14' e14'
  apply run_whole hR.fits (sMv.cast (pos' := q + 14 + 8 * cd.params.length) (by omega))
  wp_simp [k14', e14']
  -- the invariant in the function's frame
  have hdd : (maxCallDepth - (d + 1)) * maxFS + maxFS = (maxCallDepth - d) * maxFS := by
    rw [← Nat.succ_mul]; congr 1; omega
  have hfr3 : (st.store.allocFrame (some cd.env)).1.frames[st.store.frames.size]? = some ⟨some cd.env, []⟩ := by
    simp [Store.allocFrame]
  obtain ⟨frb, hfrb, hpb⟩ := pp.shape.2 _ _ hfr3
  have hgrow : Grows V.F st.store (V.F ++ [(V.hF, frameNames cd.params cd.body)]) (entryStore st.store cd vs) :=
    hg3.trans (Grows.of_shape pp.shape)
  have hobj4 : ObjAgree m0 m4 V.h := hob3.trans (pp.out.obj (h := V.h) hroomF) (Nat.le_refl _)
  have hkey : Keep [t4, t5, t6] L3 L4 := hk4
  have hlen' : st.store.frames.size = V.F.length := hm.rel.len.symm
  have hrdsp : ∀ b, b % 8 = 0 → V.hF + 8 + 16 * (frameNames cd.params cd.body).length ≤ b → rdW m4 b =
      rdW (applyW (applyW m0 (sp - frameSize cd.body, 8, r))
        (sp - frameSize cd.body + 8, 8, BitVec.ofNat 64 (V.fa env))) b := fun b hb hb' => by
    exact (pp.out b hb (.inr hb')).trans (hout3 b hb (.inr hb'))
  refine reach_here (.inr ⟨by simp only [fnBody], ?_, ?_, ?_, ?_, hobj4, ⟨hgrow, List.prefix_refl _, by
    simp only [View.enter]; omega, by simp only [View.enter]; omega⟩⟩)
  · have hfaE : (V.enter (frameNames cd.params cd.body)).fa st.store.frames.size = V.hF :=
      View.fa_eq (V := V.enter (frameNames cd.params cd.body)) hF3
    have hcl : (entryStore st.store cd vs).closures = st.store.closures := by
      rw [show entryStore st.store cd vs = (cd.params.zip vs).foldl (fun s p => s.define st.store.frames.size p.1 p.2)
        (st.store.allocFrame (some cd.env)).1 from rfl, pp.clo]; rfl
    have hroom' : stackLo + (maxCallDepth - (d + 1)) * maxFS + frameSize cd.body ≤ sp := by omega
    exact {
      rel := pp.rel
      img := hm.img.transport hobj4 (Nat.le_refl _) hm.img.ptr
      clo := hm.clo.grow hm.rel.clo hobj4 hgrow rfl hcl (fun b ⟨fr, hb'⟩ =>
        View.fa_append (by rw [← hlen']; exact (Array.getElem?_eq_some_iff.mp hb').1))
      chn := ChainL.push (hchain.grow hgrow) hfrb (by rw [hpb]) hF3
      out := hm.out
      ho := by reg_simp []; exact hkey.has (by decide) (hk3.has (by decide) (by reg_simp []; exact hm.ho))
      hf := by reg_simp []; exact hkey.has (by decide) g23
      henv := by rw [hfaE]; reg_simp []
      hsp := by reg_simp []; exact hkey.has (by decide) (hk3.has (by decide) (by reg_simp []))
      hdep := by reg_simp []; exact hkey.has (by decide) (hk3.has (by decide) (by reg_simp []))
      stk := ⟨by omega, by omega, by omega, by omega, by omega⟩
      hfal := by simp only [View.enter]; omega }
  · rw [hrdsp _ (by omega) (by omega), rdW_upd (a := sp - frameSize cd.body + 8) (by omega) (by omega),
      if_neg (by omega), rdW_upd (a := sp - frameSize cd.body) (by omega) (by omega), if_pos rfl]
  · rw [hrdsp _ (by omega) (by omega), rdW_upd (a := sp - frameSize cd.body + 8) (by omega) (by omega),
      if_pos rfl]
  · intro b h1' h2' h3'
    rw [hrdsp _ h3' (by omega), rdW_upd (a := sp - frameSize cd.body + 8) (by omega) h3',
      if_neg (by omega), rdW_upd (a := sp - frameSize cd.body) (by omega) h3', if_neg (by omega)]

end

end Vsa.Compiler
