import VsaIris.Interp.CallCloExit

/-!
# The closure call, total mode (lane E4)

`cloDefineStepT`: the parameter loop's `env_define` (`CloDefineStep`) in the
counted regime: `ms_callEnvDefine`, the world's credits the remaining
`bindParamsCost` plus the body's.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While
open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr VsaIris.VsaHeap

section Total

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}


/-- The closures' body bound, from the store's pure part. -/
theorem storeRepr_bodies (N : NativeAddrs) (st : Store) (B : List (Nat × Nat)) :
    storeRepr (GF := GF) N st B ⊢ ⌜StoreBodiesBound st perCallBudget⌝ := by
  unfold storeRepr
  iintro ⟨%mf, %mc, %Bs, -, -, %hp, -, -⟩
  ipureintro; exact hp.bodies

/-- The stack below `eval_expr`'s frame, as the closure loop states it. -/
theorem StackGeom.lowerE {s : BitVec 64} {n : Nat} (h : StackGeom s n) (hn : 1088 ≤ n)
    (hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088) :
    StackGeom (s + 18446744073709550528#64) (n - 1088) := by
  have h1 := h.le; have h2 := h.lo; have h3 := h.hi; have h4 := h.al; have h5 := h.top
  simp only [Vsa.Sim.LayoutInstance.stackSL] at h2 h3
  refine ⟨by rw [hsf]; omega, ?_, ?_, ?_, ?_⟩ <;> rw [hsf] <;>
    (try simp only [Vsa.Sim.LayoutInstance.stackSL]) <;> omega

/-- A helper's `sp` below `eval_expr`'s frame. -/
theorem envSp_eval {s : BitVec 64} (hfg : EvalFrameG s) {need : Nat} (h : need ≤ 4096) :
    EnvSp (s + 18446744073709550528#64) need := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  refine ⟨?_, ?_, ?_⟩ <;> rw [hsf] <;> (try unfold htifLo) <;> omega

/-- An empty body's derivation. -/
theorem execSeqCost_nil_inv {st st' : St} {d inner : Nat} {status : Status} {n : Nat}
    (h : ExecSeqCost st d inner [] st' status n) : st' = st ∧ status = .normal ∧ n = 0 := by
  cases h; exact ⟨rfl, rfl, rfl⟩

/-- `CloAt` across G's loop: its kept registers and the spills' invariant. -/
theorem CloAt.of_keep {R R' : Nat → BitVec 64} {Mt Mt' : Mem} {s inp sret ret : BitVec 64}
    {rv : Nat → BitVec 64} (h : CloAt R Mt s inp sret ret rv) (hk : KeepRegs closureKeep R R')
    (hsv : CloSpills Mt' s ret rv) : CloAt R' Mt' s inp sret ret rv :=
  ⟨(hk 2 (by decide)).trans h.sp, (hk 9 (by decide)).trans h.s1, (hk 18 (by decide)).trans h.s2,
    fun x hx => (hk x ((by decide : ∀ y ∈ [20, 22, 24, 25, 26, 27], y ∈ closureKeep) x hx)).trans
      (h.keep x hx), hsv⟩

/-- The parameter loop's resources, counted: the frame's binding and the world
at the body's depth, with credits for the remaining definitions and the body. -/
def cloWT (N : NativeAddrs) (inp k nb d : Nat) (out : String) (fa : Nat) (fr : BitVec 64)
    (st : Store) (rest : List (String × Value)) : IProp GF :=
  iprop(□ frameAt fa fr.toNat ∗
    world N vsaLayoutP vsaRoomB inp (.counted (k + bindParamsCost st fa rest + nb)) ⟨st, out⟩ (d + 1))

/-- **`env_define` of one parameter, counted** (`jal env_define` at
`0x80003310`). -/
theorem cloDefineStepT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp k nb d : Nat} {out : String} {s fr : BitVec 64} {fa n : Nat}
    (hed : ⊢ envDefineSpec (GF := GF) (twpW (vsaModel live)) N)
    (hfg : EvalFrameG s) (hn1 : envDefineNeed ≤ n) (hn2 : n ≤ s.toNat - 1088) :
    CloDefineStep (twpW (vsaModel live)) Φ N (cloWT N inp k nb d out fa fr) s fr fa n := by
  intro R Mt st x v rest h2 h10 h12
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  unfold cloWT
  simp only [bindParamsCost]
  rw [show k + (defineCost st fa x + bindParamsCost (st.define fa x v) fa rest) + nb =
    k + bindParamsCost (st.define fa x v) fa rest + nb + defineCost st fa x by omega]
  have hle : n ≤ (R 2).toNat := by rw [h2, hsf]; exact hn2
  have hsp : EnvSp (R 2) envDefineNeed := by rw [h2]; exact envSp_eval hfg (by decide)
  have hpv : SlotWin (R 12).toNat :=
    ⟨by rw [h12]; omega, by rw [h12]; omega, by rw [h12]; unfold htifLo; omega, by rw [h12]; omega⟩
  rw [← h2]
  iintro ⟨#Hcode, Hms, ⟨#Hfr, Hw⟩, Hval, #Hstr, Hst, Hk⟩
  ihave ⟨Hw, #Hcx⟩ := world_codeX N vsaLayoutP vsaRoomB inp _ ⟨st, out⟩ (d + 1) $$ Hw
  ihave ⟨Hh, Hc, Hio, Hi, #Hb⟩ := (world_heapStore N inp _ ⟨st, out⟩ (d + 1)).1 $$ Hw
  ihave ⟨Hsl, Hst⟩ := stackScratch_narrow (s := R 2) hle hn1 $$ Hst
  ihave #Hed := hed
  iapply ms_callEnvDefine (twpW _) (i := 0x80003310)
    (jalx_80003310 live (fun p hp => hlive _ (interp_code_80003310 p hp))) interp_code_80003310
    (by decide) (k := k + bindParamsCost (st.define fa x v) fa rest + nb) (st := st) (fa := fa)
    (x := x) (v := v) (R := R) hsp hpv
  iframe Hed Hcode Hcx Hms Hst Hstr Hval Hh
  isplitl []
  · rw [h10]; iexact Hfr
  iintro %R' %hk Hst Hval Hh Hms
  ihave Hst := stackScratch_widen (s := R 2) hle hn1 $$ [Hsl Hst]
  · iframe Hsl Hst
  iapply Hk $$ %R' %hk Hst Hval [Hh Hc Hio Hi] Hms
  iframe Hfr
  iapply (world_heapStore N inp _ ⟨st.define fa x v, out⟩ (d + 1)).2
  iframe Hh Hc Hio Hi Hb

/-- **The closure call after its head, total mode**: from the `jal env_new`
(`CloHd`, the depth word bumped in the run's bytes) with the world's closer
at the depth word: the world back at `d + 1`, the fresh frame
(`ms_callEnvNewW`), the parameters (`cloBind`), the body (`cloBodyEntry`,
G's `closureSeqT_body`), the exits (`cloExitN`, `cloExitR`). -/
theorem cloCallT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {st2 st' : St} {d k nb : Nat} {cd : ClosureData}
    {vs : List Value} {store' : Store} {frame : Addr} {status : Status} {v : Value}
    {s aX sret ret e q line prm bod nam : BitVec 64} {rv R1 : Nat → BitVec 64} {Mt Mt1 : Mem}
    {n : Nat} {P : Nat → Prop} {m : Mem}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p)
    (hen : ⊢ envNewSpec (GF := GF) (twpW (vsaModel live)) N)
    (hed : ⊢ envDefineSpec (GF := GF) (twpW (vsaModel live)) N)
    (hlen : vs.length = cd.params.length) (hd : d < maxCallDepth)
    (halloc : st2.store.allocFrame (some cd.env) = (store', frame))
    (Dseq : ExecSeqCost ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st2.out⟩ (d + 1) frame cd.body st' status nb)
    (hst : status = .normal ∧ v = .null ∨ status = .ret v)
    (hseq : closureSeqT_body (GF := GF) live N vsaLayoutP vsaRoomB inp
      ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st2.out⟩ (d + 1) frame
      cd.body st' status nb Dseq)
    (hbb : Stmt.stackNeedList cd.body ≤ perCallBudget ∧ Stmt.bodiesBoundList perCallBudget cd.body = true)
    (hfg : EvalFrameG s) (hsg : StackGeom s n) (hn1 : 1088 + envDefineNeed ≤ n)
    (hnb : ∀ x ∈ cd.body, execNeed x (d + 1) + 1088 ≤ n)
    (hal : ret.toNat % 4 = 0) (hsp : rv 2 = s) (hinpG : RtErr.InpGeom (BitVec.ofNat 64 inp))
    (hinpL : inp < 2 ^ 64) (hinpA : inp % 8 = 0) (hslg : SlotGeom sret)
    (hi3 : inp + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp + 8)
    (hfn : FnNode m P q cd.params.length prm bod nam)
    (hps : ParamsReprWithin m P prm.toNat cd.params.length cd.params)
    (hbr : StmtReprWithin m P bod.toNat (.block cd.body)) (hpg : ∀ k, P k → ReadOK k)
    (hwin : SharedWin P) (hargc : vs.length ≤ 32)
    (hhd : CloHd R1 Mt1 Mt s aX sret (BitVec.ofNat 64 inp) ret e q line rv vs.length d) :
    codeRes ∗ roOn P m ∗ □ frameAt cd.env e.toNat ∗ argVals N (imgM Mt) (argsBase s) 0 vs ∗
      ms 0x800032bc#64 R1 (cloS s (BitVec.ofNat 64 inp)) Mt1 ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗
      (∀ (d' : Nat) (img' : Nat → BitVec 8), ownImg (InExt (inp + 8, 4)) img' -∗
          ⌜imgLE img' (inp + 8) 4 = d' ∧ d' ≤ maxCallDepth⌝ -∗
          world N vsaLayoutP vsaRoomB inp
            (.counted (k + (envBytes + bindParamsCost store' frame (cd.params.zip vs) + nb))) st2 d') ∗
      slot24 sret.toNat ∗
      CallExitK live N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ rv s n sret v (.counted k) st' d ret
    ⊢ (twpW (vsaModel live)).W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hinpL
  have hle : n - 1088 ≤ (s + 18446744073709550528#64).toNat := by rw [hsf]; have := hsg.le; omega
  have hsz : st2.store.frames.size = frame := congrArg Prod.snd halloc
  have hst' : (st2.store.allocFrame (some cd.env)).1 = store' := congrArg Prod.fst halloc
  rw [show k + (envBytes + bindParamsCost store' frame (cd.params.zip vs) + nb) =
    k + bindParamsCost store' frame (cd.params.zip vs) + nb + envBytes by omega]
  unfold CallExitK
  iintro ⟨#Hcode, #Hro, #Hfe, #Hav, Hms, Hst, Hcl, Hsr, Hk⟩
  -- the depth word back to the world, at `d + 1`
  ihave Hms := ms_iff (T := fun b => InExt (s.toNat - 1088, 1088) b ∨ InExt (inp + 8, 4) b)
    (fun k => by simp only [cloS]; rw [hinpN]) $$ Hms
  ihave ⟨Hms, Hd⟩ := ms_split (S := InExt (s.toNat - 1088, 1088)) (T := InExt (inp + 8, 4))
    (fun a h1 h2 => by simp only [InExt] at h1 h2; omega) $$ Hms
  ihave Hw := Hcl $$ %(d + 1) %(imgM Mt1) Hd %⟨by have := hhd.depth; rwa [hinpN] at this, by omega⟩
  -- `env_new(cl->env)`
  have h2 : R1 2 = s + 18446744073709550528#64 := hhd.sp
  have hspN : EnvSp (R1 2) envNewNeed := by rw [h2]; exact envSp_eval hfg (by decide)
  have hnN : envNewNeed ≤ n - 1088 := by
    have := hn1; unfold envDefineNeed allocHeadroom at this; unfold envNewNeed allocHeadroom; omega
  rw [← h2]
  ihave ⟨Hsl, Hst⟩ := stackScratch_narrow (s := R1 2) (by rw [h2]; exact hle) hnN $$ Hst
  ihave #Hen := hen
  iapply ms_callEnvNewW (twpW _) (i := 0x800032bc)
    (jalx_800032bc live (fun p hp => hlive _ (interp_code_800032bc p hp))) interp_code_800032bc
    (by decide) (k := k + bindParamsCost store' frame (cd.params.zip vs) + nb) (st := st2) (d := d + 1)
    (env := cd.env) (R := R1) hspN
  iframe Hen Hcode Hms Hst Hw
  isplitl []
  · rw [hhd.a0]; iexact Hfe
  iintro %R2 %hk2 Hst Hw #Hnew Hms
  ihave Hst := stackScratch_widen (s := R1 2) (by rw [h2]; exact hle) hnN $$ [Hsl Hst]
  · iframe Hsl Hst
  rw [hst', hsz, h2]
  -- the parameters
  have hkp : ∀ y ∈ fRegs, y ∉ 10 :: retClob →
      upd R2 1 (BitVec.ofNat 64 (0x800032bc + 4)) y = R1 y := fun y hy hc => by
    have : y ≠ 1 := fun h => by subst h; simp at hy
    simp only [upd_apply, this, ite_false]; exact hk2 y hy hc
  have hEN : CloEN (upd R2 1 (BitVec.ofNat 64 (0x800032bc + 4))) Mt1 Mt s (BitVec.ofNat 64 inp) sret
      ret (R2 10) q line rv cd.params.length :=
    ⟨(hkp 2 (by decide) (by decide)).trans hhd.sp, by ix_reg,
      (hkp 9 (by decide) (by decide)).trans hhd.s1, (hkp 18 (by decide) (by decide)).trans hhd.s2,
      (hkp 21 (by decide) (by decide)).trans hhd.s5, (hkp 23 (by decide) (by decide)).trans hhd.s7,
      fun x hx => (hkp x ((by decide : ∀ y ∈ [20, 22, 24, 25, 26, 27], y ∈ fRegs) x hx)
        ((by decide : ∀ y ∈ [20, 22, 24, 25, 26, 27], y ∉ 10 :: retClob) x hx)).trans
        (hhd.keep x ((by decide : ∀ y ∈ [20, 22, 24, 25, 26, 27], y ∈ [19, 20, 22, 24, 25, 26, 27]) x hx)),
      ⟨hhd.saved, hhd.s3m, hhd.s5m, hhd.s7m⟩, hlen ▸ hhd.argcm, hlen ▸ hhd.args⟩
  have hqv : ∀ o, o = 16 ∨ o = 32 → ∀ a ∈ accAddrs (q.toNat + o) 8, P a ∧ (m[a]?).isSome := by
    intro o ho a ha
    refine hfn.view a ?_
    simp only [fnView, List.mem_append, mem_accAddrs_iff] at ha ⊢
    omega
  have hdef := cloDefineStepT (Φ := Φ) (N := N) (inp := inp) (k := k) (nb := nb) (d := d)
    (out := st2.out) (fr := R2 10) (fa := frame) (n := n - 1088) hlive hed hfg
    (by have := hn1; omega) (by have := hsg.le; omega)
  iapply cloBind hlive (twpW _) (W := cloWT N inp k nb d st2.out frame (R2 10)) (ps := cd.params)
    (vs := vs) (st := store') hfg (by omega) hfn.lo hfn.hi hfn.off (hqv 16 (.inl rfl)) hfn.prm hps
    hpg hwin hlen hdef hEN
  iframe Hcode Hro Hav Hms Hst
  isplitl [Hw]
  · unfold cloWT; iframe Hnew Hw
  iintro %R3 %Mt3 %hpd Hms HW Hst
  unfold cloWT
  simp only [bindParamsCost, Nat.add_zero]
  icases HW with ⟨#Hnew2, Hw⟩
  -- the body
  have hfold : (cd.params.zip vs).foldl (fun t p => t.define frame p.1 p.2) store' =
      (cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store' := rfl
  rw [hfold]
  iapply cloBodyEntry hlive (twpW _) hvn hfg hfn.lo hfn.hi hfn.off (hqv 32 (.inr rfl)) hfn.bod hbr hpg hpd
    (iprop(world N vsaLayoutP vsaRoomB inp (.counted (k + nb))
      ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st2.out⟩ (d + 1) ∗
      stackScratch (s + 18446744073709550528#64) (n - 1088) ∗ slot24 sret.toNat ∗
      (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
        stackScratch s n -∗ valAt N sret.toNat v -∗
        world N vsaLayoutP vsaRoomB inp (.counted k) st' d -∗ PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗
        (twpW (vsaModel live)).W Φ)))
  iframe Hcode Hro Hms
  isplitl [Hw Hst Hsr Hk]
  · iframe Hw Hst Hsr Hk
  isplit
  · -- a nonempty body: G's loop, then its exits
    iintro %R4 %Mt4 %arr %count %⟨hne, hbn, hch, hat⟩ HF Hms Hslot
    have hall : ∀ x ∈ cd.body, execNeed x (d + 1) ≤ n - 1088 ∧ x.bodiesBound perCallBudget = true :=
      fun x hx => ⟨by have := hnb x hx; omega, Stmt.bodiesBound_of_mem hbb.2 hx⟩
    have hinv : ∀ M, CloSpills M s ret rv →
        CloSpills (writeLog M [(s.toNat - 1088, 8, bod)]) s ret rv := fun M hM =>
      hM.agree fun k h1 _ _ _ => imgM_store_miss _ _ (by omega)
    icases HF with ⟨Hw, Hst, Hsr, Hk⟩
    iapply hseq Φ k 0 count bod arr (R2 10) s R4 Mt4 m P cd.body (n - 1088)
      (fun M => CloSpills M s ret rv)
      (iprop(slot24 sret.toNat ∗
        (∀ rv' : Nat → BitVec 64, ⌜KeepRegs calleeSaved rv rv'⌝ -∗ regFile rv' -∗
          stackScratch s n -∗ valAt N sret.toNat v -∗
          world N vsaLayoutP vsaRoomB inp (.counted k) st' d -∗ PC ↦ᵣ ret -∗ ra ↦ᵣ ret -∗
          (twpW (vsaModel live)).W Φ)))
      hne List.drop_zero.symm hbn hch hfg
      (hsg.lowerE (by have := hn1; omega) hsf) hall (cloSlotGeom hfg) hat.spills hinv
    iframe Hms Hcode Hro Hnew2 Hst Hslot Hw
    isplitl [Hsr Hk]
    · iframe Hsr Hk
    iintro %R5 %Mt5 %⟨hk5, h10, hinv5⟩ ⟨Hsr, Hk⟩ Hms Hst Hret Hw
    have hat5 := hat.of_keep hk5 hinv5
    rcases hst with ⟨rfl, rfl⟩ | rfl
    · rw [closureExit_normal]
      simp only [statusRet]
      iapply cloExitN hlive (twpW _) hvn hfg hsg (by have := hn1; omega) hal hsp hinpG hinpL hinpA hslg hat5
      iframe Hcode Hms Hret Hsr Hw Hst
      iexact Hk
    · rw [closureExit_abrupt (by simp)]
      simp only [statusRet]
      iapply cloExitR hlive (twpW _) hfg hsg (by have := hn1; omega) hal hsp hinpG hinpL hinpA hslg hat5 h10
      iframe Hcode Hms Hret Hsr Hw Hst
      iexact Hk
  · -- an empty body: the normal end at once
    iintro %R4 %Mt4 %⟨hb0, hat⟩ HF Hms Hslot
    obtain ⟨rfl, rfl, rfl⟩ := execSeqCost_nil_inv (hb0 ▸ Dseq)
    rcases hst with ⟨-, rfl⟩ | hr
    · icases HF with ⟨Hw, Hst, Hsr, Hk⟩
      rw [Nat.add_zero]
      iapply cloExitN hlive (twpW _) hvn hfg hsg (by have := hn1; omega) hal hsp hinpG hinpL hinpA hslg hat
      iframe Hcode Hms Hslot Hsr Hw Hst
      iexact Hk
    · cases hr


/-- A run's owned bytes are disjoint from any other owned bytes. -/
theorem ms_disj {pc : BitVec 64} {R : Nat → BitVec 64} {S T : Nat → Prop} {Mt : Mem}
    {g : Nat → BitVec 8} :
    ms (GF := GF) pc R S Mt ∗ ownSet T (fun a => a ↦ₘ g a) ⊢
      ms pc R S Mt ∗ ownSet T (fun a => a ↦ₘ g a) ∗ ⌜∀ a, S a → ¬ T a⌝ := by
  unfold ms
  iintro ⟨⟨Hpc, Hra, Hregs, HS⟩, HT⟩
  ihave ⟨⟨HS, HT⟩, %hd⟩ := keep_pure (ownSet_disj S T (imgM Mt) g) $$ [HS HT]
  · iframe HS HT
  iframe Hpc Hra Hregs HS HT
  ipureintro; exact hd

/-- **The closure call from the kind dispatch, total mode** (`0x80003254` on
a closure value): the closure's resources (`CloSupply`), the store's body
bound, the depth word out of the world, `callCloHead` (the derivation refutes
the arity and depth errors), then `cloCallT`. -/
theorem callClosureT (hlive : ∀ p ∈ interpText, live p.1) {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {inp : Nat} {st2 st' : St} {d k nb : Nat} {ca : Addr} {cd : ClosureData}
    {vs : List Value} {store' : Store} {frame : Addr} {status : Status} {v : Value}
    {f : Expr} {args : List Expr} {s aX sret ret w0 w1 w2 : BitVec 64} {rv R : Nat → BitVec 64}
    {Mt : Mem}
    (hvn : ⊢ ∀ p, valueNullSpec (GF := GF) (vsaModel live) N (twpW (vsaModel live)) p)
    (hen : ⊢ envNewSpec (GF := GF) (twpW (vsaModel live)) N)
    (hed : ⊢ envDefineSpec (GF := GF) (twpW (vsaModel live)) N)
    (hsup : CloSupply (GF := GF) N)
    (hcl : st2.store.closures[ca]? = some cd) (hlen : vs.length = cd.params.length)
    (hd : d < maxCallDepth) (halloc : st2.store.allocFrame (some cd.env) = (store', frame))
    (Dseq : ExecSeqCost ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store',
      st2.out⟩ (d + 1) frame cd.body st' status nb)
    (hst : status = .normal ∧ v = .null ∨ status = .ret v)
    (hseq : closureSeqT_body (GF := GF) live N vsaLayoutP vsaRoomB inp
      ⟨(cd.params.zip vs).foldl (fun s (x, v) => s.define frame x v) store', st2.out⟩ (d + 1) frame
      cd.body st' status nb Dseq)
    (hsg : StackGeom s (evalNeed (.call f args) d)) (hal : ret.toNat % 4 = 0) (hsp : rv 2 = s)
    (hinpG : RtErr.InpGeom (BitVec.ofNat 64 inp)) (hinpL : inp < 2 ^ 64) (hinpA : inp % 8 = 0)
    (hslg : SlotGeom sret)
    (hcall : CallAt R Mt s aX sret (BitVec.ofNat 64 inp) ret rv w0 w1 w2 vs.length)
    (hargc : vs.length ≤ 32) :
    codeRes ∗ □ astEG aX.toNat (.call f args) ∗ □ valOf N (.closure ca) w0 w1 w2 ∗
      argVals N (imgM Mt) (argsBase s) 0 vs ∗ ms 0x80003254#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗
      stackScratch (s + 18446744073709550528#64) (evalNeed (.call f args) d - 1088) ∗
      world N vsaLayoutP vsaRoomB inp
        (.counted (k + (envBytes + bindParamsCost store' frame (cd.params.zip vs) + nb))) st2 d ∗
      slot24 sret.toNat ∗
      CallExitK live N vsaLayoutP vsaRoomB inp (twpW (vsaModel live)) Φ rv s (evalNeed (.call f args) d)
        sret v (.counted k) st' d ret
    ⊢ (twpW (vsaModel live)).W Φ := by
  have hge := evalNeed_call_ge f args d
  have hs := hsg.lo; have hs2 := hsg.hi; have hs3 := hsg.al; have hs4 := hsg.le
  unfold Vsa.Sim.LayoutInstance.stackSL at hs hs2
  simp only at hs hs2
  have hsF : s - 1088#64 = s + 18446744073709550528#64 := evalSP_eq s
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := by
    rw [← hsF]; exact toNat_sub_frame (by simp only [BitVec.toNat_ofNat]; omega)
  have hfg : EvalFrameG s := ⟨hsf, by omega, hs2, hs3⟩
  have hinpN : (BitVec.ofNat 64 inp).toNat = inp := Nat.mod_eq_of_lt hinpL
  iintro ⟨#Hcode, #Hast, #Hv, #Hav, Hms, Hst, Hw, Hsr, Hk⟩
  -- the closure's resources and the body bound
  unfold valOf
  icases Hv with ⟨%⟨hk4, hw1⟩, #Hca⟩
  ihave ⟨%B, Hs, Hcw⟩ := world_store N vsaLayoutP vsaRoomB inp _ st2 d $$ Hw
  ihave ⟨Hs, #Hres⟩ := hsup st2.store B ca w1.toNat $$ [Hs Hca]
  · iframe Hs Hca
  ihave ⟨Hs, %hbod⟩ := keep_pure (storeRepr_bodies N st2.store B) $$ Hs
  ihave Hw := Hcw $$ Hs
  unfold CloRes
  icases Hres with ⟨%cd', %q, %e, %img, %P, %m, %hcf, #Himg, #Hro, #Hfe⟩
  have hcd : cd' = cd := by have := hcf.lookup; rw [hcl] at this; exact (Option.some.inj this).symm
  subst hcd
  obtain ⟨hbb1, hbb2⟩ := hbod ca cd' hcl
  -- the depth word
  have hwd := world_depth (GF := GF) N vsaLayoutP vsaRoomB inp
    (.counted (k + (envBytes + bindParamsCost store' frame (cd'.params.zip vs) + nb))) st2 d
  rw [show inp + interpDepthOff = (BitVec.ofNat 64 inp).toNat + 8 by rw [hinpN]; rfl] at hwd
  ihave ⟨%dimg, Hd, %⟨hdv, hdle⟩, Hcl⟩ := hwd $$ Hw
  ihave ⟨Hms, Hd, %hdisj⟩ := ms_disj $$ [Hms Hd]
  · iframe Hms Hd
  have hi3 : inp + 8 + 4 ≤ s.toNat - 1088 ∨ s.toNat ≤ inp + 8 := by
    refine Classical.byContradiction fun hc => ?_
    exact hdisj (max (s.toNat - 1088) (inp + 8)) (by simp only [InExt]; omega)
      (by simp only [InExt]; rw [hinpN]; omega)
  -- the `EX_FN` node
  have hqlt : q < 2 ^ 64 := by rw [← hcf.fn]; have := imgLE_lt img w1.toNat 8; omega
  have hqt : (BitVec.ofNat 64 q).toNat = q := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hqlt]
  have helt : e < 2 ^ 64 := by rw [← hcf.env]; have := imgLE_lt img (w1.toNat + 8) 8; omega
  have het : (BitVec.ofNat 64 e).toNat = e := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt helt]
  have hrepq : ExprReprWithin m P (BitVec.ofNat 64 q).toNat (.fn cd'.name cd'.params cd'.body) := by
    rw [hqt]; exact hcf.repr
  obtain ⟨prm, bod, nam, hfn, hprl, hbdl, -, hps, hbody, -⟩ := fnNode_of hrepq hcf.geo
  have hprt : (BitVec.ofNat 64 prm).toNat = prm := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hprl]
  have hbdt : (BitVec.ofNat 64 bod).toNat = bod := by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hbdl]
  -- the head
  iapply callCloHead hlive (twpW _) hcall hargc hk4 hcf hinpG (by rw [hinpN]; exact hinpA) hdv hdle hfg
  iframe Hcode Hast Himg Hro Hms Hd
  unfold CloHeadK
  isplit
  · iintro %R1 %Mt1 %line %⟨hpl, hdl1, hhd⟩ Hms
    iapply cloCallT hlive hvn hen hed hlen hd halloc Dseq hst hseq ⟨hbb1, hbb2⟩ hfg hsg
      (by unfold envDefineNeed allocHeadroom; omega)
      (fun x hx => by have := execNeed_callBody (f := f) (args := args) hd hbb1 hx; unfold evalFrame at this; omega)
      hal hsp hinpG hinpL hinpA hslg hi3 (by rw [← hlen] at hfn; exact hlen ▸ hfn)
      (by rw [hprt]; exact hps) (by rw [hbdt]; exact hbody) hcf.geo hcf.win hargc hhd
    iframe Hcode Hro Hav Hms Hst Hsr
    isplitl []
    · rw [het]; iexact Hfe
    isplitl [Hcl]
    · rw [show inp + 8 = (BitVec.ofNat 64 inp).toNat + 8 by rw [hinpN]]
      iexact Hcl
    iexact Hk
  isplit
  · iintro %R1 %Mt1 %line %⟨hne, -⟩
    exact absurd hlen.symm (by rw [← hlen] at hne; exact fun h => hne (by rw [hlen]))
  · iintro %R1 %Mt1 %line %⟨hgt, -⟩
    exact absurd hgt (by omega)

end Total

end VsaIris.Interp
