import VsaIris.Interp.CallCloRuns
import VsaIris.Interp.ExecOom

/-!
# The closure call's parameter binding (lane E4)

From `env_new`'s return (`0x800032c0`) to `jal value_null(sp+144)`
(`0x80003328`): `argc` tested, then one `env_define(frame, params[j], &arg_j)`
per argument, the argument copied to `sp+64` first (`CloB_run0`,
`CloB_runL`, `CloB_runR`).

`cloBind` is Wp-generic and abstracts the `env_define` call
(`CloDefineStep`): the total case instantiates it with `ms_callEnvDefine`
(credits `defineCost`), the partial one with `ms_callEnvDefineP` (out of
memory through `wp_oomBlock`). The store advances as the semantics' fold
(`Call.closure`: `(params.zip vs).foldl (·.define frame ·.1 ·.2)`).

* `CloSpills`: the eval prologue's spills and the call arm's (`s3`, `s5`,
  `s7`), which every run of the path keeps.
* `CloPL`: the loop head's state; `CloPD`: the state at `jal value_null`.
-/

namespace VsaIris.Interp

open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Newlib
open Vsa.MemRepr Vsa.Sim Vsa.While

/-- The spilled words the closure path keeps (`[sp+1016, sp+1088)` but
`s4`/`s6`'s slots): the prologue's `ra`, `s0`-`s2` and the arm's `s3`, `s5`,
`s7`. -/
structure CloSpills (Mt : Mem) (s ret : BitVec 64) (rv : Nat → BitVec 64) : Prop where
  saved : CallSaved Mt s ret (rv 8) (rv 9) (rv 18)
  s3 : ldv .ld Mt (s.toNat - 1088 + 1048) = rv 19
  s5 : ldv .ld Mt (s.toNat - 1088 + 1032) = rv 21
  s7 : ldv .ld Mt (s.toNat - 1088 + 1016) = rv 23

/-- The spills survive a memory agreeing on their words (`[sp+1016, sp+1088)`
but `s6`'s and `s4`'s slots, which the error paths and the loop use). -/
theorem CloSpills.agree {Mt Mt' : Mem} {s ret : BitVec 64} {rv : Nat → BitVec 64}
    (h : CloSpills Mt s ret rv)
    (hag : ∀ k, s.toNat - 1088 + 1016 ≤ k → k < s.toNat - 1088 + 1088 →
      (k < s.toNat - 1088 + 1024 ∨ s.toNat - 1088 + 1032 ≤ k) →
      (k < s.toNat - 1088 + 1040 ∨ s.toNat - 1088 + 1048 ≤ k) → imgM Mt' k = imgM Mt k) :
    CloSpills Mt' s ret rv :=
  ⟨⟨(ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.saved.ra,
    (ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.saved.s0,
    (ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.saved.s1,
    (ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.saved.s2⟩,
   (ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.s3,
   (ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.s5,
   (ldv_agree fun j hj => hag _ (by omega) (by omega) (by omega) (by omega)).trans h.s7⟩

/-- An element of a represented parameter array. -/
theorem paramsRepr_get {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ps : List String}, ParamsReprWithin m P a n ps →
      ∀ j (h : j < ps.length), ∃ p, read64 m (a + 8 * j) = some p ∧ CStringWithin m P p ps[j]
  | _, _, _, .nil, j, h => absurd h (by simp)
  | _, _, _, .cons hp _ hs _, 0, _ => ⟨_, by simpa using hp, hs⟩
  | a, _, _, .cons _ _ _ hrest, j + 1, h => by
    obtain ⟨p, hp, hs⟩ := paramsRepr_get hrest j (by simpa using h)
    exact ⟨p, by rw [show a + 8 * (j + 1) = a + 8 + 8 * j by omega]; exact hp, hs⟩

/-- Every byte of a represented parameter array's pointers is in the view
and present. -/
theorem paramsRepr_covers {m : Mem} {P : Nat → Prop} :
    ∀ {a n : Nat} {ps : List String}, ParamsReprWithin m P a n ps →
      ∀ k, k < 8 * n → P (a + k) ∧ (m[a + k]?).isSome
  | _, _, _, .nil, k, h => absurd h (by omega)
  | a, _, _, .cons hp cp _ hrest, k, h => by
    by_cases hk : k < 8
    · exact ⟨cp k hk, isSome_of_readLE hp hk⟩
    · obtain ⟨h1, h2⟩ := paramsRepr_covers hrest (k - 8) (by omega)
      rw [show a + 8 + (k - 8) = a + k by omega] at h1 h2
      exact ⟨h1, h2⟩

/-- `sext`-free offsets of the loop's loads. -/
theorem sign_extend_8 : LeanRV64DExecutable.Functions.sign_extend (m := 64) 8#12 = 8#64 := by decide
theorem sign_extend_16 : LeanRV64DExecutable.Functions.sign_extend (m := 64) 16#12 = 16#64 := by decide

theorem ofNat_add8 (a : Nat) : BitVec.ofNat 64 a + 8#64 = BitVec.ofNat 64 (a + 8) := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-- The frame without the parameter slot `sp+64` (`env_define`'s value). -/
abbrev cloSlot64 (s : BitVec 64) : Nat → Prop :=
  fun k => InExt (s.toNat - 1088, 1088) k ∧ ¬ InExt (s.toNat - 1088 + 64, 24) k

/-- The parameter loop's head (`0x800032dc`) at parameter `j`: `s0` the
argument's slot, `a5 = 8j`, `s6 = 8·argc` (the caller's `s6` spilled at
`sp+1024`), the frame in `s3`, the node in `s5`; the argument array as at the
dispatch (`Mt0`). -/
structure CloPL (R : Nat → BitVec 64) (Mt Mt0 : Mem) (s inp sret ret fr q line : BitVec 64)
    (rv : Nat → BitVec 64) (argc j : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  s0 : (R 8).toNat = s.toNat - 1088 + 240 + 24 * j
  a5 : R 15 = BitVec.ofNat 64 (8 * j)
  s6 : R 22 = BitVec.ofNat 64 (8 * argc)
  s1 : R 9 = sret
  s2 : R 18 = inp
  s3 : R 19 = fr
  s5 : R 21 = q
  s7 : R 23 = line
  keep : ∀ x ∈ [20, 24, 25, 26, 27], R x = rv x
  spills : CloSpills Mt s ret rv
  s6m : ldv .ld Mt (s.toNat - 1088 + 1024) = rv 22
  args : ∀ a, InExt (argsBase s, 24 * argc) a → imgM Mt a = imgM Mt0 a

/-- The state at `jal value_null(sp+144)` (`0x80003328`), the parameters
bound. -/
structure CloPD (R : Nat → BitVec 64) (Mt : Mem) (s inp sret ret fr q line : BitVec 64)
    (rv : Nat → BitVec 64) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  a0 : R 10 = s + 18446744073709550528#64 + 144#64
  s1 : R 9 = sret
  s2 : R 18 = inp
  s3 : R 19 = fr
  s5 : R 21 = q
  s7 : R 23 = line
  keep : ∀ x ∈ [20, 22, 24, 25, 26, 27], R x = rv x
  spills : CloSpills Mt s ret rv

/-- The state at `env_new`'s return (`0x800032c0`): `a0` the new frame,
`argc` at `sp+0`, the argument array as at the dispatch (`Mt0`). -/
structure CloEN (R : Nat → BitVec 64) (Mt Mt0 : Mem) (s inp sret ret fr q line : BitVec 64)
    (rv : Nat → BitVec 64) (argc : Nat) : Prop where
  sp : R 2 = s + 18446744073709550528#64
  a0 : R 10 = fr
  s1 : R 9 = sret
  s2 : R 18 = inp
  s5 : R 21 = q
  s7 : R 23 = line
  keep : ∀ x ∈ [20, 22, 24, 25, 26, 27], R x = rv x
  spills : CloSpills Mt s ret rv
  argcm : ldv .ld Mt (s.toNat - 1088) = BitVec.ofNat 64 argc
  args : ∀ a, InExt (argsBase s, 24 * argc) a → imgM Mt a = imgM Mt0 a

theorem ofNat_shl3 {a : Nat} (h : a ≤ 32) : BitVec.ofNat 64 a <<< 3 = BitVec.ofNat 64 (8 * a) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  omega

section Loop

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode VsaIris.Inst Vsa.RuntimeRepr

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- **One parameter's `env_define`, abstract**: from `jal env_define` with
`a0` the frame, `a1` the name, `a2 = sp+64` holding the value, the step's
resources `W st ((x, v) :: rest)` become `W (st.define fa x v) rest` at the
return. The total case supplies it with `ms_callEnvDefine`, the partial one
with `ms_callEnvDefineP`. -/
def CloDefineStep (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (W : Store → List (String × Value) → IProp GF) (s fr : BitVec 64) (fa n : Nat) :
    Prop :=
  ∀ (R : Nat → BitVec 64) (Mt : Mem) (st : Store) (x : String) (v : Value)
    (rest : List (String × Value)),
    R 2 = s + 18446744073709550528#64 → R 10 = fr → (R 12).toNat = s.toNat - 1088 + 64 →
    codeRes ∗ ms 0x80003310#64 R (cloSlot64 s) Mt ∗ W st ((x, v) :: rest) ∗
      valAt N (R 12).toNat v ∗ □ strAt (R 11).toNat x ∗ stackScratch (s + 18446744073709550528#64) n ∗
      (∀ R' : Nat → BitVec 64, ⌜∀ y ∈ fRegs, y ∉ (10 :: retClob) → R' y = R y⌝ -∗
        stackScratch (s + 18446744073709550528#64) n -∗ valAt N (R 12).toNat v -∗
        W (st.define fa x v) rest -∗
        ms (BitVec.ofNat 64 (0x80003310 + 4)) (upd R' 1 (BitVec.ofNat 64 (0x80003310 + 4)))
          (cloSlot64 s) Mt -∗ Wp.W Φ)
    ⊢ Wp.W Φ

/-- **One parameter** (`0x800032dc` round the back edge), for either WP: the
argument `v` copied to `sp+64`, `env_define(frame, x, sp+64)` (abstract,
`CloDefineStep`), then the next parameter's head or, after the last, the
state at `jal value_null(sp+144)`. -/
theorem cloParamStep (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {W : Store → List (String × Value) → IProp GF}
    {s inp sret ret fr q line prm : BitVec 64} {rv R : Nat → BitVec 64} {Mt Mt0 : Mem}
    {argc j n fa pj : Nat} {P : Nat → Prop} {m : Mem} {st : Store} {x : String} {v : Value}
    {rest : List (String × Value)}
    (hfg : EvalFrameG s) (hc : argc ≤ 32) (hj : j < argc)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (hqv : ∀ a ∈ accAddrs (q.toNat + 16) 8, P a ∧ (m[a]?).isSome)
    (hprm : ldv .ld m (q + 16#64).toNat = prm)
    (hpv : ∀ k, k < 8 → P (prm.toNat + 8 * j + k) ∧ (m[prm.toNat + 8 * j + k]?).isSome)
    (hpg : ∀ k, P k → ReadOK k)
    (hpj : read64 m (prm.toNat + 8 * j) = some pj)
    (hcl : CloPL R Mt Mt0 s inp sret ret fr q line rv argc j)
    (hdef : CloDefineStep Wp Φ N W s fr fa n) :
    codeRes ∗ roOn P m ∗ □ valImg N (imgM Mt0) (argsBase s + 24 * j) v ∗ □ strAt pj x ∗
      ms 0x800032dc#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ W st ((x, v) :: rest) ∗
      stackScratch (s + 18446744073709550528#64) n ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜j + 1 < argc ∧ CloPL R' Mt' Mt0 s inp sret ret fr q line rv argc (j + 1)⌝ -∗
          ms 0x800032dc#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ W (st.define fa x v) rest -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜j + 1 = argc ∧ CloPD R' Mt' s inp sret ret fr q line rv⌝ -∗
          ms 0x80003328#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ W (st.define fa x v) rest -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ))
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off' hfg
  have g0 := hpg _ (hpv 0 (by omega)).1
  have g7 := hpg _ (hpv 7 (by omega)).1
  have hpo : (prm + BitVec.ofNat 64 (8 * j)).toNat = prm.toNat + 8 * j := by
    have := g7.hi
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8 * j) (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hs0 := hcl.s0
  have hq8 : (R 8 + LeanRV64DExecutable.Functions.sign_extend 8#12).toNat =
      s.toNat - 1088 + 240 + 24 * j + 8 := by
    rw [sign_extend_8, BitVec.toNat_add, hs0]; simp only [BitVec.toNat_ofNat]; omega
  have hq16 : (R 8 + LeanRV64DExecutable.Functions.sign_extend 16#12).toNat =
      s.toNat - 1088 + 240 + 24 * j + 16 := by
    rw [sign_extend_16, BitVec.toNat_add, hs0]; simp only [BitVec.toNat_ofNat]; omega
  iintro ⟨#Hcode, #Hro, #Hv, #Hstr, Hms, HW, Hst, Hk⟩
  ihave #Hdv := roOwn_data (DA := accAddrs (q.toNat + 16) 8 ++ accAddrs (prm.toNat + 8 * j) 8)
    (fun a ha => by
      simp only [List.mem_append] at ha
      rcases ha with ha | ha
      · exact hqv a ha
      · obtain ⟨h1, h2⟩ := mem_accAddrs_iff.1 ha
        obtain ⟨k, rfl⟩ : ∃ k, a = prm.toNat + 8 * j + k := ⟨a - (prm.toNat + 8 * j), by omega⟩
        exact hpv k (by omega)) $$ [Hcode Hro]
  · iframe Hcode Hro
  iapply wp_swpF Wp (F := iprop(codeRes ∗ □ valImg N (imgM Mt0) (argsBase s + 24 * j) v ∗
      □ strAt pj x ∗ W st ((x, v) :: rest) ∗
      stackScratch (s + 18446744073709550528#64) n ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜j + 1 < argc ∧ CloPL R' Mt' Mt0 s inp sret ret fr q line rv argc (j + 1)⌝ -∗
          ms 0x800032dc#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ W (st.define fa x v) rest -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜j + 1 = argc ∧ CloPD R' Mt' s inp sret ret fr q line rv⌝ -∗
          ms 0x80003328#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ W (st.define fa x v) rest -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ))))
  rotate_left
  · iframe Hdv Hms Hcode Hv Hstr HW Hst; iexact Hk
  intro F'
  refine CloB_runL (pa := R 8) (off := BitVec.ofNat 64 (8 * j)) (qa := s.toNat - 1088 + 240 + 24 * j)
    (qp := prm.toNat + 8 * j) hlive hsf hs hs2 hs3 hq1 hq2 hq3 g0.lo (by have := g7.hi; omega)
    (by have := g0.off; have := g7.off; omega) rfl hcl.s5 hcl.a5 hcl.sp hprm hpo hs0 hq8 hq16
    (by omega) (by omega) (by omega) ?_
  apply swp_closeRM
  intro R1 Mt1 hR1 hMt1
  unfold F'
  iintro ⟨⟨#Hcode, #Hv, #Hstr, HW, Hst, Hk⟩, Hms⟩
  -- the copied value out as `valAt` at `sp+64`
  have hout : ∀ k, (k < s.toNat - 1088 + 64 ∨ s.toNat - 1088 + 88 ≤ k) →
      (k < s.toNat - 1088 ∨ s.toNat - 1088 + 8 ≤ k) → imgM Mt1 k = imgM Mt k := by
    intro k h1 h2
    rw [hMt1, imgM_store_miss _ _ (by rw [hoff 80 (by decide)]; omega), imgM_store_miss _ _ (by omega),
      imgM_store_miss _ _ (by rw [hoff 72 (by decide)]; omega),
      imgM_store_miss _ _ (by rw [hoff 64 (by decide)]; omega)]
  have hMt1' : Mt1 = writeLog (writeLog (writeLog (writeLog Mt
      [(s.toNat - 1088 + 64, 8, ldv .ld Mt (s.toNat - 1088 + 240 + 24 * j))])
      [(s.toNat - 1088 + 72, 8, ldv .ld Mt (s.toNat - 1088 + 240 + 24 * j + 8))])
      [(s.toNat - 1088, 8, BitVec.ofNat 64 (8 * j))])
      [(s.toNat - 1088 + 80, 8, ldv .ld Mt (s.toNat - 1088 + 240 + 24 * j + 16))] := by
    rw [hMt1, hoff 64 (by decide), hoff 72 (by decide), hoff 80 (by decide)]
  have hmiss : ∀ (M : Mem) (a b w : Nat) (u : BitVec 64), a + 8 ≤ b ∨ b + w ≤ a →
      ldv .ld (writeLog M [(b, w, u)]) a = ldv .ld M a := fun M a b w u h =>
    ldv_store_miss .ld M u (by simp only [widthOfM]; omega)
  have eA : ∀ o, o < 3 → ldv .ld Mt (s.toNat - 1088 + 240 + 24 * j + 8 * o) =
      imgW (imgM Mt0) (argsBase s + 24 * j + 8 * o) := fun o ho => by
    rw [ldv_ld_imgW]
    exact imgW_agree fun i hi => hcl.args _ (by simp only [InExt, argsBase]; omega)
  have hw0 : imgW (imgM Mt1) (s.toNat - 1088 + 64) = imgW (imgM Mt0) (argsBase s + 24 * j) := by
    rw [← ldv_ld_imgW, hMt1', hmiss _ _ _ _ _ (by omega), hmiss _ _ _ _ _ (by omega),
      hmiss _ _ _ _ _ (by omega), ldv_store_hit]
    simpa using eA 0 (by omega)
  have hw1 : imgW (imgM Mt1) (s.toNat - 1088 + 64 + 8) =
      imgW (imgM Mt0) (argsBase s + 24 * j + 8) := by
    rw [← ldv_ld_imgW, hMt1', hmiss _ _ _ _ _ (by omega), hmiss _ _ _ _ _ (by omega),
      show s.toNat - 1088 + 64 + 8 = s.toNat - 1088 + 72 by omega, ldv_store_hit]
    simpa using eA 1 (by omega)
  have hw2 : imgW (imgM Mt1) (s.toNat - 1088 + 64 + 16) =
      imgW (imgM Mt0) (argsBase s + 24 * j + 16) := by
    rw [← ldv_ld_imgW, hMt1', show s.toNat - 1088 + 64 + 16 = s.toNat - 1088 + 80 by omega,
      ldv_store_hit]
    simpa using eA 2 (by omega)
  ihave ⟨Hms, Hval⟩ := ms_carveVal N (S := InExt (s.toNat - 1088, 1088)) (a := s.toNat - 1088 + 64)
    (b := argsBase s + 24 * j)
    (img := imgM Mt0) (v := v) (fun k hk => by simp only [InExt] at hk ⊢; omega)
    hw0 hw1 hw2 $$ [Hms Hv]
  · iframe Hms Hv
  have h2' : R1 2 = s + 18446744073709550528#64 := by rw [hR1]; ix_reg; exact hcl.sp
  have h10' : R1 10 = fr := by rw [hR1]; ix_reg; exact hcl.s3
  have h12' : (R1 12).toNat = s.toNat - 1088 + 64 := by rw [hR1]; ix_reg; exact hoff 64 (by decide)
  have hpjl : pj < 2 ^ 64 := by have := readLE_lt hpj; simpa using this
  have h11' : (R1 11).toNat = pj := by
    rw [hR1]; ix_reg; rw [ldv_ld_read64 hpj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hpjl]
  ihave Hval := (show valAt (GF := GF) N (s.toNat - 1088 + 64) v ⊢ valAt N (R1 12).toNat v by
    rw [h12']) $$ Hval
  ihave #Hstr' := (show strAt (GF := GF) pj x ⊢ strAt (R1 11).toNat x by rw [h11']) $$ Hstr
  -- `env_define`
  iapply hdef R1 Mt1 st x v rest h2' h10' h12'
  iframe Hcode Hms HW Hval Hstr' Hst
  iintro %R' %hk Hst Hval HW Hms
  ihave Hval := (show valAt (GF := GF) N (R1 12).toNat v ⊢ valAt N (s.toNat - 1088 + 64) v by
    rw [h12']) $$ Hval
  ihave ⟨%M2, Hms, %hM2⟩ := ms_uncarveVal N (S := InExt (s.toNat - 1088, 1088))
    (a := s.toNat - 1088 + 64) (fun k hk => by simp only [InExt] at hk ⊢; omega) $$ [Hms Hval]
  · iframe Hms Hval
  have hag : ∀ k, InExt (s.toNat - 1088, 1088) k → ¬ InExt (s.toNat - 1088 + 64, 24) k →
      (k < s.toNat - 1088 ∨ s.toNat - 1088 + 8 ≤ k) → imgM M2 k = imgM Mt k := fun k h1 h2 h3 =>
    (hM2 k h1 h2).trans (hout k (by simp only [InExt] at h2; omega) h3)
  have hkp : ∀ y ∈ fRegs, y ∉ (10 :: retClob) → upd R' 1 (BitVec.ofNat 64 (0x80003310 + 4)) y = R1 y :=
    fun y hy hc => by
      have : y ≠ 1 := fun h => by subst h; simp at hy
      simp only [upd_apply, this, ite_false]; exact hk y hy hc
  have h2'' : upd R' 1 (BitVec.ofNat 64 (0x80003310 + 4)) 2 = s + 18446744073709550528#64 :=
    (hkp 2 (by decide) (by decide)).trans h2'
  have h22'' : upd R' 1 (BitVec.ofNat 64 (0x80003310 + 4)) 22 = BitVec.ofNat 64 (8 * argc) := by
    rw [hkp 22 (by decide) (by decide), hR1]; ix_reg; exact hcl.s6
  have hO : ldv .ld M2 (s.toNat - 1088) = BitVec.ofNat 64 (8 * j) := by
    rw [ldv_agree (M' := Mt1) fun i hi => hM2 _ (by simp only [InExt]; omega)
      (by simp only [InExt]; omega), hMt1', hmiss _ _ _ _ _ (by omega), ldv_store_hit]
  have h1024 : ldv .ld M2 (s + 18446744073709550528#64 + 1024#64).toNat = rv 22 := by
    rw [hoff 1024 (by decide), ldv_agree (M' := Mt) fun i hi => hag _ (by simp only [InExt]; omega)
      (by simp only [InExt]; omega) (by omega)]
    exact hcl.s6m
  have hsp' : CloSpills M2 s ret rv := hcl.spills.agree fun k h1 h2 _ _ =>
    hag k (by simp only [InExt]; omega) (by simp only [InExt]; omega) (by omega)
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  -- the back edge
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(W (st.define fa x v) rest ∗
      stackScratch (s + 18446744073709550528#64) n ∗
      ((∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜j + 1 < argc ∧ CloPL R' Mt' Mt0 s inp sret ret fr q line rv argc (j + 1)⌝ -∗
          ms 0x800032dc#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ W (st.define fa x v) rest -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ) ∧
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem),
          ⌜j + 1 = argc ∧ CloPD R' Mt' s inp sret ret fr q line rv⌝ -∗
          ms 0x80003328#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗ W (st.define fa x v) rest -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ))))
  rotate_left
  · rw [hro]; iframe Hcode Hms HW Hst; iexact Hk
  intro F'
  have hkeep1 : ∀ y ∈ [9, 18, 19, 20, 21, 23, 24, 25, 26, 27], R' y = R y := fun y hy => by
    rw [hk y ((by decide : ∀ z ∈ [9, 18, 19, 20, 21, 23, 24, 25, 26, 27], z ∈ fRegs) y hy)
      ((by decide : ∀ z ∈ [9, 18, 19, 20, 21, 23, 24, 25, 26, 27], z ∉ 10 :: retClob) y hy), hR1]
    simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg
  have h2R : R' 2 = s + 18446744073709550528#64 := (hk 2 (by decide) (by decide)).trans h2'
  have h22R : R' 22 = BitVec.ofNat 64 (8 * argc) := by
    rw [hk 22 (by decide) (by decide), hR1]; ix_reg; exact hcl.s6
  refine CloB_runR (m := ∅) (j := j) (argc := argc) hlive hsf hs hs2 hs3 hj hc h2'' h22'' hO h1024 ?_ ?_
  · intro hne
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    subst hR3
    rw [hMt3]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h22R, ofNat_add8] at hne
    have hlt : j + 1 < argc := by
      refine Nat.lt_of_le_of_ne hj fun h => hne ?_
      rw [← h, show 8 * (j + 1) = 8 * j + 8 by omega]
    have hcl' : CloPL (upd (upd (upd R' 1 (BitVec.ofNat 64 (0x80003310 + 4))) 15
        (BitVec.ofNat 64 (8 * j))) 15 (BitVec.ofNat 64 (8 * j) + 8#64)) M2 Mt0 s inp sret ret fr q
        line rv argc (j + 1) := by
      refine ⟨by ix_reg; exact h2R, ?_, ?_, by ix_reg; exact h22R, ?_, ?_, ?_, ?_, ?_, ?_, hsp',
        ?_, ?_⟩
      · ix_reg
        rw [hk 8 (by decide) (by decide), hR1]; ix_reg
        rw [BitVec.toNat_add, hs0]; simp only [BitVec.toNat_ofNat]; omega
      · ix_reg; rw [ofNat_add8]; congr 1
      · ix_reg; rw [hkeep1 9 (by decide)]; exact hcl.s1
      · ix_reg; rw [hkeep1 18 (by decide)]; exact hcl.s2
      · ix_reg; rw [hkeep1 19 (by decide)]; exact hcl.s3
      · ix_reg; rw [hkeep1 21 (by decide)]; exact hcl.s5
      · ix_reg; rw [hkeep1 23 (by decide)]; exact hcl.s7
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;>
          (ix_reg; rw [hkeep1 _ (by decide)]; exact hcl.keep _ (by decide))
      · rw [ldv_agree (M' := Mt) fun i hi => hag _ (by simp only [InExt]; omega)
          (by simp only [InExt]; omega) (by omega)]
        exact hcl.s6m
      · intro a ha
        rw [hag a (by simp only [InExt, argsBase] at ha ⊢; omega)
          (by simp only [InExt, argsBase] at ha ⊢; omega) (by simp only [InExt, argsBase] at ha; omega)]
        exact hcl.args a ha
    unfold F'
    iintro ⟨⟨HW, Hst, Hk⟩, Hms⟩
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ %_ %M2 %⟨hlt, hcl'⟩ Hms HW Hst
  · intro heq
    apply swp_closeRM
    intro R3 Mt3 hR3 hMt3
    subst hR3
    rw [hMt3]
    simp only [upd_apply, Nat.reduceEqDiff, ite_true, ite_false, h22R, ofNat_add8, ne_eq,
      Decidable.not_not] at heq
    have hj1 : j + 1 = argc := by
      have := congrArg BitVec.toNat heq
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      omega
    have hpd : CloPD (upd (upd (upd (upd (upd R' 1 (BitVec.ofNat 64 (0x80003310 + 4))) 15
        (BitVec.ofNat 64 (8 * j))) 15 (BitVec.ofNat 64 (8 * j) + 8#64)) 22 (rv 22)) 10
        (s + 18446744073709550528#64 + 144#64)) M2 s inp sret ret fr q line rv := by
      refine ⟨by ix_reg; exact h2R, by ix_reg, ?_, ?_, ?_, ?_, ?_, ?_, hsp'⟩
      · ix_reg; rw [hkeep1 9 (by decide)]; exact hcl.s1
      · ix_reg; rw [hkeep1 18 (by decide)]; exact hcl.s2
      · ix_reg; rw [hkeep1 19 (by decide)]; exact hcl.s3
      · ix_reg; rw [hkeep1 21 (by decide)]; exact hcl.s5
      · ix_reg; rw [hkeep1 23 (by decide)]; exact hcl.s7
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
        · ix_reg; rw [hkeep1 _ (by decide)]; exact hcl.keep _ (by decide)
        · ix_reg
        all_goals (ix_reg; rw [hkeep1 _ (by decide)]; exact hcl.keep _ (by decide))
    unfold F'
    iintro ⟨⟨HW, Hst, Hk⟩, Hms⟩
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ %_ %M2 %⟨hj1, hpd⟩ Hms HW Hst

/-- An element of an argument array's values. -/
theorem argVals_get (N : NativeAddrs) (img : Nat → BitVec 8) (base : Nat) :
    ∀ (i : Nat) (vs : List Value) (j : Nat) (h : j < vs.length),
      argVals (GF := GF) N img base i vs ⊢ valImg N img (base + 24 * (i + j)) vs[j]
  | _, [], _, h => absurd h (by simp)
  | i, v :: vs, 0, _ => by
    unfold argVals
    simp only [Nat.add_zero, List.getElem_cons_zero]
    iintro ⟨#H, -⟩
    iexact H
  | i, v :: vs, j + 1, h => by
    unfold argVals
    have hr := argVals_get N img base (i + 1) vs j (by simpa using h)
    rw [show i + (j + 1) = i + 1 + j by omega, List.getElem_cons_succ]
    iintro ⟨-, #H⟩
    iapply hr
    iexact H

/-- **The parameter loop** (`0x800032dc`), for either WP: from parameter
`j`, every remaining `(param, argument)` pair is defined in the frame
(`CloDefineStep`), in order; the loop leaves at `jal value_null(sp+144)` with
the store the semantics' fold gives (`Call.closure`). -/
theorem cloParamLoop (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {W : Store → List (String × Value) → IProp GF}
    {s inp sret ret fr q line prm : BitVec 64} {rv : Nat → BitVec 64} {Mt0 : Mem}
    {argc n fa : Nat} {P : Nat → Prop} {m : Mem} {ps : List String} {vs : List Value}
    (hfg : EvalFrameG s) (hc : argc ≤ 32)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (hqv : ∀ a ∈ accAddrs (q.toNat + 16) 8, P a ∧ (m[a]?).isSome)
    (hprm : ldv .ld m (q + 16#64).toNat = prm)
    (hps : ParamsReprWithin m P prm.toNat argc ps) (hpg : ∀ k, P k → ReadOK k) (hwin : SharedWin P)
    (hlen : vs.length = argc) (hdef : CloDefineStep Wp Φ N W s fr fa n) :
    ∀ (k j : Nat), argc - j = k → j < argc → ∀ (R : Nat → BitVec 64) (Mt : Mem) (st : Store),
      CloPL R Mt Mt0 s inp sret ret fr q line rv argc j →
      codeRes ∗ roOn P m ∗ argVals N (imgM Mt0) (argsBase s) 0 vs ∗
        ms 0x800032dc#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ W st ((ps.zip vs).drop j) ∗
        stackScratch (s + 18446744073709550528#64) n ∗
        (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜CloPD R' Mt' s inp sret ret fr q line rv⌝ -∗
          ms 0x80003328#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗
          W (((ps.zip vs).drop j).foldl (fun t p => t.define fa p.1 p.2) st) [] -∗
          stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ)
      ⊢ Wp.W Φ := by
  have hpl := paramsRepr_length hps
  intro k
  induction k with
  | zero => intro j hk hj; omega
  | succ k ih =>
    intro j hk hj R Mt st hcl
    obtain ⟨pj, hrd, hcs⟩ := paramsRepr_get hps j (by omega)
    have hzip : (ps.zip vs).drop j = (ps[j]'(by omega), vs[j]'(by omega)) :: (ps.zip vs).drop (j + 1) := by
      rw [List.drop_eq_getElem_cons (by simp; omega)]
      simp [List.getElem_zip]
    have hpv : ∀ k, k < 8 → P (prm.toNat + 8 * j + k) ∧ (m[prm.toNat + 8 * j + k]?).isSome := fun k hk' => by
      have := paramsRepr_covers hps (8 * j + k) (by omega)
      rwa [← Nat.add_assoc] at this
    rw [hzip, List.foldl_cons]
    by_cases hlast : j + 1 = argc
    · have e : (ps.zip vs).drop (j + 1) = [] := List.drop_eq_nil_of_le (by simp; omega)
      rw [e, List.foldl_nil]
      iintro ⟨#Hcode, #Hro, #Hav, Hms, HW, Hst, Hk⟩
      ihave #Hv := argVals_get N (imgM Mt0) (argsBase s) 0 vs j (by omega) $$ Hav
      rw [Nat.zero_add]
      ihave #Hstr := strAt_of_cstringWithin hcs hwin $$ Hro
      iapply cloParamStep hlive Wp hfg hc hj hq1 hq2 hq3 hqv hprm hpv hpg hrd hcl hdef
      iframe Hcode Hro Hv Hstr Hms HW Hst
      isplit
      · iintro %R' %Mt' %⟨hlt, _⟩
        exact absurd hlt (by omega)
      · iintro %R' %Mt' %⟨_, hpd⟩ Hms HW Hst
        iapply Hk $$ %R' %Mt' %hpd Hms HW Hst
    · iintro ⟨#Hcode, #Hro, #Hav, Hms, HW, Hst, Hk⟩
      ihave #Hv := argVals_get N (imgM Mt0) (argsBase s) 0 vs j (by omega) $$ Hav
      rw [Nat.zero_add]
      ihave #Hstr := strAt_of_cstringWithin hcs hwin $$ Hro
      iapply cloParamStep hlive Wp hfg hc hj hq1 hq2 hq3 hqv hprm hpv hpg hrd hcl hdef
      iframe Hcode Hro Hv Hstr Hms HW Hst
      isplit
      · iintro %R' %Mt' %⟨hlt, hcl'⟩ Hms HW Hst
        iapply ih (j + 1) (by omega) hlt R' Mt' _ hcl'
        iframe Hcode Hro Hav Hms HW Hst
        iexact Hk
      · iintro %R' %Mt' %⟨heq, _⟩
        exact absurd heq hlast

/-- **The parameters bound** (`0x800032c0` to `jal value_null(sp+144)`), for
either WP: `s3 = frame`, then each `(param, argument)` pair defined in order
(`cloParamLoop`); the store is the semantics' fold. -/
theorem cloBind (hlive : ∀ p ∈ interpText, live p.1) (Wp : MachWP (GF := GF) (vsaModel live))
    {Φ : Nat × String → IProp GF} {N : NativeAddrs} {W : Store → List (String × Value) → IProp GF}
    {s inp sret ret fr q line prm : BitVec 64} {rv R : Nat → BitVec 64} {Mt Mt0 : Mem}
    {argc n fa : Nat} {P : Nat → Prop} {m : Mem} {ps : List String} {vs : List Value} {st : Store}
    (hfg : EvalFrameG s) (hc : argc ≤ 32)
    (hq1 : 0x80000000 ≤ q.toNat) (hq2 : q.toNat + 40 ≤ 0x100000000)
    (hq3 : q.toNat + 40 ≤ tohostAddr ∨ tohostAddr + 16 ≤ q.toNat)
    (hqv : ∀ a ∈ accAddrs (q.toNat + 16) 8, P a ∧ (m[a]?).isSome)
    (hprm : ldv .ld m (q + 16#64).toNat = prm)
    (hps : ParamsReprWithin m P prm.toNat argc ps) (hpg : ∀ k, P k → ReadOK k) (hwin : SharedWin P)
    (hlen : vs.length = argc) (hdef : CloDefineStep Wp Φ N W s fr fa n)
    (hen : CloEN R Mt Mt0 s inp sret ret fr q line rv argc) :
    codeRes ∗ roOn P m ∗ argVals N (imgM Mt0) (argsBase s) 0 vs ∗
      ms 0x800032c0#64 R (InExt (s.toNat - 1088, 1088)) Mt ∗ W st (ps.zip vs) ∗
      stackScratch (s + 18446744073709550528#64) n ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜CloPD R' Mt' s inp sret ret fr q line rv⌝ -∗
        ms 0x80003328#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗
        W ((ps.zip vs).foldl (fun t p => t.define fa p.1 p.2) st) [] -∗
        stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hsf := hfg.sf; have hs := hfg.lo; have hs2 := hfg.hi; have hs3 := hfg.al
  have hoff := evalSP_off' hfg
  have hpl := paramsRepr_length hps
  have hro : roOwn (GF := GF) roR (interpText ++ dataOf ∅ []) = codeRes := by
    unfold codeRes; simp [dataOf]
  iintro ⟨#Hcode, #Hro, #Hav, Hms, HW, Hst, Hk⟩
  iapply wp_swpF Wp (text := interpText ++ dataOf ∅ []) (F := iprop(codeRes ∗ roOn P m ∗
      argVals N (imgM Mt0) (argsBase s) 0 vs ∗ W st (ps.zip vs) ∗
      stackScratch (s + 18446744073709550528#64) n ∗
      (∀ (R' : Nat → BitVec 64) (Mt' : Mem), ⌜CloPD R' Mt' s inp sret ret fr q line rv⌝ -∗
        ms 0x80003328#64 R' (InExt (s.toNat - 1088, 1088)) Mt' -∗
        W ((ps.zip vs).foldl (fun t p => t.define fa p.1 p.2) st) [] -∗
        stackScratch (s + 18446744073709550528#64) n -∗ Wp.W Φ)))
  rotate_left
  · rw [hro]; iframe Hcode Hro Hav Hms HW Hst; iexact Hk
  intro F'
  have htoI : (BitVec.ofNat 64 argc).toInt = argc := ofNat_toInt_small (by omega)
  refine CloB_run0 (m := ∅) hlive hsf hs hs2 hs3 hen.a0 hen.sp hen.argcm ?_ ?_
  · -- no arguments
    intro hle
    apply swp_closeRM
    intro R1 Mt1 hR1 hMt1
    subst hR1
    rw [hMt1]
    have h0 : argc = 0 := by rw [htoI] at hle; simp at hle; omega
    have hz : ps.zip vs = [] := by
      rw [List.eq_nil_of_length_eq_zero (show ps.length = 0 by omega)]; simp
    have hpd : CloPD (upd (upd (upd R 15 (BitVec.ofNat 64 argc)) 19 fr) 10
        (s + 18446744073709550528#64 + 144#64)) Mt s inp sret ret fr q line rv := by
      refine ⟨by ix_reg; exact hen.sp, by ix_reg, by ix_reg; exact hen.s1, by ix_reg; exact hen.s2,
        by ix_reg, by ix_reg; exact hen.s5, by ix_reg; exact hen.s7, ?_, hen.spills⟩
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> (ix_reg; exact hen.keep _ (by decide))
    unfold F'
    iintro ⟨⟨#Hcode, #Hro, #Hav, HW, Hst, Hk⟩, Hms⟩
    ihave HW := (show W st (ps.zip vs) ⊢ W ((ps.zip vs).foldl (fun t p => t.define fa p.1 p.2) st) []
      by rw [hz]; exact .rfl) $$ HW
    iapply Hk $$ %_ %Mt %hpd Hms HW Hst
  · -- the loop
    intro hgt
    apply swp_closeRM
    intro R1 Mt1 hR1 hMt1
    subst hR1
    rw [hMt1]
    have hpos : 0 < argc := by rw [htoI] at hgt; simp at hgt; omega
    have hmiss : ∀ k, (k < s.toNat - 1088 + 1024 ∨ s.toNat - 1088 + 1032 ≤ k) →
        imgM (writeLog Mt [((s + 18446744073709550528#64 + 1024#64).toNat, 8, R 22)]) k = imgM Mt k :=
      fun k hk => imgM_store_miss _ _ (by rw [hoff 1024 (by decide)]; omega)
    have hcl : CloPL (upd (upd (upd (upd (upd R 15 (BitVec.ofNat 64 argc)) 19 fr) 8
        (s + 18446744073709550528#64 + 240#64)) 22 (BitVec.ofNat 64 argc <<< 3)) 15 0#64)
        (writeLog Mt [((s + 18446744073709550528#64 + 1024#64).toNat, 8, R 22)]) Mt0 s inp sret ret
        fr q line rv argc 0 := by
      refine ⟨by ix_reg; exact hen.sp, by ix_reg; rw [hoff 240 (by decide)],
        by first | (ix_reg; done) | (ix_reg; rfl),
        by ix_reg; exact ofNat_shl3 hc, by ix_reg; exact hen.s1, by ix_reg; exact hen.s2, by ix_reg,
        by ix_reg; exact hen.s5, by ix_reg; exact hen.s7, ?_, ?_, ?_, ?_⟩
      · intro y hy
        simp only [List.mem_cons, List.not_mem_nil, _root_.or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl <;> (ix_reg; exact hen.keep _ (by decide))
      · exact hen.spills.agree fun k _ _ h3 _ => hmiss k h3
      · rw [← hoff 1024 (by decide), ldv_store_hit]; exact hen.keep 22 (by decide)
      · intro a ha
        rw [hmiss a (by simp only [InExt, argsBase] at ha; omega)]
        exact hen.args a ha
    have hl := cloParamLoop hlive Wp (W := W) (Φ := Φ) (ps := ps) (vs := vs) hfg hc hq1 hq2 hq3
      hqv hprm hps hpg hwin hlen hdef argc 0 (Nat.sub_zero _) hpos _ _ st hcl
    rw [List.drop_zero] at hl
    unfold F'
    iintro ⟨⟨#Hcode, #Hro, #Hav, HW, Hst, Hk⟩, Hms⟩
    iapply hl
    iframe Hcode Hro Hav Hms HW Hst
    iexact Hk

end Loop

end VsaIris.Interp
