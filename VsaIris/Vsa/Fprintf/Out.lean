import VsaIris.Vsa.Fprintf.Fmts
import VsaIris.Vsa.Stdout.StrOut
import VsaIris.Vsa.InterpImg
import Vsa.Sim.SnprintfSpec39
import VsaIris.Vsa.Stderr.FprintfSpec

/-!
# `out.fprintf`, proved (lane N5)

`fprintf_out`: `NewlibOut.outSpec` for `fprintf(stdout, fmt, arg)` with
`value_print`'s formats (`fprintfOut`), through `outSpec_of_run`:

* the run's data view (`soDt`) holds `_impure_ptr` (`impureRO`), the
  `.rodata` it reads (the three formats, the decimal point `"."`, the
  conversion jump table), the interpreter's code and tables (`interpText`:
  the arithmetic helpers of the digit loop) and, for `%s`, the name up to its
  NUL (`strAt`). Its image is `_impure_ptr`, else the binary, else the
  name's bytes (`soImg`); where they overlap they agree (`roImg_agree`);
* `"%lld"` runs `fprintf_lld` (`putcs (lldBytes v) = intToString v.toInt`),
  `"<fn %s>"`/`"<native fn %s>"` run `fprintf_s`;
* `stdout` may be unoriented at entry (`StdioOK`: `_flags` `0x000a` or
  `0x200a`, `consoleMt_of`); `_vfprintf_r` orients it (`vfp_outer`);
* the end state is `OutEnd` (`outEnd_of`): the frame `FpReg`, `stdout`'s
  pointer and count untouched, its flags oriented (`0x200a`).
-/

namespace VsaIris.Sym.Fp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open Vsa.MemRepr Vsa.Sim VsaIris.Interp VsaIris.MallocFast VsaIris.Stdio VsaIris.Newlib VsaIris.Inst
open Vsa.While (natToString intToString natDigits)

/-! ## What `%lld` prints -/

theorem putcs_digBytes (n : Nat) : putcs (digBytes n) = natToString n := by
  have hc : ∀ c ∈ natDigits (n + 1) n, c.toNat < 256 := fun c hc => by
    have := natDigits_ascii_39 (n + 1) n c hc; omega
  unfold digBytes chByte
  rw [putcs_chars _ hc]
  apply String.toList_injective
  rw [String.toList_ofList, natToString_toList_39]

theorem putcs_lldBytes (v : BitVec 64) : putcs (lldBytes v) = intToString v.toInt := by
  rw [intToString_of_bv]
  unfold lldBytes lldMag
  by_cases h : 2 ^ 63 ≤ v.toNat
  · have hn : isNeg v := h
    rw [if_pos hn, if_pos hn, if_pos h, putcs_append, putcs_digBytes, BitVec.zero_sub]
    rfl
  · have hn : ¬ isNeg v := h
    rw [if_neg hn, if_neg hn, if_neg h, List.nil_append, putcs_digBytes]

/-- A signed halfword load of a small value is the unsigned one. -/
theorem ldv_lhu_of_lh {M : Mem} {a v : Nat} (hv : v < 2 ^ 15) (h : ldv .lh M a = BitVec.ofNat 64 v) :
    ldv .lhu M a = BitVec.ofNat 64 v := by
  rw [ldv_lh_img] at h; rw [ldv_lhu_img]
  have hw := imgLE_lt (imgM M) a 2
  generalize imgLE (imgM M) a 2 = w at h hw ⊢
  have h3 := congrArg BitVec.toNat h
  simp only [LeanRV64DExecutable.Functions.sign_extend, Sail.BitVec.signExtend, BitVec.toNat_signExtend,
    BitVec.toNat_setWidth, BitVec.toNat_ofNat] at h3
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  split at h3 <;> omega

/-! ## The data view -/

/-- The data view's image: `_impure_ptr`, else the binary's `.text`/`.rodata`,
else `bv` (the name's bytes). -/
def soImg (bv : Nat → BitVec 8) (a : Nat) : BitVec 8 :=
  if impureW a then impureByte a else if textDom a then textByte a else if rodataDom a then rodataByte a
  else bv a

/-- The `.rodata` the run reads: the formats (`0x800192c0`, `0x800192c8`,
`0x800192d8`), the decimal point, the conversion jump table. -/
abbrev soRo : List Nat := accAddrs 0x800192c0 40 ++ accAddrs 0x80019770 2 ++ accAddrs 0x8001a288 364

/-- The data view's addresses: `_impure_ptr`, the `.rodata` read, the
interpreter's code and tables, the string `sa`. -/
abbrev soDA (sa : List Nat) : List Nat :=
  accAddrs 0x8001b970 8 ++ soRo ++ interpText.map Prod.fst ++ sa

/-- The data view. -/
def soDt (bv : Nat → BitVec 8) (sa : List Nat) : Mem := fillMem (soImg bv) (soDA sa)

variable {bv : Nat → BitVec 8} {sa : List Nat}

theorem imgM_soDt {a : Nat} (h : a ∈ soDA sa) : imgM (soDt bv sa) a = soImg bv a := by
  unfold imgM soDt; rw [fillMem_get _ h]; rfl

theorem soRo_mem {a : Nat} (h : a ∈ soRo) : a ∈ soDA sa :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ h))

theorem soDt_ro {a : Nat} (h : a ∈ soRo) : imgM (soDt bv sa) a = rodataByte a := by
  have h' := h
  simp only [List.mem_append, mem_accAddrs_iff] at h'
  rw [imgM_soDt (soRo_mem h)]
  unfold soImg
  rw [if_neg (by unfold impureW; omega), if_neg (by unfold textDom; omega), if_pos (by unfold rodataDom; omega)]

theorem ldv_soDt (bv : Nat → BitVec 8) (sa : List Nat) :
    ldv .ld (soDt bv sa) 0x8001b970 = 0x8001b538#64 := by
  have e : ∀ j, j < 8 → imgM (soDt bv sa) (0x8001b970 + j) = impureByte (0x8001b970 + j) := fun j hj => by
    rw [imgM_soDt (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_accAddrs hj))))]
    unfold soImg; rw [if_pos (by unfold impureW; omega)]
  have h : imgLE (imgM (soDt bv sa)) 0x8001b970 8 = 0x8001b538 := by
    rw [imgLE_congr (img' := impureByte) e]; decide
  exact ldvf_ld_imgLE h

theorem soDA_imp : Cover (· ∈ soDA sa) 0x8001b970 0x8001b978 := fun b h1 h2 =>
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (mem_accAddrs_iff.2 ⟨h1, by omega⟩)))

/-- The interpreter's code and tables read as themselves. -/
theorem soDt_interp : ∀ p ∈ interpText, p ∈ dataOf (soDt bv sa) (soDA sa) := by
  intro p hp
  have hA : p.1 ∈ soDA sa :=
    List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem (f := Prod.fst) hp))
  refine List.mem_map.2 ⟨p.1, hA, ?_⟩
  rw [imgM_soDt hA]
  obtain ⟨a, b⟩ := p
  rcases interpText_img_mem _ hp with ⟨hd, he⟩ | ⟨hd, he⟩
  · unfold textDom at hd
    unfold soImg
    rw [if_neg (by unfold impureW; omega), if_pos (by unfold textDom; omega)]
    exact congrArg _ he
  · unfold rodataDom at hd
    unfold soImg
    rw [if_neg (by unfold impureW; omega), if_neg (by unfold textDom; omega), if_pos (by unfold rodataDom; omega)]
    exact congrArg _ he

theorem lbu_soDt {a : Nat} (h : a ∈ soRo) :
    ldv .lbu (soDt bv sa) a = BitVec.zeroExtend 64 (rodataByte a) :=
  Newlib.lbu_of_img (soDt_ro h)

theorem lw_soDt {a v : Nat} (h : ∀ j, j < 4 → a + j ∈ soRo) (hv : imgLE rodataByte a 4 = v) :
    ldv .lw (soDt bv sa) a = LeanRV64DExecutable.Functions.sign_extend (m := 64) (BitVec.ofNat 32 v) := by
  refine ldv_lw_of_imgLE ?_
  rw [imgLE_congr (img' := rodataByte) fun j hj => soDt_ro (h j hj)]; exact hv

/-- A format string in `.rodata`, read through the view. -/
theorem fmtAt_so {P : Nat} {bs : List (BitVec 8)} (hP : ∀ i, i < bs.length → P + i ∈ soRo)
    (hlo : 0x80000000 ≤ P) (hhi : P + bs.length < 0x8001ad00)
    (hb : ∀ i (h : i < bs.length), rodataByte (P + i) = bs[i]) : FmtAt (soDt bv sa) (soDA sa) P bs where
  lo := hlo
  hi := hhi
  mem i hi := soRo_mem (hP i hi)
  byte i hi := by rw [lbu_soDt (hP i hi), hb i hi]

theorem soRo_fmt {a : Nat} (h1 : 0x800192c0 ≤ a) (h2 : a < 0x800192e8) : a ∈ soRo :=
  List.mem_append_left _ (List.mem_append_left _ (mem_accAddrs_iff.2 ⟨h1, h2⟩))

theorem soRo_tab {a : Nat} (h1 : 0x8001a288 ≤ a) (h2 : a < 0x8001a3f4) : a ∈ soRo :=
  List.mem_append_right _ (mem_accAddrs_iff.2 ⟨h1, h2⟩)

theorem soRo_dot {a : Nat} (h1 : 0x80019770 ≤ a) (h2 : a < 0x80019772) : a ∈ soRo :=
  List.mem_append_left _ (List.mem_append_right _ (mem_accAddrs_iff.2 ⟨h1, h2⟩))

theorem so_lld : LldFmt (soDt bv sa) (soDA sa) where
  fmtDA b h1 h2 := soRo_mem (soRo_fmt (by omega) (by omega))
  tabDA b h1 h2 := soRo_mem (soRo_tab h1 h2)
  l1 := by rw [lbu_soDt (soRo_fmt (by decide) (by decide))]; decide
  l2 := by rw [lbu_soDt (soRo_fmt (by decide) (by decide))]; decide
  d := by rw [lbu_soDt (soRo_fmt (by decide) (by decide))]; decide
  tabL := by rw [lw_soDt (v := 0xffff141c) (fun j hj => soRo_tab (by omega) (by omega)) (by decide)]; decide
  tabD := by rw [lw_soDt (v := 0xffff0cd8) (fun j hj => soRo_tab (by omega) (by omega)) (by decide)]; decide

theorem so_sfmt {X : Nat} (h1 : 0x800192c0 ≤ X) (h2 : X + 2 < 0x800192e8) (hs : rodataByte (X + 1) = 115#8) :
    SFmt (soDt bv sa) (soDA sa) X where
  fmtDA b h1 h2 := soRo_mem (soRo_fmt (by omega) (by omega))
  tabDA b h1 h2 := soRo_mem (soRo_tab h1 h2)
  s := by rw [lbu_soDt (soRo_fmt (by omega) (by omega)), hs]; decide
  tabS := by rw [lw_soDt (v := 0xffff10a4) (fun j hj => soRo_tab (by omega) (by omega)) (by decide)]; decide

theorem so_dot : 0x80019770 ∈ soDA sa ∧ 0x80019771 ∈ soDA sa :=
  ⟨soRo_mem (soRo_dot (by decide) (by decide)), soRo_mem (soRo_dot (by decide) (by decide))⟩

theorem so_dotv : imgM (soDt bv sa) 0x80019770 = 0x2e#8 ∧ imgM (soDt bv sa) 0x80019771 = 0#8 :=
  ⟨by rw [soDt_ro (soRo_dot (by decide) (by decide))]; decide,
   by rw [soDt_ro (soRo_dot (by decide) (by decide))]; decide⟩

/-! ## The formats -/

/-- A string format of `value_print`: its address and the literal before `%s`. -/
structure SFmtCase (fmt : BitVec 64) (lit : String) : Prop where
  cases : (fmt = 0x800192c8#64 ∧ lit = "<fn ") ∨ (fmt = 0x800192d8#64 ∧ lit = "<native fn ")

/-- The facts `fprintf_s` reads about a string format. -/
structure SFmtFacts (Dt : Mem) (DA : List Nat) (fmt : BitVec 64) (lit : List (BitVec 8)) : Prop where
  ne : lit ≠ []
  bytes : ∀ b ∈ lit, b ≠ 0#8 ∧ b ≠ 37#8
  len : lit.length ≤ 16
  pct : FmtAt Dt DA fmt.toNat (lit ++ [37#8])
  s : SFmt Dt DA (fmt.toNat + lit.length)
  gt : FmtAt Dt DA (fmt.toNat + lit.length + 2) ([0x3e#8] ++ [0#8])

theorem sFmtFacts_of {fmt : BitVec 64} {lit : String} (h : SFmtCase fmt lit) :
    SFmtFacts (soDt bv sa) (soDA sa) fmt (strBytes lit) := by
  rcases h.cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e : (strBytes "<fn ").length = 4 := by decide
    have t : (0x800192c8#64).toNat = 0x800192c8 := rfl
    exact ⟨by decide, by decide, by decide,
      fmtAt_so (fun i hi => soRo_fmt (by rw [t]; omega) (by simp only [List.length_append, e, List.length_singleton] at hi; rw [t]; omega))
        (by decide) (by decide) (by decide),
      so_sfmt (by decide) (by decide) (by decide),
      fmtAt_so (fun i hi => soRo_fmt (by rw [t]; omega) (by simp only [List.length_append, List.length_singleton, e] at hi ⊢; rw [t]; omega))
        (by decide) (by decide) (by decide)⟩
  · have e : (strBytes "<native fn ").length = 11 := by decide
    have t : (0x800192d8#64).toNat = 0x800192d8 := rfl
    exact ⟨by decide, by decide, by decide,
      fmtAt_so (fun i hi => soRo_fmt (by rw [t]; omega) (by simp only [List.length_append, e, List.length_singleton] at hi; rw [t]; omega))
        (by decide) (by decide) (by decide),
      so_sfmt (by decide) (by decide) (by decide),
      fmtAt_so (fun i hi => soRo_fmt (by rw [t]; omega) (by simp only [List.length_append, List.length_singleton, e] at hi ⊢; rw [t]; omega))
        (by decide) (by decide) (by decide)⟩

/-- The `%s` case of the data witness: the name at `arg`, read-only, and its
bytes as the view shows them. -/
structure StrCase (fmt arg : BitVec 64) (frag : String) (bv : Nat → BitVec 8) (name lit : String) : Prop where
  fmt : SFmtCase fmt lit
  frag : frag = lit ++ name ++ ">"
  cstr : CStrImg bv arg.toNat name
  win : StrWin arg.toNat name.toList.length
  agree : ∀ a, InExt (arg.toNat, name.toList.length + 1) a → soImg bv a = bv a

/-- The data witness of `fprintf_out`: `"%lld"` with no string, or a name. -/
inductive SoPf (fmt arg : BitVec 64) (frag : String) :
    (Nat → BitVec 8) → List Nat → String → String → Prop
  | lld {bv name lit} : fmt = 0x800192c0#64 → frag = intToString arg.toInt → SoPf fmt arg frag bv [] name lit
  | str {bv name lit} : StrCase fmt arg frag bv name lit →
      SoPf fmt arg frag bv (accAddrs arg.toNat (name.toList.length + 1)) name lit

/-! ## Ownership -/

section Own

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- `_impure_ptr`, the binary and `bv` on `S`, as one read-only image. -/
theorem roImg_so (S : Nat → Prop) (bv : Nat → BitVec 8) :
    iprop(impureRO ∗ binImg ∗ roImg S bv) ⊢@{IProp GF}
      roImg (fun a => impureW a ∨ textDom a ∨ rodataDom a ∨ S a) (soImg bv) := by
  unfold impureRO binImg roImg
  iintro ⟨#Hi, ⟨#Ht, #Hr⟩, #Hs⟩
  imodintro
  iintro %k %hk
  unfold soImg
  by_cases h1 : impureW k
  · rw [if_pos h1]; iapply Hi $$ %k %h1
  rw [if_neg h1]
  by_cases h2 : textDom k
  · rw [if_pos h2]; iapply Ht $$ %k %h2
  rw [if_neg h2]
  by_cases h3 : rodataDom k
  · rw [if_pos h3]; iapply Hr $$ %k %h3
  rw [if_neg h3]
  iapply Hs $$ %k %(((hk.resolve_left h1).resolve_left h2).resolve_left h3)

theorem roImg_none (f : Nat → BitVec 8) : ⊢@{IProp GF} roImg (fun _ => False) f := by
  unfold roImg
  imodintro
  iintro %k %hk
  exact hk.elim

/-- **The run's read-only cells**: `gp`, the stdio code, and the view. -/
theorem soView (S : Nat → Prop) (bv : Nat → BitVec 8) (sa : List Nat) (hS : ∀ a ∈ sa, S a) :
    iprop(gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO ∗ roImg S bv) ⊢@{IProp GF}
      roOwn roR (stdioText ++ dataOf (soDt bv sa) (soDA sa)) := by
  unfold roOwn
  iintro ⟨#Hgp, #Hb, #Hi, #Hs⟩
  isplitl []
  · simp only [roR, sepL_cons, sepL_nil]
    rw [show Newlib.gpV = MallocFast.gpV from rfl]
    iframe Hgp
  iapply (sepL_append _ _ _).2
  isplitl []
  · iapply binImg_sepL stdioText (fun p hp => .inl (stdioText_img_mem p hp)) $$ Hb
  ihave #H := roImg_so S bv $$ [Hi Hb Hs]
  · iframe Hi Hb Hs
  unfold dataOf
  rw [sepL_map]
  ihave #H := roImg_restrict (T := fun a => a ∈ soDA sa) (g := imgM (soDt bv sa))
    (fun a ha => by
      rcases List.mem_append.mp ha with ha | ha
      · rcases List.mem_append.mp ha with ha | ha
        · rcases List.mem_append.mp ha with ha | ha
          · left; have := of_mem_accAddrs ha; unfold impureW; omega
          · simp only [List.mem_append, mem_accAddrs_iff] at ha
            right; right; left; unfold rodataDom; omega
        · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
          rcases interpText_img_mem p hp with ⟨hd, -⟩ | ⟨hd, -⟩
          · exact .inr (.inl hd)
          · exact .inr (.inr (.inl hd))
      · exact .inr (.inr (.inr (hS a ha))))
    (fun k hk => (imgM_soDt hk).symm) $$ H
  iapply roImg_list _ (imgM (soDt bv sa)) _ (fun a ha => ha) $$ H

/-- A name's bytes agree with the view's image on its window. -/
theorem so_agree (p n : Nat) (img : Nat → BitVec 8) :
    iprop(impureRO ∗ binImg ∗ roImg (InExt (p, n)) img) ⊢@{IProp GF}
      ⌜∀ a, InExt (p, n) a → soImg img a = img a⌝ := by
  iintro ⟨#Hi, #Hb, #Hs⟩
  ihave #Ho := roImg_so (InExt (p, n)) img $$ [Hi Hb Hs]
  · iframe Hi Hb Hs
  ihave #Ho := roImg_restrict (T := InExt (p, n)) (g := soImg img) (fun _ h => .inr (.inr (.inr h)))
    (fun _ _ => rfl) $$ Ho
  ihave %h := roImg_agree (f := soImg img) (g := img) $$ [Ho Hs]
  · iframe Ho Hs
  ipureintro; exact h

end Own

/-- The interpreter's stack lies above the first megabyte of RAM. -/
theorem stackMb_of_stackGeom {s : BitVec 64} {n need : Nat} (h : StackGeom s n) (hle : need ≤ n) :
    0x80100000 ≤ s.toNat - need := by
  have h1 := h.le; have h2 := h.lo
  unfold Vsa.Sim.LayoutInstance.stackSL at h2
  simp only at h2
  omega

section Spec

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF]

/-- A name, read-only, as the `%s` data witness. -/
theorem soData_str {fmt : BitVec 64} {frag : String} (arg : BitVec 64) (name lit : String)
    (hf : SFmtCase fmt lit) (hfr : frag = lit ++ name ++ ">") :
    iprop(strAt arg.toNat name ∗ gp ↦ᵣ□ Newlib.gpV ∗ binImg ∗ impureRO) ⊢@{IProp GF}
      ∃ x : (Nat → BitVec 8) × List Nat × String × String,
        roOwn roR (stdioText ++ dataOf (soDt x.1 x.2.1) (soDA x.2.1)) ∗
        ⌜SoPf fmt arg frag x.1 x.2.1 x.2.2.1 x.2.2.2⌝ := by
  unfold strAt
  iintro ⟨⟨%img, %⟨hc, hw⟩, #Hs⟩, #Hgp, #Himg, #Hi⟩
  ihave %hag := so_agree arg.toNat (name.toList.length + 1) img $$ [Hi Himg Hs]
  · iframe Hi Himg Hs
  iexists (img, accAddrs arg.toNat (name.toList.length + 1), name, lit)
  isplitl
  · iapply soView (InExt (arg.toNat, name.toList.length + 1)) img _ (fun a ha => by
      have := of_mem_accAddrs ha; unfold InExt; dsimp only; omega) $$ [Hgp Himg Hi Hs]
    iframe Hgp Himg Hi Hs
  · ipureintro; exact .str ⟨hf, hfr, hc, hw, hag⟩

/-- **`fprintf(stdout, fmt, arg)`, proved** (`OutHoles.fprintf`), with the
interpreter's code live (the digit loop's arithmetic helpers) and the stack
above the first megabyte of RAM (`__sbprintf`'s stack `FILE` and the callee
frames below it). -/
theorem fprintf_out (live : Nat → Prop) (Wp : MachWP (GF := GF) (vsaModel live))
    (fmt arg s : BitVec 64) (cs : Nat → BitVec 64) (frag o : String) (hcl : CodeLive live)
    (hlive' : ∀ p ∈ interpText, live p.1) (hsp : SpIn s fprintfNeed)
    (hs4 : 0x80100000 ≤ s.toNat - fprintfNeed) :
    ⊢ outSpec live Wp fprintfEntry [stdoutFile, fmt, arg] (fprintfOut fmt arg frag) s fprintfNeed cs o frag := by
  have hlo := hsp.lo
  have hhi := hsp.hi
  unfold tohostAddr fprintfNeed at hlo
  unfold fprintfNeed at hs4 ⊢
  refine outSpec_of_run (X := (Nat → BitVec 8) × List Nat × String × String)
    (Pf := fun x => SoPf fmt arg frag x.1 x.2.1 x.2.2.1 x.2.2.2)
    (Dt := fun x => soDt x.1 x.2.1) (DA := fun x => soDA x.2.1)
    Wp (by simp) (by omega) (by omega) ?_
    (fun x R Mt r img hal h1 h2 hargs hcs hok himp hMt hPf hoff => ?_)
  · unfold fprintfOut
    iintro ⟨HR, #Hgp, #Himg, #Hi⟩
    icases HR with (%h | ⟨%name, %h, #Hs⟩ | ⟨%name, %h, #Hs⟩)
    · iexists ((fun _ => 0#8), [], "", "")
      ihave #Hn := roImg_none (GF := GF) (fun _ => 0#8)
      isplitl
      · iapply soView (fun _ => False) (fun _ => 0#8) [] (fun a ha => by cases ha) $$ [Hgp Himg Hi Hn]
        iframe Hgp Himg Hi Hn
      · ipureintro; exact .lld h.1 h.2
    · iapply soData_str arg name "<fn " ⟨.inl ⟨h.1, rfl⟩⟩ h.2 $$ [Hs Hgp Himg Hi]
      iframe Hs Hgp Himg Hi
    · iapply soData_str arg name "<native fn " ⟨.inr ⟨h.1, rfl⟩⟩ h.2 $$ [Hs Hgp Himg Hi]
      iframe Hs Hgp Himg Hi
  obtain ⟨bv, sa, name, lit⟩ := x
  dsimp only at hPf hoff ⊢
  obtain ⟨ob, hokA⟩ := id hok
  have hcm := consoleMt_of hokA fun a ha hi => hMt a ⟨ha, hi⟩
  have hlm := localeMt_of hok fun a ha hi => hMt a ⟨ha, hi⟩
  have hSo : StdoutSbAt (consoleFlagsV ob) Mt := ⟨hcm.flagsU, hcm.flagsS, ldv_lhu_of_lh (by decide) hcm.fd, hcm.fd, hcm.lockMode,
    hcm.cookie, hcm.writer, hcm.sinit⟩
  have hbase : ldv .ld Mt 0x8001bb38 ≠ 0#64 := by rw [hcm.base]; decide
  have hloc : LocMb Mt := ⟨hlm.mbtowc, hlm.mbMax⟩
  have h10 : R 10 = 0x8001bb20#64 := hargs 0 (by simp)
  have h11 : R 11 = fmt := hargs 1 (by simp)
  have h12 : R 12 = arg := hargs 2 (by simp)
  have hs5 : 0x8001c168 ≤ s.toNat - 2960 := by omega
  have hlive := Newlib.stdioText_live hcl
  have fin : ∀ (bytes : List (BitVec 8)) (a0 : BitVec 64), putcs bytes = frag → ∀ R' M', RetOK R R' a0 →
      Frame M' Mt (FpReg (s.toNat - 80)) → ldv .lh M' 0x8001bb30 = 0x200a#64 →
      SWPO live (stdioText ++ dataOf (soDt bv sa) (soDA sa)) iRegs (outS s 4096) (OutEnd o frag r s cs)
        (o ++ putcs bytes) (R 1) R' M' := by
    intro bytes a0 hb R' M' hr hF hfl
    refine swpo_done fun rv mv hm => ?_
    have hK : MemKeep Mt M' (outKeep s 2960) := ⟨fun a ha => hF a fun h => by
      obtain ⟨o1, o2, o3, o4, o5⟩ := ha
      unfold FpReg at h
      rcases h with ⟨q1, q2⟩ | q | q
      · rw [Nat.sub_sub] at q1; exact o1 ⟨q1, by omega⟩
      · exact o4 ⟨by omega, by omega⟩
      · exact o2 q⟩
    have hnF : ∀ a w, 0x8001bb20 ≤ a → a + w ≤ 0x8001bb30 → ∀ j, j < w → ¬ FpReg (s.toNat - 80) (a + j) :=
      fun a w ha hw j hj h => by
        unfold FpReg at h
        rcases h with ⟨q1, q2⟩ | q | q
        · rw [Nat.sub_sub] at q1; omega
        · omega
        · omega
    refine outEnd_of (k := 2960) hok himp hMt hr h1 h2 hcs hs5 hK ?_ ?_ (ldv_lhu_of_lh (by decide) hfl) (by rw [h1] at hm; exact hm)
      (by rw [hb])
    · rw [hF.ldv .ld fun j hj => hnF 0x8001bb20 8 (by decide) (by decide) j (by simpa [widthOfM] using hj)]
      exact hcm.p
    · rw [hF.ldv .lw fun j hj => hnF 0x8001bb2c 4 (by decide) (by decide) j (by simpa [widthOfM] using hj)]
      exact hcm.w
  cases hPf with
  | lld hf hfr =>
    subst hf
    refine fprintf_lld hlive hlive' soDt_interp (by omega) (by omega) hhi hs4 hsp.align (by rw [h1]; exact hal) h2 h10 h11
      (ldv_soDt _ _) soDA_imp hlm.decPoint so_dot so_dotv hSo hbase hloc so_lld
      (fmtAt_so (fun i hi => soRo_fmt (by omega) (by simp at hi; omega)) (by decide) (by decide) (by decide))
      (fmtAt_so (fun i hi => soRo_fmt (by omega) (by simp at hi; omega)) (by decide) (by decide) (by decide))
      fun R' M' hr hF hfl => fin _ _ (by rw [h12, putcs_lldBytes, hfr]) R' M' hr hF hfl
  | str hS =>
    have F := sFmtFacts_of (bv := bv) (sa := accAddrs arg.toNat (name.toList.length + 1)) hS.fmt
    have hc := hS.cstr
    have hw := hS.win
    have hn := strBytes_length name
    have hA : ∀ i, i ≤ name.toList.length → arg.toNat + i ∈ soDA (accAddrs arg.toNat (name.toList.length + 1)) ∧
        imgM (soDt bv (accAddrs arg.toNat (name.toList.length + 1))) (arg.toNat + i) = bv (arg.toNat + i) :=
      fun i hi => by
        have hm : arg.toNat + i ∈ soDA (accAddrs arg.toNat (name.toList.length + 1)) :=
          List.mem_append_right _ (mem_accAddrs (by omega))
        refine ⟨hm, ?_⟩
        rw [imgM_soDt hm, hS.agree _ (by unfold InExt; dsimp only; omega)]
    have hch : ∀ c ∈ name.toList, c.toNat < 256 := fun c hc' => by
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc'
      have := (hc.1 i hi).2.2; omega
    refine fprintf_s (lit := strBytes lit) (bs := strBytes name) hlive hlive' soDt_interp (by omega) (by omega)
      hhi hs4 hsp.align (by rw [h1]; exact hal) h2 h10 h11 (ldv_soDt _ _) soDA_imp hlm.decPoint so_dot so_dotv hSo hbase hloc
      F.ne F.bytes F.len F.pct F.s F.gt (by rw [h12, hn]; exact hw) (fun i hi => ?_) (fun b hb => ?_) ?_
      (fun i hi => ?_) fun R' M' hr hF hfl => fin _ _ ?_ R' M' hr hF hfl
    · rw [hn] at hi
      rw [h12, (hA i (by omega)).2, (hc.1 i hi).1]
      exact ⟨(hA i (by omega)).1, by simp [strBytes]⟩
    · obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hb
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hc'
      have := (hc.1 i hi).2
      intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at h'
      omega
    · rw [h12, hn]
      exact ⟨(hA _ (Nat.le_refl _)).1, by rw [(hA _ (Nat.le_refl _)).2]; exact hc.2⟩
    · rw [hn] at hi
      rw [h12]
      exact hoff (_, _) (List.mem_map.2 ⟨_, (hA i (by omega)).1, rfl⟩)
    · rw [putcs_append, putcs_append, putcs_strBytes name hch, hS.frag]
      rw [putcs_strBytes lit (by rcases hS.fmt.cases with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide)]
      rfl

end Spec

end VsaIris.Sym.Fp
