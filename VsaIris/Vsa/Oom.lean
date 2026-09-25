import VsaIris.Vsa.SegRO
import VsaIris.Interp.Abort

/-!
# The out-of-memory block: `fwrite` then `exit(1)` (H5)

Every inlined `xmalloc` NULL arm of the interpreter is the same nine
instructions (`env_new`, `env_define`, `stringify`; `eval_expr`'s `fn` arm
interleaves two spills):

```
h+0:  ld a5,1120(gp)       _impure_ptr
h+4:  li a2,14
h+8:  li a1,1
h+12: ld a3,24(a5)         _impure_data._stderr
h+16: auipc a0; addi a0    "out of memory\n" (0x80019040)
h+24: jal fwrite           IrisHoles.newlib.fwrite
h+28: li a0,1
h+32: jal exit
```

One descriptor `OomSite` (the site's code, reflected segments and `jal`
sites) with its decided facts `OomSite.OK` gives `wp_oomBlock`: from the
block's head, with the site's whole stack region, the run reaches `exit`'s
entry with `a0 = 1` and hands the abort continuation `abortRes s n` (its
`oomCore` disjunct). Instances are generated (`scripts/gen_h5_sites.py`,
kind `oom`).
-/

namespace VsaIris.Newlib.Oom

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Sim VsaIris.Inst VsaIris.Interp VsaIris.Stdio VsaIris.Newlib.Exit VsaIris.Newlib.MainErr

/-- `"out of memory\n"` (`.rodata`). -/
def oomMsg : BitVec 64 := 0x80019040#64

theorem oomMsg_text : ∀ i, i < 14 → rodataDom (oomMsg.toNat + i) := by decide

/-- An out-of-memory block, as read off the disassembly: `stage`
instructions before `jal fwrite` (6, or 8 where `eval_expr` interleaves two
spills), the callee-saved registers they spill (`spills`: register and `sp`
offset), all inside `[sp, sp + frameTop)`. -/
structure OomSite where
  head : Nat
  code : List (BitVec 8)
  stage : Nat
  spills : List (Nat × Nat)
  frameTop : Nat
  seg : List BBlock
  li : List BBlock
  fw : JalSite
  ex : JalSite

abbrev oomLw (a5v a2v a1v a3v a0v : BitVec 64) : GRegs :=
  [(15, a5v), (12, a2v), (11, a1v), (13, a3v), (10, a0v)]
abbrev oomLr : GRegs := [(3, gpV)]
abbrev oomLds (simg : Nat → BitVec 8) : List (List (BitVec 8)) :=
  [imgWord simg consoleImpurePtrAddr, imgWord simg stderrPtrAddr]

/-- The staging's written pins: the argument registers, `sp`, the spilled
callee-saved registers. -/
abbrev oomLx (S : OomSite) (a5v a2v a1v a3v a0v s' : BitVec 64) (cs : Nat → BitVec 64) : GRegs :=
  oomLw a5v a2v a1v a3v a0v ++ (2, s') :: S.spills.map fun p => (p.1, cs p.1)

/-- The staging's pin keys. -/
def oomKeys (S : OomSite) : List Nat := [15, 12, 11, 13, 10, 2] ++ S.spills.map Prod.fst ++ [3]

theorem keysG_map (cs : Nat → BitVec 64) :
    ∀ l : List (Nat × Nat), keysG (l.map fun p => (p.1, cs p.1)) = l.map Prod.fst
  | [] => rfl
  | _ :: l => by simp only [List.map_cons, keysG, keysG_map cs l]

theorem keysG_append : ∀ l₁ l₂ : GRegs, keysG (l₁ ++ l₂) = keysG l₁ ++ keysG l₂
  | [], _ => rfl
  | (_, _) :: l, l₂ => by simp only [List.cons_append, keysG, keysG_append l l₂]

theorem keysG_oomLx (S : OomSite) (a5v a2v a1v a3v a0v s' : BitVec 64) (cs : Nat → BitVec 64) :
    keysG (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) = oomKeys S := by
  simp [oomLx, oomKeys, keysG_append, keysG_map, keysG, oomLw, oomLr]

/-- The staging's stack pointer: RAM above the HTIF words, 16-aligned, the
spill window in RAM. -/
structure OomSp (S : OomSite) (s' : BitVec 64) : Prop where
  lo : Vsa.Sim.tohostAddr + 16 ≤ s'.toNat
  hi : s'.toNat + S.frameTop ≤ 0x100000000
  align : s'.toNat % 16 = 0

/-- A spill address `sp + off` inside the staging's window. -/
theorem oomSp_off {S : OomSite} {s' : BitVec 64} (hs : OomSp S s') (off : Nat) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64).toNat = off) (hoff : off + 8 ≤ S.frameTop) :
    ∀ x : BitVec 64, x = s' + sign_extend (m := 64) imm → x.toNat = s'.toNat + off := by
  intro x hx
  have h2 := hs.hi
  rw [hx, addr_off _ _ off himm (by omega)]

/-- The decided facts about an out-of-memory block. -/
structure OomSite.OK (S : OomSite) : Prop where
  text : TextAt S.head S.code
  stage_pos : 1 ≤ S.stage
  len : evalBlocksFuel S.seg = (S.stage - 1) + 1
  wf : ChainOK (BitVec.ofNat 64 S.head) (oomKeys S) S.seg
  keys : KeysOK (oomKeys S)
  wr : ∀ k ∈ wrChain S.seg, k ∈ [15, 12, 11, 13, 10]
  spillsSaved : calleeSaved.filter (fun r => decide (r ∈ S.spills.map Prod.fst)) =
    S.spills.map Prod.fst
  logIn : ∀ (a5v a2v a1v a3v a0v s' : BitVec 64) (cs : Nat → BitVec 64) (simg : Nat → BitVec 8),
    OomSp S s' → ∀ e ∈ (segOut S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg)).log,
      s'.toNat ≤ e.1 ∧ e.1 + e.2.1 ≤ s'.toNat + S.frameTop
  facts : ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (a5v a2v a1v a3v a0v s' : BitVec 64)
    (cs : Nat → BitVec 64) (simg : Nat → BitVec 8),
    (∀ p ∈ codeFoot S.head S.code, m[p.1]? = some p.2.2) → StdioOK simg → OomSp S s' →
    (∀ k, (consoleImpurePtrAddr ≤ k ∧ k < consoleImpurePtrAddr + 8) ∨
      (stderrPtrAddr ≤ k ∧ k < stderrPtrAddr + 8) → (m[k]?).getD 0 = simg k) →
    ChainFacts m m (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) S.seg
  pc : ∀ (a5v a2v a1v a3v a0v s' : BitVec 64) (cs : Nat → BitVec 64) (simg : Nat → BitVec 8),
    evalBlocksPC (BitVec.ofNat 64 S.head)
      (SegEvalState.init (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg)) S.seg =
      BitVec.ofNat 64 (S.head + 4 * S.stage)
  fin : ∀ (a5v a2v a1v a3v a0v s' : BitVec 64) (cs : Nat → BitVec 64) (simg : Nat → BitVec 8),
    StdioOK simg →
    finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) 15 =
        BitVec.ofNat 64 consoleReent ∧
      finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) 12 = 14#64 ∧
      finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) 11 = 1#64 ∧
      finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) 13 = stderrFile ∧
      finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) 10 = oomMsg ∧
      finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) 2 = s'
  finKeep : ∀ (a5v a2v a1v a3v a0v s' : BitVec 64) (cs : Nat → BitVec 64) (simg : Nat → BitVec 8),
    ∀ p ∈ S.spills, finReg S.seg (oomLx S a5v a2v a1v a3v a0v s' cs ++ oomLr) (oomLds simg) p.1 =
      cs p.1
  liLen : evalBlocksFuel S.li = 0 + 1
  liWf : ChainOK (BitVec.ofNat 64 (S.head + 4 * S.stage + 4)) [10] S.li
  liWr : ∀ k ∈ wrChain S.li, k ∈ [10]
  liLog : ∀ a0v : BitVec 64, (segOut S.li [(10, a0v)] []).log = []
  liFacts : ∀ (m : Std.ExtHashMap Nat (BitVec 8)) (a0v : BitVec 64),
    (∀ p ∈ codeFoot S.head S.code, m[p.1]? = some p.2.2) → ChainFacts m m [(10, a0v)] [] S.li
  liPc : ∀ a0v : BitVec 64, evalBlocksPC (BitVec.ofNat 64 (S.head + 4 * S.stage + 4))
    (SegEvalState.init [(10, a0v)] []) S.li = BitVec.ofNat 64 (S.head + 4 * S.stage + 8)
  liFin : ∀ a0v : BitVec 64, finReg S.li [(10, a0v)] [] 10 = 1#64
  fwCert : S.fw.Cert
  fwPc : S.fw.pc = S.head + 4 * S.stage
  fwTgt : S.fw.tgt = fwriteEntry
  fwText : TextAt S.fw.pc S.fw.code
  exCert : S.ex.Cert
  exPc : S.ex.pc = S.head + 4 * S.stage + 8
  exTgt : S.ex.tgt = exitEntry
  exText : TextAt S.ex.pc S.ex.code

/-- The block's stack pointer `s'` inside the site's region `[s - n, s)`,
with room for `fwrite` below it and the staging's spills above it. -/
structure OomBlockSp (S : OomSite) (s : BitVec 64) (n : Nat) (s' : BitVec 64) : Prop where
  need : n ≤ s.toNat
  lo : Vsa.Sim.tohostAddr + 16 ≤ s.toNat - n
  fits : s.toNat - n + fwriteNeed ≤ s'.toNat
  frame : s'.toNat + S.frameTop ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  align : s'.toNat % 16 = 0

/-- A log inside `[lo, hi)` misses every address outside it. -/
theorem outL_of_in {lo hi a : Nat} (ha : a < lo ∨ hi ≤ a) :
    ∀ log : List WEntry, (∀ e ∈ log, lo ≤ e.1 ∧ e.1 + e.2.1 ≤ hi) → OutL log a
  | [], _ => trivial
  | e :: log, h => by
    have he := h e List.mem_cons_self
    exact ⟨by omega, outL_of_in ha log (fun f hf => h f (.tail _ hf))⟩

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

omit I in
theorem sepL_spills (l : List (Nat × Nat)) (cs : Nat → BitVec 64) :
    sepL (GF := GF) (l.map Prod.fst) (fun q => q ↦ᵣ cs q) ⊣⊢
      sepL (l.map fun p => (p.1, cs p.1)) (fun p => p.1 ↦ᵣ p.2) := by
  rw [VsaIris.sepL_map, VsaIris.sepL_map]
  exact .rfl

omit I in
theorem sepL_spills_keep (l : List (Nat × Nat)) (f cs : Nat → BitVec 64)
    (h : ∀ p ∈ l, f p.1 = cs p.1) :
    sepL (GF := GF) (l.map fun p => (p.1, cs p.1)) (fun p => p.1 ↦ᵣ f p.1) ⊢
      sepL (l.map fun p => (p.1, cs p.1)) (fun p => p.1 ↦ᵣ p.2) := by
  rw [VsaIris.sepL_map, VsaIris.sepL_map,
    sepL_congr (l := l) (Φ := fun p => p.1 ↦ᵣ f p.1) (Ψ := fun p => p.1 ↦ᵣ cs p.1)
      (fun p hp => by rw [h p hp])]

omit I in
theorem ownSet_none (Φ : Nat → IProp GF) : ⊢ ownSet (fun _ => False) Φ := by
  unfold ownSet
  iexists []
  isplitr
  · ipureintro; exact ⟨List.nodup_nil, fun a => by simp⟩
  · simp only [sepL_nil]; iempintro

/-- **The out-of-memory block**, for either WP: from the block's head, owning
every register, the site's region `[s - n, s)` with `sp = s'` inside it, and
newlib's data, the run reaches `exit(1)`'s entry and the abort continuation
takes over with `abortRes s n`. -/
theorem wp_oomBlock (H : NewlibHoles) (live : Nat → Prop) (hlive : CodeLive live)
    (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (N : Vsa.RuntimeRepr.NativeAddrs) (L : DlLayout) (Room : RoomPred) (inp : Nat)
    (S : OomSite) (hS : S.OK) (s s' r : BitVec 64) (n : Nat) (hsp : OomBlockSp S s n s')
    (cs : Nat → BitVec 64) (o : String) :
    PC ↦ᵣ BitVec.ofNat 64 S.head ∗ ra ↦ᵣ r ∗ sp ↦ᵣ s' ∗ clobbered argRegs ∗ clobbered tmpRegs ∗
      sepL calleeSaved (fun q => q ↦ᵣ cs q) ∗ gp ↦ᵣ□ gpV ∗ binImg ∗ stackScratch s n ∗
      stdioOwn ∗ errnoOwn ∗ consoleOwn o ∗ (abortRes N L Room inp s n -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  have hHA := H.at
  have h1 := hsp.need; have h2 := hsp.lo; have h3 := hsp.fits; have h4 := hsp.frame
  have h5 := hsp.hi; have h6 := hsp.align
  unfold fwriteNeed tohostAddr at *
  have hsp' : OomSp S s' := ⟨by unfold tohostAddr; omega, by omega, h6⟩
  have hcodeL := hS.text.live hlive
  unfold VsaIris.sp VsaIris.ra VsaIris.gp
  iintro ⟨Hpc, Hra, Hsp, Hargs, Htmp, Hsaved, #Hgp, #Himg, Hscr, Hstd, Hno, Hcon, Hk⟩
  ihave #Hcode := instrAt_of_binImg hS.text $$ Himg
  -- the stack: `[s-n, s'-768)`, `fwrite`'s scratch, the spill window, the rest
  unfold stackScratch
  ihave ⟨Hlo, Hscr⟩ := blockOwn_split (s.toNat - n) n (s'.toNat - 768 - (s.toNat - n))
    (s'.toNat - 768) (n - (s'.toNat - 768 - (s.toNat - n))) (by omega) (by omega) rfl $$ Hscr
  ihave ⟨Hscr, Hhi⟩ := blockOwn_split (s'.toNat - 768) (n - (s'.toNat - 768 - (s.toNat - n))) 768
    s'.toNat (n - (s'.toNat - 768 - (s.toNat - n)) - 768) (by omega) (by omega) rfl $$ Hscr
  ihave ⟨Hwin, Hhi⟩ := blockOwn_split s'.toNat (n - (s'.toNat - 768 - (s.toNat - n)) - 768)
    S.frameTop (s'.toNat + S.frameTop) (n - (s'.toNat - 768 - (s.toNat - n)) - 768 - S.frameTop)
    (by omega) rfl rfl $$ Hhi
  ihave Hwin := blockOwn_range _ _ $$ Hwin
  ihave ⟨%Wf, %hWf, Hwin⟩ := sepL_byteAny_exists _ $$ Hwin
  -- the spilled registers out of the callee-saved ones
  ihave ⟨Hsp1, Hsaved⟩ := (sepL_filter calleeSaved
    (fun q => decide (q ∈ S.spills.map Prod.fst)) (fun q => q ↦ᵣ cs q)).1 $$ Hsaved
  rw [hS.spillsSaved]
  ihave Hsp1 := (sepL_spills S.spills cs).1 $$ Hsp1
  -- `_impure_ptr` and `_impure_data._stderr`
  ihave ⟨%simg, %⟨hok, himp⟩, Hw, Hrest, #Himp⟩ := stdioAt_open StdioOK StdWin $$ Hstd
  ihave Hw := stdWin_foot simg himp $$ [Hw]
  · iframe Hw Himp
  ihave ⟨⟨%a5v, Ha5⟩, Hargs⟩ := clobbered_take (r := 15) (by decide) $$ Hargs
  ihave ⟨⟨%a2v, Ha2⟩, Hargs⟩ := clobbered_take (r := 12) (by decide) $$ Hargs
  ihave ⟨⟨%a1v, Ha1⟩, Hargs⟩ := clobbered_take (r := 11) (by decide) $$ Hargs
  ihave ⟨⟨%a3v, Ha3⟩, Hargs⟩ := clobbered_take (r := 13) (by decide) $$ Hargs
  ihave ⟨⟨%a0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  have hWm : ∀ a, (∃ q ∈ Wf, q.1 = a) ↔ a ∈ List.range' s'.toNat S.frameTop := by
    intro a; rw [← hWf]; simp
  iapply wp_segRW live Wp S.seg (oomLx S a5v a2v a1v a3v a0v s' cs) oomLr (oomLds simg)
    (BitVec.ofNat 64 S.head) DFrac.discard (codeFoot S.head S.code ++ stdFoot simg) Wf
    (S.stage - 1) hS.len (by rw [keysG_oomLx]; exact hS.wf) (by rw [keysG_oomLx]; exact hS.keys)
    (fun k hk => by
      have hk' := hS.wr k hk
      rw [show keysG (oomLx S a5v a2v a1v a3v a0v s' cs) = [15, 12, 11, 13, 10, 2] ++
        S.spills.map Prod.fst by simp [oomLx, keysG_map, keysG]]
      exact List.mem_append_left _ (by simp at hk' ⊢; omega))
    (fun a ha => by
      have : ¬ a ∈ List.range' s'.toNat S.frameTop := fun h => by
        obtain ⟨q, hq, e⟩ := (hWm a).2 h
        exact ha q hq e
      rw [List.mem_range'] at this
      exact outL_of_in (lo := s'.toNat) (hi := s'.toNat + S.frameTop)
        (by apply Classical.byContradiction; intro hc; exact this ⟨a - s'.toNat, by omega, by omega⟩)
        _ (hS.logIn a5v a2v a1v a3v a0v s' cs simg hsp'))
    (fun c hok' ⟨_, hMR, _, _⟩ => hS.facts _ _ _ _ _ _ s' cs simg
      (code_present hok' _ (fun q hq => hMR q (List.mem_append_left _ hq)) hcodeL) hok hsp'
      (fun k hk => by
        rcases hk with hk | hk
        · exact imgFootD_pin (a := consoleImpurePtrAddr) (n := 8) hMR
            (fun q hq => List.mem_append_right _ (List.mem_append_left _ hq)) k hk.1 hk.2
        · exact imgFoot_pin (a := stderrPtrAddr) (n := 8) hMR
            (fun q hq => List.mem_append_right _ (List.mem_append_right _ hq)) k hk.1 hk.2))
  obtain ⟨f15, f12, f11, f13, f10, f2⟩ := hS.fin a5v a2v a1v a3v a0v s' cs simg hok
  have hpc := hS.pc a5v a2v a1v a3v a0v s' cs simg
  have hkeep := hS.finKeep a5v a2v a1v a3v a0v s' cs simg
  simp only [oomLx, oomLw, oomLr, List.cons_append, List.nil_append] at f15 f12 f11 f13 f10 f2
  simp only [oomLx, oomLw, oomLr, List.cons_append, List.nil_append] at hpc hkeep
  simp only [oomLx, oomLw, oomLr, List.cons_append, List.nil_append, sepL_cons, sepL_nil, hpc,
    f15, f12, f11, f13, f10, f2]
  iframe Hpc Ha5 Ha2 Ha1 Ha3 Ha0 Hsp Hsp1 Hgp Hwin
  isplitl [Hw]
  · iapply (sepL_append _ _ _).2
    isplitr
    · rw [← instrAt_eq]; iexact Hcode
    iexact Hw
  iintro Hpc ⟨Ha5, Ha2, Ha1, Ha3, Ha0, Hsp, Hsp1⟩ - Hwin HMR
  ihave ⟨-, Hw⟩ := (sepL_append _ _ _).1 $$ HMR
  ihave Hw := stdWin_back simg $$ Hw
  ihave Hstd := stdioAt_close StdioOK StdWin simg hok himp $$ [Hw Hrest]
  · iframe Hw Hrest Himp
  ihave Hsp1 := sepL_spills_keep S.spills _ cs hkeep $$ Hsp1
  ihave Hwin := blockOwn_of_W Wf s'.toNat S.frameTop _ hWf $$ Hwin
  -- the callee-saved registers back together
  ihave Hsp1 := (sepL_spills S.spills cs).2 $$ Hsp1
  ihave Hsaved := (sepL_filter calleeSaved (fun q => decide (q ∈ S.spills.map Prod.fst))
    (fun q => q ↦ᵣ cs q)).2 $$ [Hsp1 Hsaved]
  · rw [hS.spillsSaved]; iframe Hsp1 Hsaved
  -- `fwrite(msg, 1, 14, stderr)` below `s'`
  have hfw := hHA.fwrite live Wp s' oomMsg 14#64 cs rodataDom (fun _ => False) rodataByte o hlive
    (fun i hi => .inl (oomMsg_text i hi)) ⟨by unfold fwriteNeed tohostAddr; omega, by omega, h6⟩
  unfold fwriteSpec at hfw
  have hj : JalExec (vsaModel live) S.fw.pc S.fw.code fwriteEntry :=
    hS.fwTgt ▸ JalSite.exec hS.fwCert live (hS.fwText.live hlive)
  ihave #Hjal := instrAt_of_binImg hS.fwText $$ Himg
  ihave #Hf := hfw
  iapply wp_callW Wp (v := r) hj
  iframe Hjal Hf
  rw [hS.fwPc]
  unfold VsaIris.ra
  iframe Hpc Hra
  isplitl [Ha0 Ha1 Ha2 Ha3 Ha5 Hargs Hstd Hcon Hsp Hscr Hsaved Htmp]
  · unfold argsAt callFrame readable VsaIris.sp stackScratch fwriteNeed VsaIris.gp
    simp only [List.zipIdx_cons, List.zipIdx_nil, sepL_cons, sepL_nil, List.length_cons,
      List.length_nil, Nat.add_zero, Nat.reduceAdd]
    iframe Ha0 Ha1 Ha2 Ha3 Hstd Hcon Hsp Hscr Hsaved Htmp Hgp Himg
    isplitl [Ha5 Hargs]
    · rw [show List.drop 4 argRegs = [14, 15, 16, 17] from rfl]
      iapply clobbered_put (r := 15) (rs := [14, 15, 16, 17]) (by decide)
      rw [show ([14, 15, 16, 17] : List Nat).erase 15 =
        ((((argRegs.erase 15).erase 12).erase 11).erase 13).erase 10 from rfl]
      iframe Hargs
      iexists _
      iexact Ha5
    isplitr
    · iapply binImg_rodata $$ Himg
    iapply ownSet_none
  -- `li a0,1; jal exit`
  rw [show S.head + 4 * S.stage + 4 = S.head + 4 * S.stage + 4 from rfl]
  unfold callFrame VsaIris.sp readable stackScratch fwriteNeed VsaIris.gp
  iintro Hpc Hra ⟨Hargs, -, Hstd, ⟨%o', Hcon⟩, ⟨Hsp, Hscr, Hsaved, Htmp, -, -⟩⟩
  ihave ⟨⟨%b0v, Ha0⟩, Hargs⟩ := clobbered_take (r := 10) (by decide) $$ Hargs
  iapply wp_segW live Wp S.li [(10, b0v)] [] (BitVec.ofNat 64 (S.head + 4 * S.stage + 4))
    (codeFoot S.head S.code) [] 0 hS.liLen hS.liWf (by change KeysOK [10]; decide) hS.liWr
    (fun a _ => by rw [hS.liLog]; trivial)
    (fun c hok' ⟨_, hMR, _, _⟩ => hS.liFacts _ _ (code_present hok' _ hMR hcodeL))
  simp only [sepL_cons, sepL_nil, hS.liPc, hS.liFin]
  rw [← instrAt_eq]
  iframe Hpc Ha0 Hcode
  iintro Hpc ⟨Ha0, -⟩ - -
  have hje : JalExec (vsaModel live) S.ex.pc S.ex.code exitEntry :=
    hS.exTgt ▸ JalSite.exec hS.exCert live (hS.exText.live hlive)
  ihave #Hjex := instrAt_of_binImg hS.exText $$ Himg
  iapply wp_jalW Wp hje
  rw [hS.exPc]
  unfold VsaIris.ra
  iframe Hjex Hpc Hra
  iintro Hpc Hra
  iapply Wp.lat_intro
  -- hand the abort continuation `exit(1)`'s entry
  iapply Hk
  unfold abortRes
  iapply abortAt_intro
  isplitl [Hpc Hra Ha0 Hsp Hargs Htmp Hsaved Hstd Hno Hcon]
  · unfold abortCore oomCore
    iright
    ihave ⟨Hs0, Hsaved⟩ := (sepL_calleeSaved cs).1 $$ Hsaved
    iexists s', BitVec.ofNat 64 (S.head + 4 * S.stage + 8 + 4), cs 8, o ++ o'
    unfold VsaIris.sp VsaIris.ra
    iframe Hpc Ha0 Hra Hs0 Hsp Htmp Hno Hcon
    isplitr
    · ipureintro
      exact ⟨h1, h2, by unfold exitNeed exitHandlersNeed; omega, by omega, h5, h6⟩
    isplitl [Hargs]
    · rw [show List.drop 1 argRegs = argRegs.erase 10 from rfl]; iexact Hargs
    isplitl [Hsaved]
    · iapply sepL_mono _ _ _ (fun q => by iintro H; iexists cs q; iexact H) $$ Hsaved
    iapply stdioAt_mono (fun img h => .inr h) $$ Hstd
  · unfold stackScratch
    ihave Hb := blockOwn_join s'.toNat S.frameTop (s'.toNat + S.frameTop)
      (n - (s'.toNat - 768 - (s.toNat - n)) - 768 - S.frameTop)
      (n - (s'.toNat - 768 - (s.toNat - n)) - 768) rfl (by omega) $$ [Hwin Hhi]
    · iframe Hwin Hhi
    ihave Hb := blockOwn_join (s'.toNat - 768) 768 s'.toNat
      (n - (s'.toNat - 768 - (s.toNat - n)) - 768) (n - (s'.toNat - 768 - (s.toNat - n)))
      (by omega) (by omega) $$ [Hscr Hb]
    · iframe Hscr Hb
    iapply blockOwn_join (s.toNat - n) (s'.toNat - 768 - (s.toNat - n)) (s'.toNat - 768)
      (n - (s'.toNat - 768 - (s.toNat - n))) n (by omega) (by omega) $$ [Hlo Hb]
    iframe Hlo Hb

end Wp

end VsaIris.Newlib.Oom
