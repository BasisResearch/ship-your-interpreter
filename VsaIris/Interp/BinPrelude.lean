import VsaIris.Interp.ArmCore
import VsaIris.Interp.Case.BinaryAddIntT
import VsaIris.Interp.SymInterp

/-!
The shared `eval_expr` prelude of every binary operator: entry, spill, the left and right
child calls, up to the operator dispatch at `0x8000351c`. `binPreludeT` (total, counted) and
`binPreludeP` (partial, with abort) hand the arm to an operator tail with the named state
`BinMid` and the caller's exit contract (`ExitK`, and `AbortK` for the partial spec).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Sym VsaIris.MallocFast VsaIris.Inst VsaIris.Newlib
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-- Geometry of an `eval_expr` activation with frame base `s`, return address `ret`,
result slot `sret` and stack budget `n`. -/
structure ArmGeo (s ret sret : BitVec 64) (n : Nat) : Prop where
  sf : (evalSP s).toNat = s.toNat - 1088
  lo : 0x87800000 + 1088 ≤ s.toNat
  hi : s.toNat ≤ 0x88000000
  al : s.toNat % 16 = 0
  sg : StackGeom s n
  need : 1088 ≤ n
  ral : ret.toNat % 4 = 0
  slg : SlotGeom sret

theorem ArmGeo.off {s ret sret : BitVec 64} {n : Nat} (g : ArmGeo s ret sret n) (c : Nat)
    (hc : c < 4096) : (evalSP s + BitVec.ofNat 64 c).toNat = s.toNat - 1088 + c :=
  evalSP_off g.sf (by have := g.hi; omega) c hc

/-- The binary-operator node at `aX` (read-only view and operator token). -/
structure BinOpNode (m : Mem) (P : Nat → Prop) (aX : BitVec 64) (tok : Nat) : Prop where
  op : ldv .lw m (aX + 8#64).toNat = BitVec.ofNat 64 tok
  view : ∀ a ∈ binView aX.toNat, P a ∧ (m[a]?).isSome = true
  lo : 0x80000000 ≤ aX.toNat
  hi : aX.toNat + 32 ≤ 0x100000000
  off : aX.toNat + 32 ≤ Vsa.Sim.tohostAddr ∨ Vsa.Sim.tohostAddr + 16 ≤ aX.toNat

/-- Machine state of a binary arm at the operator dispatch `0x8000351c`: both operand values
are in their result slots (`+120`, `+144`), the left kind is spilled at the frame base. -/
structure BinMid (s sret inp : BitVec 64) (rv R : Nat → BitVec 64) (Mt : Mem) (ret aX : BitVec 64)
    (lv rv' : Value) (w0 w1 w2 u0 u1 u2 : BitVec 64) : Prop where
  r2 : R 2 = evalSP s
  r8 : R 8 = aX
  r9 : R 9 = sret
  r18 : R 18 = inp
  r19 : R 19 = w1
  hi : ∀ x ∈ hiSaved, R x = rv x
  sp : rv 2 = s
  saved : EvalSaved Mt s ret (rv 8) (rv 9) (rv 18) (rv 19)
  kl : ldv .ld Mt (s.toNat - 1088) = BitVec.ofNat 64 (valTag lv)
  kr : ldv .lw Mt (evalSP s + 144#64).toNat = BitVec.ofNat 64 (valTag rv')
  l0 : ldv .ld Mt (evalSP s + 120#64).toNat = w0
  l1 : ldv .ld Mt (evalSP s + 128#64).toNat = w1
  l2 : ldv .ld Mt (evalSP s + 136#64).toNat = w2
  q0 : ldv .ld Mt (evalSP s + 144#64).toNat = u0
  q1 : ldv .ld Mt (evalSP s + 152#64).toNat = u1
  q2 : ldv .ld Mt (evalSP s + 160#64).toNat = u2
  tl : w0.toNat % 2 ^ 32 = valTag lv
  tr : u0.toNat % 2 ^ 32 = valTag rv'

/-- Machine state of a binary arm after the left child returned (`0x800034fc`). -/
structure BinLeft (s sret inp aE : BitVec 64) (rv R : Nat → BitVec 64) (Mt : Mem) (ret aX : BitVec 64)
    (lv : Value) (w0 w1 w2 : BitVec 64) : Prop where
  r2 : R 2 = evalSP s
  r8 : R 8 = aX
  r9 : R 9 = sret
  r18 : R 18 = inp
  hi : ∀ x ∈ hiSaved, R x = rv x
  sp : rv 2 = s
  saved : EvalSaved Mt s ret (rv 8) (rv 9) (rv 18) (rv 19)
  ae : ldv .ld Mt (s.toNat - 1088) = aE
  kl : ldv .lw Mt (evalSP s + 120#64).toNat = BitVec.ofNat 64 (w0.toNat % 2 ^ 32)
  l0 : ldv .ld Mt (evalSP s + 120#64).toNat = w0
  l1 : ldv .ld Mt (evalSP s + 128#64).toNat = w1
  l2 : ldv .ld Mt (evalSP s + 136#64).toNat = w2
  tl : w0.toNat % 2 ^ 32 = valTag lv

/-- The right operand of a binary node. -/
structure BinRight (m : Mem) (P : Nat → Prop) (aX : BitVec 64) (r : Expr) (aR : Nat) : Prop where
  ptr : ldv .ld m (aX + 24#64).toNat = BitVec.ofNat 64 aR
  repr : ExprReprWithin m P aR r
  lt : aR < 2 ^ 64
  ok : ∀ k, P k → ReadOK k

theorem binMid_of_left {n : Nat} {s sret inp aE ret aX w0 w1 w2 u0 u1 u2 aR kL : BitVec 64}
    {rv R R2 : Nat → BitVec 64} {Mt : Mem} {lv rv' : Value}
    (g : ArmGeo s ret sret n) (b : BinLeft s sret inp aE rv R Mt ret aX lv w0 w1 w2)
    (h9 : R2 9 = sret) (h19 : R2 19 = w1)
    (hk : KeepRegs calleeSaved (upd (upd (upd (upd (upd (upd R 12 aR) 13 aE) 16 kL) 10
      (evalSP s + 144#64)) 11 inp) 19 w1) R2)
    (htr : u0.toNat % 2 ^ 32 = valTag rv') :
    BinMid s sret inp rv (upd R2 1 (BitVec.ofNat 64 (0x80003518 + 4)))
      (slotWrite (Vsa.Sim.writeLog Mt [(s.toNat - 1088, 8, BitVec.ofNat 64 (w0.toNat % 2 ^ 32))])
        (evalSP s + 144#64).toNat u0 u1 u2) ret aX lv rv' w0 w1 w2 u0 u1 u2 := by
  have hoff := g.off
  have hsf := g.sf; have hs2 := g.hi; have hs' := g.lo
  have htr' : u0.toNat % 2 ^ 32 < 2 ^ 31 := by rw [htr]; exact valTag_lt _
  exact {
    r2 := by ix_reg; rw [hk 2 (by decide)]; ix_reg; exact b.r2
    r8 := by ix_reg; rw [hk 8 (by decide)]; ix_reg; exact b.r8
    r9 := by ix_reg; exact h9
    r18 := by ix_reg; rw [hk 18 (by decide)]; ix_reg; exact b.r18
    r19 := by ix_reg; exact h19
    hi := fun x hx => by
      have e := b.hi x hx
      simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (ix_reg; rw [hk _ (by decide)]; ix_reg; exact e)
    sp := b.sp
    saved := EvalSaved.slotWrite (EvalSaved.store b.saved _ (by omega)) _ _ _
      (by rw [hoff 144 (by decide)]; omega)
    kl := by ix_fwd; rw [ofNat_lo32 b.tl]
    kr := by ix_fwd; exact ofNat_lo32 htr
    l0 := by ix_fwd; exact b.l0
    l1 := by ix_fwd; exact b.l1
    l2 := by ix_fwd; exact b.l2
    q0 := by ix_fwd
    q1 := by ix_fwd
    q2 := by ix_fwd
    tl := b.tl
    tr := htr }

/-- A reflected `eval_expr` epilogue from `pc` to the return address. -/
def EpiRun (pc : BitVec 64) : Prop :=
  ∀ {live : Nat → Prop}, (∀ p ∈ interpText, live p.1) →
  ∀ {m : Mem} {DA : List Nat} {s ret sret : BitVec 64} {R : Nat → BitVec 64} {Mt : Mem} {n : Nat}
    {v8 v9 v18 v19 : BitVec 64},
    ArmGeo s ret sret n → R 2 = evalSP s → EvalSaved Mt s ret v8 v9 v18 v19 →
    MRun live m DA (InExt (s.toNat - 1088, 1088)) pc ret R Mt
      (fun R' _ => EpiPost R R' s ret v8 v9 v18 v19)

set_option hygiene false in
macro "epi_run" : tactic => `(tactic| (
  intro live hlive m DA s ret sret R Mt n v8 v9 v18 v19 g h2 hsv Q hk
  have hsf : (s + 18446744073709550528#64).toNat = s.toNat - 1088 := g.sf
  have hs := g.lo; have hs2 := g.hi; have hs3 := g.al; have hal := g.ral
  have h2' : R 2 = s + 18446744073709550528#64 := h2
  have hoff := evalSP_off (s := s) hsf (by omega)
  have hRA : ldv .ld Mt (s + 18446744073709550528#64 + 1080#64).toNat = ret := by
    rw [hoff _ (by decide)]; exact hsv.ra
  have hS0 : ldv .ld Mt (s + 18446744073709550528#64 + 1072#64).toNat = v8 := by
    rw [hoff _ (by decide)]; exact hsv.s0
  have hS1 : ldv .ld Mt (s + 18446744073709550528#64 + 1064#64).toNat = v9 := by
    rw [hoff _ (by decide)]; exact hsv.s1
  have hS2 : ldv .ld Mt (s + 18446744073709550528#64 + 1056#64).toNat = v18 := by
    rw [hoff _ (by decide)]; exact hsv.s2
  have hS3 : ldv .ld Mt (s + 18446744073709550528#64 + 1048#64).toNat = v19 := by
    rw [hoff _ (by decide)]; exact hsv.s3
  clear g h2 hsv hoff
  sym_run hlive using [h2', hRA, hS0, hS1, hS2, hS3, hsf, hal]
  refine hk _ _ ⟨by ix_reg, by ix_reg; exact evalSP_restore s, by ix_reg, by ix_reg, by ix_reg,
    by ix_reg, fun x hx => ?_⟩
  simp only [hiSaved, List.mem_cons, List.not_mem_nil, _root_.or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> ix_reg))

section

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

/-- The frame of a binary arm after its prelude. -/
abbrev binArmF (N : NativeAddrs) (P : Nat → Prop) (m : Mem) (env : Nat) (aE s : BitVec 64)
    (n : Nat) (sret : BitVec 64) (Wd K : IProp GF) : IProp GF :=
  evalArmF P m env aE (evalSP s) (n - 1088) (slot24 sret.toNat) Wd K

/-- The abort contract of the partial spec's continuation `K`. -/
def AbortK (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF) (inp : Nat)
    (Core : IProp GF) (s sret : BitVec 64) (n : Nat) (K : IProp GF) : Prop :=
  K ⊢ □ errCtx inp ∗ (abortAt Core s n ∗ slot24 sret.toNat -∗ Wp.W Φ)

/-- What an operator tail proves from the dispatch point. -/
def BinTail (Wp : MachWP (GF := GF) (vsaModel live)) (Φ : Nat × String → IProp GF)
    (N : NativeAddrs) (F : IProp GF) (R : Nat → BitVec 64) (s : BitVec 64) (Mt : Mem)
    (lv rv' : Value) (w0 w1 w2 u0 u1 u2 : BitVec 64) : Prop :=
  (□ valOf N lv w0 w1 w2 ∗ □ valOf N rv' u0 u1 u2) ∗ F ∗
    ms 0x8000351c#64 R (InExt (s.toNat - 1088, 1088)) Mt ⊢ Wp.W Φ

theorem BinTail.ints {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {F : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem} {a b : Int}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : w1.toInt = a → u1.toInt = b →
      ArmAt Wp Φ F 0x8000351c#64 R (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N F R s Mt (.int a) (.int b) w0 w1 w2 u0 u1 u2 := by
  unfold BinTail valOf
  iintro ⟨⟨%⟨_, h1⟩, %⟨_, h2⟩⟩, HF, Hms⟩
  iapply (h h1 h2)
  iframe HF Hms

theorem BinTail.strs {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {P : Nat → Prop} {m : Mem} {env : Nat} {aE s' : BitVec 64} {n' : Nat}
    {Out Wd K : IProp GF} {R : Nat → BitVec 64} {s : BitVec 64} {Mt : Mem} {x y : String}
    {w0 w1 w2 u0 u1 u2 : BitVec 64}
    (h : ArmAt Wp Φ (evalArmF P m env aE s' n' Out Wd
      iprop(K ∗ □ (strAt w1.toNat x ∗ strAt u1.toNat y))) 0x8000351c#64 R
      (InExt (s.toNat - 1088, 1088)) Mt) :
    BinTail Wp Φ N (evalArmF P m env aE s' n' Out Wd K) R s Mt (.str x) (.str y) w0 w1 w2 u0 u1 u2 := by
  unfold BinTail valOf
  iintro ⟨⟨⟨-, #Hx⟩, ⟨-, #Hy⟩⟩, HF, Hms⟩
  iapply h
  iframe Hms
  unfold evalArmF
  icases HF with ⟨#Hc, #Hr, #Hf, Hs, Ho, Hw, HK⟩
  iframe Hc Hr Hf Hs Ho Hw HK
  iframe Hx Hy

theorem ExitK.frame {Wp : MachWP (GF := GF) (vsaModel live)} {Φ : Nat × String → IProp GF}
    {N : NativeAddrs} {s ret sret : BitVec 64} {rv : Nat → BitVec 64} {n : Nat} {v : Value}
    {Wd K : IProp GF} (X : IProp GF) [Persistent X] (h : ExitK Wp Φ N s ret sret rv n v Wd K) :
    ExitK Wp Φ N s ret sret rv n v Wd iprop(K ∗ X) := by
  intro R' hk
  iintro ⟨Hpc, Hra, Hr, Hs, Hv, Hw, HK, -⟩
  iapply h R' hk
  iframe Hpc Hra Hr Hs Hv Hw HK

end

end VsaIris.Interp
