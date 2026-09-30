import Vsa.Compiler.StmtS
import Vsa.Compiler.AbsLift

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step Steps StepsN Halted Halts Diverges output)

def compileBytes (p : Program) : List (BitVec 8) :=
  (compile p).flatMap fun i => [byte i.encode 0, byte i.encode 1, byte i.encode 2, byte i.encode 3]

def body (p : Program) : List Ins := (cseq ⟨[[]], 0, 0, 0⟩ mainPos₀ p).1

theorem compile_eq (p : Program) :
    compile p = [Ins.jal 0 (jOff 0 mainPos₀)] ++ errCode ++ printCode ++ body p ++ exitCode 0 := rfl

theorem compile_segs (p : Program) :
    Seg (compile p) 0 [Ins.jal 0 (jOff 0 mainPos₀)] ∧ Seg (compile p) errPos errCode ∧
      Seg (compile p) printPos printCode ∧ Seg (compile p) mainPos₀ (body p) ∧
      Seg (compile p) (mainPos₀ + (body p).length) (exitCode 0) := by
  have h := Seg.self (compile p)
  rw [compile_eq] at h
  obtain ⟨h1234, h5⟩ := h.append
  obtain ⟨h123, h4⟩ := h1234.append
  obtain ⟨h12, h3⟩ := h123.append
  obtain ⟨h1, h2⟩ := h12.append
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [compile_eq]
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact Seg.pos_eq (by simp [mainPos₀, printPos, errPos]; omega) h5

theorem mainPos_val : mainPos₀ = 100 := rfl

theorem codeAt_of_bytes {p : Program} {m : Mem}
    (h : ∀ k, k < (compileBytes p).length → m[codeBase + k]? = (compileBytes p)[k]?) :
    CodeAt m (compile p) := codeAt_of_codeBytes h

def ctx0 : Ctx := ⟨[[]], 0, 0, 0⟩

theorem at0 (p : Program) (hfit : Fits (compile p)) : At (compile p) ctx0 mainPos₀ := by
  obtain ⟨-, h2, h3, h4, h5⟩ := compile_segs p
  have hpo := Seg.end_ok hfit h5 (by simp [exitCode])
  refine ⟨⟨hfit, h2, h3⟩, by simp [ctx0], by simp [ctx0, Scope.slots], by simp [ctx0, Scope.slots],
    by simp [ctx0], by simp [ctx0], by unfold PosOK at *; omega⟩

theorem enter (p : Program) (hfit : Fits (compile p)) (m : Mem) (o : Array String) :
    astep (compile p) (A0 m o) = some (.run ⟨pcOf mainPos₀, [], m, o⟩) := by
  obtain ⟨h1, -⟩ := compile_segs p
  have := at0 p hfit
  exact step_jump hfit h1.head rfl (by unfold PosOK Fits at *; decide) this.posok

theorem sr0 (m : Mem) (o : Array String) (ho : String.join o.toList = "") :
    SR ctx0.Γ 0 initSt ⟨pcOf mainPos₀, [], m, o⟩ := ⟨chain_init m, ho⟩

theorem abstract_term (p : Program) (hsup : Supported p) (hfit : Fits (compile p)) (m : Mem)
    (o : Array String) (ho : String.join o.toList = "") {out : String} (hb : BigStep p out) :
    Reaches (compile p) (A0 m o) fun B => astep (compile p) B = some (.halt 0) ∧
      String.join B.out.toList = out := by
  obtain ⟨st', D, rfl⟩ := hb
  obtain ⟨-, -, -, h4, h5⟩ := compile_segs p
  have hAt := at0 p hfit
  have hbl : (body p).length = (cseq ctx0 mainPos₀ p).1.length := rfl
  have hpos := Seg.end_ok hfit h5 (by simp [exitCode])
  obtain ⟨B, r, hpc, hout, -, -, -, -⟩ := seqT (code := compile p) D ctx0 false mainPos₀ _ [] [] rfl hAt
    hsup h4 (by unfold PosOK at *; omega) (fun h => by cases h) rfl (sr0 m o ho)
  obtain ⟨B', r', -, hBo, hh⟩ := run_exit hfit (by decide : (0 : Nat) = 0 ∨ 0 = 70) h5 (by
    rw [hpc]; rfl)
  exact ⟨B', Star.step (enter p hfit m o) (r.trans r'), hh, by rw [hBo]; exact hout⟩

theorem abstract_stuck (p : Program) (hsup : Supported p) (hfit : Fits (compile p)) (m : Mem)
    (o : Array String) (ho : String.join o.toList = "") (hnb : ¬ ∃ out, BigStep p out) :
    Reaches (compile p) (A0 m o) (fun B => astep (compile p) B = some (.halt 70)) ∨
      ∀ n, Runs (compile p) n (A0 m o) := by
  obtain ⟨-, -, -, h4, h5⟩ := compile_segs p
  have hAt := at0 p hfit
  have hbl : (body p).length = (cseq ctx0 mainPos₀ p).1.length := rfl
  have hpos := Seg.end_ok hfit h5 (by simp [exitCode])
  have hne : ¬ HasSeqExec initSt 0 0 p := by
    rintro ⟨st', t, D⟩
    obtain ⟨-, -, -, -, -, -, hnorm, -⟩ := seqT (code := compile p) D ctx0 false mainPos₀ _ [] [] rfl hAt
      hsup h4 (by unfold PosOK at *; omega) (fun h => by cases h) rfl (sr0 m o ho)
    exact hnb ⟨st'.out, st', by rw [← hnorm rfl]; exact D, rfl⟩
  have hf : ∀ n, Fail (compile p) n (A0 m o) := fun n =>
    Fail.of_star (Star.single (enter p hfit m o)) (seqFail_all n initSt 0 0 p ctx0 false mainPos₀ _ [] []
      rfl hAt hsup h4 (by unfold PosOK at *; omega) (fun h => by cases h) rfl (sr0 m o ho) hne)
  by_cases hh : Reaches (compile p) (A0 m o) (fun B => astep (compile p) B = some (.halt 70))
  · exact .inl hh
  · exact .inr fun n => (hf n).resolve_left hh

theorem compile_correct (p : Program) (hsup : Supported p)
    (hfit : 0x80004800 + 4 * (compile p).length ≤ 0x8001ad00) (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileBytes p).length →
      c.σ.mem[0x80004800 + k]? = (compileBytes p)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) := by
  have hfit' : Fits (compile p) := hfit
  have hlib' : LibLoaded (A0 c.σ.mem c.σ.sailOutput).mem :=
    let ⟨h1, h2, h3, h4, h5⟩ := hlib; ⟨h1, h2, h3, h4, h5⟩
  have hc : Corr c (A0 c.σ.mem c.σ.sailOutput) :=
    ⟨hgood, htick, by rw [hpc]; rfl, trivial, (fun _ h => by cases h), rfl, rfl, hpw⟩
  have hca : CodeAt (A0 c.σ.mem c.σ.sailOutput).mem (compile p) := codeAt_of_bytes hcode
  have ho : String.join c.σ.sailOutput.toList = "" := hout
  have term : ∀ out, BigStep p out → Halts c out 0 := by
    intro out hb
    obtain ⟨B, r, hh, hBo⟩ := abstract_term p hsup hfit' c.σ.mem c.σ.sailOutput ho hb
    have := halts_of_abstract hfit' hc hca hlib' r hh
    rwa [hBo] at this
  refine ⟨fun out => ⟨term out, fun hH => ?_⟩, fun hd ⟨out, hb⟩ => hd.not_halts (term out hb)⟩
  by_cases hnb' : BigStep p out
  · exact hnb'
  have hnb : ¬ BigStep p out := hnb'
  exfalso
  by_cases hex : ∃ out', BigStep p out'
  · obtain ⟨out', hb'⟩ := hex
    obtain ⟨rfl, -⟩ := hH.deterministic (term out' hb')
    exact hnb hb'
  · rcases abstract_stuck p hsup hfit' c.σ.mem c.σ.sailOutput ho hex with ⟨B, r, hh⟩ | hdiv
    · have := halts_of_abstract hfit' hc hca hlib' r hh
      exact absurd (hH.deterministic this).2 (by decide)
    · exact (diverges_of_abstract hfit' hc hca hlib' hdiv).not_halts hH

#print axioms compile_correct

end Vsa.Compiler
