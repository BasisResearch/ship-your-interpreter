import Vsa.Compiler.CorrectG

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Halts Diverges output)

def latin1B (s : String) : Bool := s.toList.all fun c => decide (c.toNat < 256)

theorem latin1B_sound {s : String} (h : latin1B s = true) : Latin1 s := by
  simpa [latin1B, Latin1] using h

mutual
def wfEB (T : List String) (Γ : List (List String)) : Expr → Bool
  | .int n => decide (-2 ^ 63 ≤ n ∧ n < 2 ^ 63)
  | .str s => latin1B s && T.contains s
  | .bool _ => true
  | .null => true
  | .var _ => true
  | .assign _ e => wfEB T Γ e
  | .binary _ l r => wfEB T Γ l && wfEB T Γ r
  | .logical _ l r => wfEB T Γ l && wfEB T Γ r
  | .unary _ e => wfEB T Γ e
  | .call f args => wfEB T Γ f && wfArgsB T Γ args
  | .fn name params body =>
    latin1B (dispName name) && latin1B (catName name) && T.contains (dispName name) &&
      T.contains (catName name) && decide (params.length ≤ 120) &&
      decide ((frameNames params body).length ≤ 120) && decide (tSeq body ≤ 120) &&
      wfSeqB T (frameNames params body :: Γ) body

def wfArgsB (T : List String) (Γ : List (List String)) : List Expr → Bool
  | [] => true
  | e :: es => wfEB T Γ e && wfArgsB T Γ es

def wfOEB (T : List String) (Γ : List (List String)) : Option Expr → Bool
  | none => true
  | some e => wfEB T Γ e

def wfSB (T : List String) (Γ : List (List String)) : Stmt → Bool
  | .expr e => wfEB T Γ e
  | .varDecl x i => (Γ.headD []).contains x && wfOEB T Γ i
  | .block ss => decide ((frameNames [] ss).length ≤ 120) && wfSeqB T (frameNames [] ss :: Γ) ss
  | .ifStmt c t e => wfEB T Γ c && wfSB T Γ t && wfOSB T Γ e
  | .whileStmt c b => wfEB T Γ c && wfSB T Γ b
  | .forStmt i c st b =>
    decide ((forNames i b).length ≤ 120) && wfOSB T (forNames i b :: Γ) i && wfOEB T (forNames i b :: Γ) c &&
      wfOEB T (forNames i b :: Γ) st && wfSB T (forNames i b :: Γ) b
  | .ret e => wfOEB T Γ e
  | .brk => true
  | .cont => true

def wfOSB (T : List String) (Γ : List (List String)) : Option Stmt → Bool
  | none => true
  | some s => wfSB T Γ s

def wfSeqB (T : List String) (Γ : List (List String)) : List Stmt → Bool
  | [] => true
  | s :: ss => wfSB T Γ s && wfSeqB T Γ ss
end

section
variable {T : List String}

mutual
theorem wfEB_sound : ∀ {Γ : List (List String)} (e : Expr), wfEB T Γ e = true → WfE T Γ e
  | _, .int _, h => by simpa [wfEB, WfE, I64] using h
  | _, .str _, h => by
    simp only [wfEB, Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨latin1B_sound h.1, h.2⟩
  | _, .bool _, _ => trivial
  | _, .null, _ => trivial
  | _, .var _, _ => trivial
  | _, .assign _ e, h => wfEB_sound e h
  | _, .binary _ l r, h => by
    simp only [wfEB, Bool.and_eq_true] at h
    exact ⟨wfEB_sound l h.1, wfEB_sound r h.2⟩
  | _, .logical _ l r, h => by
    simp only [wfEB, Bool.and_eq_true] at h
    exact ⟨wfEB_sound l h.1, wfEB_sound r h.2⟩
  | _, .unary _ e, h => wfEB_sound e h
  | _, .call f args, h => by
    simp only [wfEB, Bool.and_eq_true] at h
    exact ⟨wfEB_sound f h.1, wfArgsB_sound args h.2⟩
  | _, .fn _ _ body, h => by
    simp only [wfEB, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
    exact ⟨latin1B_sound h1, latin1B_sound h2, h3, h4, h5, h6, h7, wfSeqB_sound body h8⟩

theorem wfArgsB_sound : ∀ {Γ : List (List String)} (es : List Expr), wfArgsB T Γ es = true → WfArgs T Γ es
  | _, [], _ => trivial
  | _, e :: es, h => by
    simp only [wfArgsB, Bool.and_eq_true] at h
    exact ⟨wfEB_sound e h.1, wfArgsB_sound es h.2⟩

theorem wfOEB_sound : ∀ {Γ : List (List String)} (e : Option Expr), wfOEB T Γ e = true → WfOE T Γ e
  | _, none, _ => trivial
  | _, some e, h => wfEB_sound e h

theorem wfSB_sound : ∀ {Γ : List (List String)} (s : Stmt), wfSB T Γ s = true → WfS T Γ s
  | _, .expr e, h => wfEB_sound e h
  | _, .varDecl _ i, h => by
    simp only [wfSB, Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨h.1, wfOEB_sound i h.2⟩
  | _, .block ss, h => by
    simp only [wfSB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, wfSeqB_sound ss h.2⟩
  | _, .ifStmt c t e, h => by
    simp only [wfSB, Bool.and_eq_true] at h
    exact ⟨wfEB_sound c h.1.1, wfSB_sound t h.1.2, wfOSB_sound e h.2⟩
  | _, .whileStmt c b, h => by
    simp only [wfSB, Bool.and_eq_true] at h
    exact ⟨wfEB_sound c h.1, wfSB_sound b h.2⟩
  | _, .forStmt i c st b, h => by
    simp only [wfSB, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    exact ⟨h1, wfOSB_sound i h2, wfOEB_sound c h3, wfOEB_sound st h4, wfSB_sound b h5⟩
  | _, .ret e, h => wfOEB_sound e h
  | _, .brk, _ => trivial
  | _, .cont, _ => trivial

theorem wfOSB_sound : ∀ {Γ : List (List String)} (s : Option Stmt), wfOSB T Γ s = true → WfOS T Γ s
  | _, none, _ => trivial
  | _, some s, h => wfSB_sound s h

theorem wfSeqB_sound : ∀ {Γ : List (List String)} (ss : List Stmt), wfSeqB T Γ ss = true → WfSeq T Γ ss
  | _, [], _ => trivial
  | _, s :: ss, h => by
    simp only [wfSeqB, Bool.and_eq_true] at h
    exact ⟨wfSB_sound s h.1, wfSeqB_sound ss h.2⟩
end

end

def supportedGB (p : Program) : Bool :=
  wfSeqB (strTab p) [globalNames p] p && (strTab p).all latin1B &&
    decide (strOff (strTab p) (strTab p).length ≤ 0x100000) && decide ((globalNames p).length ≤ 120) &&
    decide (tSeq p ≤ 120)

theorem supportedGB_sound {p : Program} (h : supportedGB p = true) : SupportedG p := by
  simp only [supportedGB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨wfSeqB_sound p h1, ⟨fun s hs => latin1B_sound (h2 s hs), h3, h4, h5⟩⟩

def fitsB (p : Program) : Bool := decide (0x80004800 + 4 * (compileG p).length ≤ 0x8001ad00)

theorem fitsB_sound {p : Program} (h : fitsB p = true) : 0x80004800 + 4 * (compileG p).length ≤ 0x8001ad00 :=
  of_decide_eq_true h

theorem checked_correct (p : Program) (hs : supportedGB p = true) (hf : fitsB p = true)
    (hcap : ∀ out, BigStep p out → BigStepBudget p out heapUnits) (c : Config)
    (hgood : GoodState c.σ) (htick : c.tick < 2)
    (hpc : c.σ.regs.get? Register.PC = some 0x80004800#64)
    (hpw : c.σ.regs.get? Register.htif_payload_writes = some 0#4)
    (hout : output c.σ = "")
    (hcode : ∀ k, k < (compileGBytes p).length →
      c.σ.mem[0x80004800 + k]? = (compileGBytes p)[k]?)
    (hlib : Code.__muldi3Loaded c.σ.mem ∧ Code.__divdi3Loaded c.σ.mem ∧
      Code.__umoddi3Loaded c.σ.mem ∧ Code.__hidden___udivdi3Loaded c.σ.mem ∧
      Code.__moddi3Loaded c.σ.mem) :
    (∀ out, BigStep p out ↔ Halts c out 0) ∧ (Diverges c → ¬ ∃ out, BigStep p out) :=
  compileG_correct p (supportedGB_sound hs) (fitsB_sound hf) hcap c hgood htick hpc hpw hout hcode hlib

end Vsa.Compiler
