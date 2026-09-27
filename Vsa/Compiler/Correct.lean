import Vsa.Compiler.StmtS
import Vsa.Compiler.Lift

/-!
# Compiler correctness

`compile_correct`: for every supported WHILE program `p` and every machine
configuration whose memory holds the bytes of `compile p` at `codeBase` (plus
libgcc's `__muldi3`/`__divdi3`/`__moddi3` and their cores, as in the interpreter
image), with the PC at `codeBase`, in a good machine state with an empty console,
the machine halts with exit code `0` and output `out` exactly when `out` is a
big-step behaviour of `p`, and a diverging machine means `p` has no behaviour —
the shape of `endToEnd_refinement`.
-/

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step Steps StepsN Halted Halts Diverges output)

/-- The machine code bytes of `compile p` (little-endian words). -/
def compileBytes (p : Program) : List (BitVec 8) :=
  (compile p).flatMap fun i => [byte i.encode 0, byte i.encode 1, byte i.encode 2, byte i.encode 3]

/-! ## From abstract runs to machine runs -/

theorem run_sim {code : List Ins} (hfit : Fits code) : ∀ {k : Nat} {A B : AM}, StarN code k A B →
    ∀ {c : Config}, Corr c A → CodeAt A.mem code → LibLoaded A.mem →
    ∃ c', Steps c c' ∧ c.steps + k ≤ c'.steps ∧ Corr c' B ∧ CodeAt B.mem code ∧ LibLoaded B.mem
  | _, _, _, .refl _, c, hc, hcode, hlib => ⟨c, .refl _, by simp, hc, hcode, hlib⟩
  | _, _, _, .step hs rest, c, hc, hcode, hlib => by
    obtain ⟨c1, hs1, hlt1, hc1⟩ := step_sim hc hcode hlib hs
    have hag := astep_mem_low hs
    obtain ⟨c2, hs2, hlt2, hc2, hcode2, hlib2⟩ := run_sim hfit rest hc1 (CodeAt.of_low hfit hag hcode)
      (LibLoaded.of_low hag hlib)
    exact ⟨c2, Vsa.Machine.Steps.trans hs1 hs2, by omega, hc2, hcode2, hlib2⟩

theorem StepsN.truncate' : ∀ {m : Nat} {a b : Config}, StepsN m a b → ∀ n, n ≤ m → ∃ c, StepsN n a c
  | _, a, _, .zero _, n, h => ⟨a, by rw [Nat.le_zero.mp h]; exact .zero _⟩
  | _, a, _, .succ s rest, n, h => by
    cases n with
    | zero => exact ⟨a, .zero _⟩
    | succ n =>
      obtain ⟨c, hc⟩ := StepsN.truncate' rest n (by omega)
      exact ⟨c, .succ s hc⟩

/-! ## The program image -/

/-- The compiled statement list. -/
def body (p : Program) : List Ins := (cseq ⟨[[]], 0, 0, 0⟩ mainPos p).1

theorem compile_eq (p : Program) :
    compile p = [Ins.jal 0 (jOff 0 mainPos)] ++ errCode ++ printCode ++ body p ++ exitCode 0 := rfl

theorem Seg.self (code : List Ins) : Seg code 0 code := fun j _ => by simp

theorem compile_segs (p : Program) :
    Seg (compile p) 0 [Ins.jal 0 (jOff 0 mainPos)] ∧ Seg (compile p) errPos errCode ∧
      Seg (compile p) printPos printCode ∧ Seg (compile p) mainPos (body p) ∧
      Seg (compile p) (mainPos + (body p).length) (exitCode 0) := by
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
  · exact Seg.pos_eq (by simp [mainPos, printPos, errPos]; omega) h5

theorem mainPos_val : mainPos = 100 := rfl

theorem flatMap4_get {α : Type} (f : Ins → List α) (hf : ∀ i, (f i).length = 4) :
    ∀ (l : List Ins) (k : Nat) (i : Ins), l[k]? = some i → ∀ j < 4,
      (l.flatMap f)[4 * k + j]? = (f i)[j]?
  | [], k, i, h, _, _ => by simp at h
  | a :: l, 0, i, h, j, hj => by
    simp at h; subst h
    rw [List.flatMap_cons, List.getElem?_append_left (by rw [hf]; omega)]
    simp
  | a :: l, k + 1, i, h, j, hj => by
    rw [List.flatMap_cons, List.getElem?_append_right (by rw [hf]; omega), hf]
    rw [show 4 * (k + 1) + j - 4 = 4 * k + j by omega]
    exact flatMap4_get f hf l k i (by simpa using h) j hj

theorem codeAt_of_bytes {p : Program} {m : Mem}
    (h : ∀ k, k < (compileBytes p).length → m[codeBase + k]? = (compileBytes p)[k]?) :
    CodeAt m (compile p) := by
  intro k i hk j hj
  have hlen : (compileBytes p).length = 4 * (compile p).length := by
    unfold compileBytes
    induction compile p with
    | nil => rfl
    | cons a l ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; omega
  have hk' : k < (compile p).length := (List.getElem?_eq_some_iff.mp hk).1
  rw [Nat.add_assoc, h _ (by omega), compileBytes,
    flatMap4_get _ (fun _ => rfl) _ k i hk j hj]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

/-! ## The abstract machine runs the program -/

def ctx0 : Ctx := ⟨[[]], 0, 0, 0⟩

theorem at0 (p : Program) (hfit : Fits (compile p)) : At (compile p) ctx0 mainPos := by
  obtain ⟨-, h2, h3, h4, h5⟩ := compile_segs p
  have hpo := Seg.end_ok hfit h5 (by simp [exitCode])
  refine ⟨⟨hfit, h2, h3⟩, by simp [ctx0], by simp [ctx0, Scope.slots], by simp [ctx0, Scope.slots],
    by simp [ctx0], by simp [ctx0], by unfold PosOK at *; omega⟩

/-- The initial abstract state: at `codeBase`, no known registers. -/
def A0 (m : Mem) (o : Array String) : AM := ⟨pcOf 0, [], m, o⟩

theorem enter (p : Program) (hfit : Fits (compile p)) (m : Mem) (o : Array String) :
    astep (compile p) (A0 m o) = some (.run ⟨pcOf mainPos, [], m, o⟩) := by
  obtain ⟨h1, -⟩ := compile_segs p
  have := at0 p hfit
  exact step_jump hfit h1.head rfl (by unfold PosOK Fits at *; decide) this.posok

theorem sr0 (m : Mem) (o : Array String) (ho : String.join o.toList = "") :
    SR ctx0.Γ 0 initSt ⟨pcOf mainPos, [], m, o⟩ := ⟨chain_init m, ho⟩

/-- A big-step behaviour is reached, and the code then exits with `0`. -/
theorem abstract_term (p : Program) (hsup : Supported p) (hfit : Fits (compile p)) (m : Mem)
    (o : Array String) (ho : String.join o.toList = "") {out : String} (hb : BigStep p out) :
    ∃ B, Star (compile p) (A0 m o) B ∧ astep (compile p) B = some (.halt 0) ∧
      String.join B.out.toList = out := by
  obtain ⟨st', D, rfl⟩ := hb
  obtain ⟨-, -, -, h4, h5⟩ := compile_segs p
  have hAt := at0 p hfit
  have hbl : (body p).length = (cseq ctx0 mainPos p).1.length := rfl
  have hpos := Seg.end_ok hfit h5 (by simp [exitCode])
  obtain ⟨B, r, hpc, hout, -, -, -, -⟩ := seqT (code := compile p) D ctx0 false mainPos _ [] [] rfl hAt
    hsup h4 (by unfold PosOK at *; omega) (fun h => by cases h) rfl (sr0 m o ho)
  obtain ⟨B', r', -, hBo, hh⟩ := run_exit hfit (by decide : (0 : Nat) = 0 ∨ 0 = 70) h5 (by
    rw [hpc]; rfl)
  exact ⟨B', Star.step (enter p hfit m o) (r.trans r'), hh, by rw [hBo]; exact hout⟩

/-- Without a big-step behaviour the code reaches the error exit or runs forever. -/
theorem abstract_stuck (p : Program) (hsup : Supported p) (hfit : Fits (compile p)) (m : Mem)
    (o : Array String) (ho : String.join o.toList = "") (hnb : ¬ ∃ out, BigStep p out) :
    (∃ B, Star (compile p) (A0 m o) B ∧ astep (compile p) B = some (.halt 70)) ∨
      ∀ n, ∃ B, StarN (compile p) n (A0 m o) B := by
  obtain ⟨-, -, -, h4, h5⟩ := compile_segs p
  have hAt := at0 p hfit
  have hbl : (body p).length = (cseq ctx0 mainPos p).1.length := rfl
  have hpos := Seg.end_ok hfit h5 (by simp [exitCode])
  have hne : ¬ ∃ st' t, ExecSeq initSt 0 0 p st' t := by
    rintro ⟨st', t, D⟩
    obtain ⟨-, -, -, -, -, -, hnorm, -⟩ := seqT (code := compile p) D ctx0 false mainPos _ [] [] rfl hAt
      hsup h4 (by unfold PosOK at *; omega) (fun h => by cases h) rfl (sr0 m o ho)
    exact hnb ⟨st'.out, st', by rw [← hnorm rfl]; exact D, rfl⟩
  have hf : ∀ n, Fail (compile p) n (A0 m o) := fun n =>
    Fail.of_star (Star.single (enter p hfit m o)) (seqFail_all n initSt 0 0 p ctx0 false mainPos _ [] []
      rfl hAt hsup h4 (by unfold PosOK at *; omega) (fun h => by cases h) rfl (sr0 m o ho) hne)
  by_cases hh : ∃ B, Star (compile p) (A0 m o) B ∧ astep (compile p) B = some (.halt 70)
  · exact .inl hh
  · exact .inr fun n => (hf n).resolve_left hh

/-! ## The machine -/

theorem halts_of_abstract {code : List Ins} (hfit : Fits code) {A B : AM} {c : Config} {e : Nat}
    (hc : Corr c A) (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem) (r : Star code A B)
    (hh : astep code B = some (.halt e)) : Halts c (String.join B.out.toList) e := by
  obtain ⟨k, hk⟩ := r
  obtain ⟨c', hs, -, hc', hcode', -⟩ := run_sim hfit hk hc hcode hlib
  obtain ⟨σf, hH, ho⟩ := halt_sim hc' hcode' hh
  exact ⟨c', σf, hs, hH, ho⟩

theorem diverges_of_abstract {code : List Ins} (hfit : Fits code) {A : AM} {c : Config}
    (hc : Corr c A) (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem)
    (h : ∀ n, ∃ B, StarN code n A B) : Diverges c := by
  intro n
  obtain ⟨B, hB⟩ := h n
  obtain ⟨c', hs, hle, -⟩ := run_sim hfit hB hc hcode hlib
  exact StepsN.truncate' (Vsa.Machine.Steps.toN_of_stepsField hs) n (by omega)

/-- **Compiler correctness.** For every program `p` in the supported subset, and
every machine configuration whose memory holds the code bytes of `compile p` at
`0x80004800` (below `tohost`), libgcc's multiply and signed divide/remainder
routines at their addresses in the interpreter image, with the PC at the code,
in a good machine state (`GoodState`) with an idle HTIF mailbox and an empty
console: the machine halts with exit code `0` and output `out` exactly when `out`
is a big-step behaviour of `p`, and a diverging machine means `p` has none. -/
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
  have hc : Corr c (A0 c.σ.mem c.σ.sailOutput) :=
    ⟨hgood, htick, by rw [hpc]; rfl, trivial, (fun _ h => by cases h), rfl, rfl, hpw⟩
  have hca : CodeAt (A0 c.σ.mem c.σ.sailOutput).mem (compile p) := codeAt_of_bytes hcode
  have ho : String.join c.σ.sailOutput.toList = "" := hout
  have term : ∀ out, BigStep p out → Halts c out 0 := by
    intro out hb
    obtain ⟨B, r, hh, hBo⟩ := abstract_term p hsup hfit' c.σ.mem c.σ.sailOutput ho hb
    have := halts_of_abstract hfit' hc hca hlib r hh
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
    · have := halts_of_abstract hfit' hc hca hlib r hh
      exact absurd (hH.deterministic this).2 (by decide)
    · exact (diverges_of_abstract hfit' hc hca hlib hdiv).not_halts hH

#print axioms compile_correct

end Vsa.Compiler
