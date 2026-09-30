import Vsa.Compiler.Lift
import Vsa.Compiler.Run

namespace Vsa.Compiler

open Vsa.While Vsa.Sim LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config Step Steps StepsN Halted Halts Diverges output)

structure RunSim (code : List Ins) (k : Nat) (c : Config) (B : AM) (c' : Config) : Prop where
  steps : Steps c c'
  count : c.steps + k ≤ c'.steps
  corr : Corr c' B
  code : CodeAt B.mem code
  lib : LibLoaded B.mem

theorem run_sim {code : List Ins} (hfit : Fits code) : ∀ {k : Nat} {A B : AM}, StarN code k A B →
    ∀ {c : Config}, Corr c A → CodeAt A.mem code → LibLoaded A.mem →
    ∃ c', RunSim code k c B c'
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

theorem Seg.self (code : List Ins) : Seg code 0 code := fun j _ => by simp

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

def codeBytes (code : List Ins) : List (BitVec 8) :=
  code.flatMap fun i => [byte i.encode 0, byte i.encode 1, byte i.encode 2, byte i.encode 3]

theorem codeBytes_length : ∀ code : List Ins, (codeBytes code).length = 4 * code.length
  | [] => rfl
  | a :: l => by
    have ih := codeBytes_length l
    unfold codeBytes at ih ⊢
    rw [List.flatMap_cons, List.length_append, ih]
    simp only [List.length_cons, List.length_nil]
    omega

theorem codeAt_of_codeBytes {code : List Ins} {m : Mem}
    (h : ∀ k, k < (codeBytes code).length → m[codeBase + k]? = (codeBytes code)[k]?) :
    CodeAt m code := by
  intro k i hk j hj
  have hlen := codeBytes_length code
  have hk' : k < code.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [Nat.add_assoc, h _ (by omega), codeBytes,
    flatMap4_get _ (fun _ => rfl) _ k i hk j hj]
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

def A0 (m : Mem) (o : Array String) : AM := ⟨pcOf 0, [], m, o⟩

theorem halts_of_abstract {code : List Ins} (hfit : Fits code) {A B : AM} {c : Config} {e : Nat}
    (hc : Corr c A) (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem) (r : Star code A B)
    (hh : astep code B = some (.halt e)) : Halts c (String.join B.out.toList) e := by
  obtain ⟨k, hk⟩ := r
  obtain ⟨c', hs, -, hc', hcode', -⟩ := run_sim hfit hk hc hcode hlib
  obtain ⟨σf, hH, ho⟩ := halt_sim hc' hcode' hh
  exact ⟨c', σf, hs, hH, ho⟩

theorem diverges_of_abstract {code : List Ins} (hfit : Fits code) {A : AM} {c : Config}
    (hc : Corr c A) (hcode : CodeAt A.mem code) (hlib : LibLoaded A.mem)
    (h : ∀ n, Runs code n A) : Diverges c := by
  intro n
  obtain ⟨B, hB⟩ := h n
  obtain ⟨c', hs, hle, -⟩ := run_sim hfit hB hc hcode hlib
  exact StepsN.truncate' (Vsa.Machine.Steps.toN_of_stepsField hs) n (by omega)

end Vsa.Compiler
