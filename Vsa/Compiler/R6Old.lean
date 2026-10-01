import Vsa.Compiler.StmtT
import Vsa.Compiler.Fail
import Vsa.Compiler.R6Layout

namespace Vsa.Compiler

open Vsa.While Vsa.Sim

section
variable {code : List Ins}

theorem At.after {C : Ctx} {pos : Nat} (hAt : At code C pos) {p : Nat} (s : Stmt) (hp : pos ≤ p) {q : Nat}
    (hq : p + (cstmt C p s).1.length ≤ q) (hq' : PosOK q) : At code ⟨C.Γ, (cstmt C p s).2, C.brk, C.cont⟩ q :=
  have hn := cstmt_next C p s
  ⟨hAt.lay, hAt.ne, hAt.nd, fun i hi => Nat.lt_of_lt_of_le (hAt.lt i hi) hn.1, hAt.nat,
    by show (cstmt C p s).2 ≤ q; have := hAt.nextle; omega, hq'⟩

theorem Fail.cond {n : Nat} {C : Ctx} {pos L : Nat} {c : Expr} {st : St} {d : Nat} {env : Addr} {A : AM}
    (hAt : At code C pos) (hc : CondE C.Γ.names c) (s1 : Seg code pos (cexpr C.Γ 0 pos c))
    (s2 : Seg code (pos + (cexpr C.Γ 0 pos c).length)
      [.br .ne a0 0 (bSkip 1), .jal 0 (jOff (pos + (cexpr C.Γ 0 pos c).length + 1) L)])
    (hL : PosOK L) (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A)
    (hk : ∀ st1 v B, EvalE st d env c st1 v → SR C.Γ env st1 B →
      B.pc = pcOf (bif v.truthy then pos + (cexpr C.Γ 0 pos c).length + 2 else L) → Fail code n B) :
    Fail code n A := by
  obtain ⟨B1, r1, hB1⟩ := sim_cond (d := d) hAt hc (seg_app_iff.mpr ⟨s1, s2⟩) hL hA hsr
  rcases hB1 with ⟨st1, v, hev, hsr1, -, hpc1⟩ | ⟨hh, -⟩
  · exact Fail.of_star r1 (hk st1 v B1 hev hsr1 (by rw [hpc1]; cases v.truthy <;> rfl))
  · exact .inl ⟨B1, r1, hh⟩

theorem TSpec.fail {n : Nat} {st : St} {d : Nat} {env : Addr} {s : Stmt} {st1 : St} {t : Status}
    (h : TSpec code st d env s st1 t) {C : Ctx} {loop : Bool} {pos : Nat} {A : AM} (hAt : At code C pos)
    (hs : SupS C.Γ.names loop s) (hseg : Seg code pos (cstmt C pos s).1)
    (hpos : PosOK (pos + (cstmt C pos s).1.length)) (hloop : loop = true → PosOK C.brk ∧ PosOK C.cont)
    (hA : A.pc = pcOf pos) (hsr : SR C.Γ env st A)
    (hk : ∀ B, B.pc = pcOf (exitPos C (pos + (cstmt C pos s).1.length) t) → SR C.Γ env st1 B → Fail code n B) :
    Fail code n A := by
  obtain ⟨B, r, hpc, hsr1, -⟩ := h C loop pos A hAt hs hseg hpos hloop hA hsr
  exact Fail.of_star r (hk B hpc hsr1)

end

end Vsa.Compiler
