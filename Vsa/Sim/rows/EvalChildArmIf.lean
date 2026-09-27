import Vsa.Sim.EvalChildArm
import Vsa.Sim.ExecCondArmSites

/-!
# `EvalChildArmIf` — the if-condition instance of `EvalChildArm`

The `if` arm's condition call (`0x800041e8`: `ld a2,8(s0); mv a3,s3; mv a1,s1;
addi a0,sp,56; jal eval_expr`), for both `ifStmt c t none` and
`ifStmt c t (some e)`.
-/

