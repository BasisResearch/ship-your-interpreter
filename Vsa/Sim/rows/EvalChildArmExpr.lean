import Vsa.Sim.EvalChildArm

/-!
# `EvalChildArmExpr` — the expression-statement instance of `EvalChildArm`

The `expr` arm (`0x80004170`: `ld a2,8(s0); addi a0,sp,16; mv a3,s3; mv a1,s1;
jal eval_expr`).
-/

