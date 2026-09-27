import Vsa.Sim.EvalChildArm

/-!
# `EvalChildArmRet` — the value-return instance of `EvalChildArm`

The `ret e` arm (`0x80004120`: `ld a2,8(s0); beqz a2 (not taken: the
expression is present); mv a3,s3; mv a1,s1; addi a0,sp,16; jal eval_expr`).
-/

