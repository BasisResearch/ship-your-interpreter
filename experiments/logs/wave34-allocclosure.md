# Wave 34 — AllocClosureContract inhabitant → fnArmGeom_closed → evalFnSim

Goal: inhabit `AllocClosureContract` (Vsa/Sim/AllocClosure.lean) from 3 machine pieces,
so `fnArmSeamRun_of_allocClosure → fnArmGeom_hArm_of_seam → fnArmSpec_of_geom → evalFnSim`
composes end-to-end.

## Chain state (verified before starting)
- `fnArmSeamRun_of_allocClosure` (rows/FnArmSeamReduce): GREEN, axiom-clean. Takes `AllocClosureContract` → `FnArmSeamRun`.
- `fnArmGeom_hArm_of_seam` (FnArmGeomReduce): part of same import, green.
- `fnArmSpec_of_geom` (ArmSpecBridge): FnArmGeom → FnArmSpec.
- `evalFnSim` (EvalFn): FnArmSpec → the recursor motive Triple. Green (conditional on FnArmSpec).
- `fnArmMallocCallBridge` (rows/FnArmMallocCallGen): GENERATED, the malloc-call span 0x800033c4→jal, bridgeOfSeg. Residual: hjalSeam.
- `storeRepr_pushClosure` (AllocClosure): GREEN axiom-clean — grows old store at φc' by pushClosure.

So EVERYTHING above the contract is landed. My job = the contract inhabitant.

## The `AllocClosureContract.spec` Triple (what to build)
Pre = the ArmEntryK-∃ dispatch predicate. Post (at fixed mpre, φc', p) exposes:
- mem=mpre; φc' size=p; p≠0; A.contains p 16; p%8=0; freshness; ClosureRepr mpre φf p cd;
  PhiExtends φc φc' size; StoreRepr mpre …; sret reads (kind4, payload φc' a, nonzero);
  + the big register/geometry/frame `hrest` bundle (mirrors ArmEntryK's tail + PC=0x800033ec).

## Disasm (eval_expr EX_FN arm)
```
prologue 0x80003164..0x800031ac : addi sp,-1088; spill s0/s2/ra/s1; mv s0,a2; mv s2,a1; mv s1,a0; jr a5
0x800033c4 li a0,16 ; sd a3,0(sp) ; jal malloc         <- fnArmMallocCall (GENERATED seg+bridge)
0x800033d0 ld a3,0(sp) ; beqz a0,OOM(0x80003e1c)         <- reload a3; OOM prune (nonNull_of_bounded)
0x800033d8 li a5,4 ; sd s0,0(a0) ; sd a3,8(a0)           <- closure build
0x800033e4 sd a0,8(s1) ; sw a5,0(s1)                     <- sret box (kind4 @ sret, payload p @ sret+8)
0x800033ec (join = epilogue entry)
```
- s0 = aExpr (fn Expr node) → closure[0]; ClosureRepr needs ExprRepr mpre aExpr (.fn …). ArmEntryK gives it.
- a3 = φf env (the env argument to eval_expr) → closure[8]. ClosureRepr needs read64(p+8)=φf env.

## KEY FINDING (a3 linkage)
ArmEntryK (EvalSimCommon:185) does NOT pin x13/a3. `eval_expr(sret,interp,expr,env)` receives
env in a3 from the CALLER; the prologue never touches a3. So `a3 = φf env` at the arm is a fact the
CALLER establishes, NOT carried by ArmEntryK. The contract Pre uses ArmEntryK, so a3=φf env must be
an ADDITIONAL named premise of the inhabitant (or the ArmEntryK-∃ predicate must be strengthened).
Since the contract's Pre is FIXED (fnArmSeamRun_of_allocClosure instantiates it as the ArmEntryK-∃),
I cannot add x13 to that Pre without changing the already-landed consumer. => a3=φf env becomes a
named typed premise `hA3Pre : ∀ c, Pre c → c.σ.regs.get? x13 = some (φf env image)`.
See observations.md entry.

## Progress
(to be filled incrementally)

## Coordinator recovery (after two watchdog stalls)
- `fnArmClosureBuild_mem_eq` heartbeat timeout FIXED per the stalled agent's own diagnosis:
  split into `fnArmClosureBuild_log_eq` (the concrete 4-entry log list, fast rfl — 0.43s)
  then offset-normalize (h0/h8/h4 + BitVec.add_zero) and one cheap foldl/applyW rfl.
  Whole file now 0.56s, green, axiom-clean (was: timeout at 800k + sorryAx).
  Also fixed a latent type error the timeout had masked: `swData 4#32` → `swData (4#64)`
  (swData : BitVec 64 → BitVec 32).
- Remaining: the AllocClosureContract inhabitant assembly (malloc splice over
  FnArmMallocCallGen ≫ OOM prune ≫ fnArmClosureBuildSeg ≫ post bundle w/
  storeRepr_pushClosure + the named hA3Pre premise).
