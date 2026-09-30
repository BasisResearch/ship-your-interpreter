import Vsa.Sim.HelperCall

/-!
# `HelperCallEnvDefine` — the `env_define` contract and its adapter

`env_define(env, name, pv)` binds `name` to the value at `pv` in the frame at
`env` (`Store.define`): the update path rewrites an existing slot, the append
path grows the frame's arrays through the allocator.  No whole-function
contract of `env_define` is proved (`EnvDefSpec.lean` records the composed
proof as remaining; `EnvDefCompose` composes the paths over their
straight-line bridges).  This file states the contract the statement arms
consume, ONCE, as a named premise:

* `EnvDefineEntryState`: the state the parametric call parks at
  (`HelperCall.Parked` with `a0 = env`, `a1 = name`, `a2 = pv`) together
  with the memory facts every consumer has (`EnvDefineMem`: the fixed code
  image, the represented store and its stack survival, the name string, the
  represented value, the in-frame buffer, the stack budget);
* `EnvDefineReturnState`: the return at the link PC with the `Store.define`
  result represented, memory unchanged outside the arena and the callee's
  stack window, presence preserved, output unchanged;
* `EnvDefineContract`: the Triple between them, for all ghosts.

**Supplier.** `EnvDefCompose.envDefContract` over the update
(`EnvDefSpec3.env_define_update_post`), append and grow paths; the append and
grow paths need the allocator contracts (`MallocContract`, `ReallocOps`) and
the allocator-private footprint inside the arena (task 2 of the plan).  The
contract is consumed by `hSVarInit` and `hSVarNull` (below), and is the same
seam `hAssign` and `hCallClosure` need.
-/

