import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.EnvDefineClose
import Vsa.Sim.EnvDefSpec3
import Vsa.Sim.StrlenSpec
import Vsa.Sim.MemcpySpec4

/-!
# `EnvDefCompose` — the composed `env_define` contract (Shape-D)

Step 5 of `experiments/interp-sim-completion-plan.md`.  `env_define` is the
biggest semantic gap: its append/grow paths call `strlen`, `malloc`, `memcpy`,
and `realloc` (twice).  Every one of those calls is a Shape-D `jal rd` splice
`prefix ≫ callee ≫ suffix` (`Vsa/Sim/DeriveCallSeg.lean`, `callSeg`), with the
callee contract threaded as a NAMED HYPOTHESIS — `MallocContract` (`Vsa/Alloc.lean`,
the plan's `MallocSpec`), `ReallocOps` (`Vsa/Sim/ReallocSpec.lean`), `strlen_spec`
(`StrlenSpec`), `memcpy_spec` (`MemcpySpec4`).  None is a Lean `axiom`; each is a
structure field or a proved Triple.

This file lands the **maximal composition skeleton**, modelling `divValueTail`
(`Vsa/Sim/BinOpValueTails.lean`): the whole append and grow paths are assembled as
`callSeg` chains over the real callee contracts, with the per-block MACHINE
BRIDGES stated as named hypotheses.  Each bridge is a straight-line
`#derive_case`/`chain_facts` segment (Shape-A) — the honest remaining machine
work — but the CALL COMPOSITION (the hard Shape-D algebra) is proved here and is
axiom-clean.  The consumer (`Call.closure`/`varDecl`/`assign`) sees one Triple.

## Control-flow map (from `experiments/disasm.txt`; recap of `EnvDefSpec2` header)

```
PROLOGUE 0x80002a5c..0x80002a90  ── PROVED (EnvDefSpec17.env_define_prologue)
  blez s3 → CAP-INIT   (count == 0, name absent)
SCAN 0x80002a94..0x80002abc      ── update path (EnvDefSpec3, loop + strcmp)
  hit  → UPDATE 0x80002ac0..0x80002ae8 → EPILOGUE      (name found)
  miss → CAP-CHECK 0x80002b14: beq cap,count → GROW      (name absent)
APPEND 0x80002b1c..0x80002b8c     ── strlen ≫ malloc ≫ (NULL guard) ≫ memcpy ≫ store
  b20 jal strlen  ;  b2c jal malloc  ;  b34 beqz a0 → OOM  ;  b40 jal memcpy
  b44..b88 store copy into names[count]/vals[count], count++      → EPILOGUE
GROW 0x80002b90..0x80002bcc       ── cap' ≫ realloc(names) ≫ realloc(vals) → APPEND head
  ba0 jal realloc(names,cap'*8)  ;  bbc jal realloc(vals,cap'*24)  ;  bcc → 0xb1c
EPILOGUE 0x80002aec..0x80002b10  ── restore 7 spills, sp+=64, ret
```

## What is PROVED vs a NAMED BRIDGE

| Segment | Status |
|---------|--------|
| prologue 0x80002a5c→0x80002a90 | PROVED (`env_define_prologue`) |
| scan loop + update block | statement + all ingredients (`EnvDefSpec3`); loop body a documented obligation |
| **strlen call splice** | PROVED HERE (`envDefStrlenSplice`) over `strlen_spec` |
| **malloc call splice** | PROVED HERE (`envDefMallocSplice`) over `MallocContract.spec` |
| **memcpy call splice** | PROVED HERE (`envDefMemcpySplice`) over `memcpy_spec` |
| **realloc(names) splice** | PROVED HERE (`envDefReallocNamesSplice`) over `ReallocOps.grow` |
| **realloc(vals) splice** | PROVED HERE (`envDefReallocValsSplice`) over `ReallocOps.grow` |
| **append path composed** | PROVED HERE (`envDefAppendContract`) |
| **grow path composed** | PROVED HERE (`envDefGrowContract`) |
| machine bridges (`*Pre`/`*Stage`/`*Suf`) | NAMED HYPOTHESES (Shape-A residuals) |

The residual per splice is exactly the three concrete straight-line machine
bridges the arm still needs (mirroring `divValueTail`'s `pre`/`stage`/`suf`):
the prefix landing the callee entry, the inter-call staging, and the return
suffix.  Each is a `#derive_case` segment over pinned bytes — no reflection is
performed here, so the whole file elaborates in constant time and is axiom-clean.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Alloc
open Vsa.Sim.Code (Env_defineLoaded)

namespace Vsa.Sim

/-! ## The CARRIED FRAME — assertion-carried framing across the callee seams

The structural gap diagnosed in `experiments/envdefine-composition.md` (last
ledger section) is this: the seam predicate between two callees was the BARE
downstream-callee post (`strlen_post`, malloc-post), which discards the
caller-saved context (`sp`/`gp`/ABI callee-saveds/`AInv`) that the NEXT callee's
entry requires.  So `bridgeMallocPre`/`bridgeMemcpyPre` were unprovable as
stated — there was nowhere for the malloc-entry `sp`/`gp`/`AInv` facts to come
from.

The fix is the house pattern (`BlockLogic.negProloguePost`, `BinOpValueTails`,
`ReallocPost`): **assertion-carried framing** — the seam is
`calleePost ∧ <carried frame>`, where the frame is precisely the ABI/heap
context the downstream entry needs, and it is threaded THROUGH each callee by a
frame-preservation clause the callee's own contract supplies.  A generic
`Triple.frame` would be unsound (`BlockLogic.lean:78`); the frame is instead
carried as an explicit conjunct proved by the segment that spans it.

`EnvDefFrame` is that carried context: the ABI callee-saveds tie (`gm`), `sp` +
`StackOK`, `gp`, and the allocator invariant `AInv` over the live extents — i.e.
the malloc/realloc-entry frame minus the argument-specific pins (PC/x10/x1/mem),
which each prefix supplies. -/

/-- **The carried caller-frame** threaded across the append/grow callee seams:
the ABI callee-saved register tie (`gm`), the stack pointer + `StackOK`, the
global pointer, and the allocator invariant over the live extents.  This is
exactly the sub-state the downstream malloc/realloc entry predicate needs beyond
the argument pins — conjoined to each callee seam so it survives the call. -/
def EnvDefFrame (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (sp : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (c : Config) : Prop :=
  c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
  c.σ.regs.get? Register.x3 = some gpv ∧
  (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
  AInv c.σ exts ∧ c.tick < 2

/-! ## Single-call splices — each `prefix ≫ callee ≫ suffix` over one real contract

Each splice is `callSeg pre callee suf` (`DeriveCallSeg.lean`): the caller prefix
lands the callee's entry predicate, the real callee contract runs, the caller
suffix consumes the callee's exit.  The two `Triple.seq`s are the whole content of
the Shape-D algebra; the callee is threaded, never re-proved. -/

/-- **`strlen` call splice** (`0x80002b1c mv a0,s2 ; 0x80002b20 jal strlen`).
Prefix marshals `name` into `a0` and lands `strlen_pre`; `strlen_spec` runs;
suffix consumes `strlen_post` (`a0 = len`) to `Q`.

**FRAME-CARRYING form.**  `strlen_post` carries only PC/x10/x1/mem — it drops
`sp`/`gp`/ABI/`AInv`.  strlen physically preserves those (it is a leaf reader:
no stores, callee-saveds honoured), but that preservation is NOT in
`strlen_post`'s stated conclusion — it is the exact **missing preservation
clause** the ledger flagged.  Rather than silently assume it (unsound) or weaken
the seam (dishonest), we thread the carried frame through strlen as the EXPLICIT
named premise `strlenFramed : Triple (strlen_pre ∧ F) (strlen_post ∧ F)`.  This
makes the missing clause a visible, auditable hypothesis; the downstream
`bridgeMallocPre` then draws its `sp`/`gp`/`AInv` facts from `F`, not from thin
air.  See the frame-preservation residual note in the ledger. -/
theorem envDefStrlenSplice {P Q F : Config → Prop}
    (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (strlenFramed : Triple (fun c => strlen_pre p r s m0 c ∧ F c)
      (fun c => strlen_post r s m0 c ∧ F c))
    (pre : Triple P (fun c => strlen_pre p r s m0 c ∧ F c))
    (suf : Triple (fun c => strlen_post r s m0 c ∧ F c) Q) :
    Triple P Q :=
  callSeg pre strlenFramed suf

/-- **`malloc` call splice** (`0x80002b28 mv a0,s0 ; 0x80002b2c jal malloc`).
Prefix marshals `len+1` into `a0` and lands `MallocContract.spec`'s entry
predicate; the allocator contract runs; suffix consumes its post (fresh block or
NULL) to `Q`.  The `MallocContract` (= the plan's `MallocSpec`) is a hypothesis,
never an axiom. -/
theorem envDefMallocSplice {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {P Q : Config → Prop}
    (M : MallocContract A SL gpv headroom maxReq)
    (g : (R : Register) → Option (RegisterType R))
    (exts : List (Nat × Nat)) (n : Nat) (sp r : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hn : n ≤ maxReq)
    (pre : Triple P
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 n) ∧
        c.σ.regs.get? Register.x1 = some r ∧ r.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some sp ∧ StackOK SL sp headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        M.AInv c.σ exts ∧ c.σ.mem = m0))
    (suf : Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some r ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g R) ∧
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p n ∧
           (∀ e ∈ exts, ExtDisjoint (p, n) e) ∧
           M.AInv c.σ ((p, n) :: exts))) ∧
        (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < sp.toNat) →
          c.σ.mem[a]? = m0[a]?))
      Q) :
    Triple P Q :=
  callSeg pre (M.spec g exts n sp r m0 hn) suf

/-- **`memcpy` call splice** (`0x80002b40 jal memcpy`, `memcpy(copy, name, len+1)`).
Prefix marshals `dst/src/n` and lands `memcpy_spec`'s `PreDispatch`; `memcpy_spec`
runs (byte or word path per `hroute`); suffix consumes its post to `Q`. -/
theorem envDefMemcpySplice {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (n : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halign : r.toNat % 4 = 0)
    (hroute : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ n < 8 ∨
      (dst.toNat % 8 = 0 ∧ 8 * (n / 8) ≤ 64))
    (pre : Triple P (PreDispatch g r dst src n m0 bs))
    (suf : Triple (fun c => ∃ g', memcpy_bytepath_post g' r dst n m0 bs c) Q) :
    Triple P Q :=
  callSeg pre (memcpy_spec g r dst src n m0 bs halign hroute) suf

/-! ## `realloc` splices — over `ReallocOps.grow` (both grow-path calls) -/

/-- **`realloc(names)` call splice** (`0x80002b9c mv a0,s6 ; 0x80002ba0 jal realloc`,
`realloc(names, newcap*8)`).  Prefix marshals `pOld/nNew` and lands `ReallocPre`;
`ReallocOps.grow` runs (grow always: `nNew = newcap*8 > cap*8 = nOld`); suffix
consumes `ReallocPost ∧ ReallocGrowResult` to `Q`.  `ReallocOps` is a hypothesis. -/
theorem envDefReallocNamesSplice {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {AInv : MState → List Extent → Prop}
    {privFoot : Nat → Prop} {P Q : Config → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew : Nat) (sp r : BitVec 64)
    (m0 : Vsa.MemRepr.Mem)
    (hle : nNew ≤ maxReq) (hlt : nOld < nNew) (hp : pOld ≠ 0) (hmem : (pOld, nOld) ∈ exts)
    (pre : Triple P (ReallocPre SL gpv headroom AInv exts pOld nNew sp r m0 g))
    (suf : Triple
      (fun c => ReallocPost gpv sp r g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) Q) :
    Triple P Q :=
  callSeg pre (RO.grow g exts pOld nOld nNew sp r m0 hle hlt hp hmem) suf

/-- **`realloc(vals)` call splice** (`0x80002bbc jal realloc`, `realloc(vals,
newcap*24)`).  Same shape as the names splice with the vals base/stride. -/
theorem envDefReallocValsSplice {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} {AInv : MState → List Extent → Prop}
    {privFoot : Nat → Prop} {P Q : Config → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (g : (R : Register) → Option (RegisterType R))
    (exts : List Extent) (pOld nOld nNew : Nat) (sp r : BitVec 64)
    (m0 : Vsa.MemRepr.Mem)
    (hle : nNew ≤ maxReq) (hlt : nOld < nNew) (hp : pOld ≠ 0) (hmem : (pOld, nOld) ∈ exts)
    (pre : Triple P (ReallocPre SL gpv headroom AInv exts pOld nNew sp r m0 g))
    (suf : Triple
      (fun c => ReallocPost gpv sp r g c ∧
        ReallocGrowResult A SL privFoot AInv exts pOld nOld nNew sp m0 c.σ) Q) :
    Triple P Q :=
  callSeg pre (RO.grow g exts pOld nOld nNew sp r m0 hle hlt hp hmem) suf

/-! ## The APPEND path composed — `strlen ≫ malloc ≫ memcpy ≫ store`

The append path (`0x80002b1c..0x80002b8c`, name absent, `count < cap`) is three
call splices in series plus a straight-line store block.  It is one
`callSeg`-chain over `strlen_spec`, `MallocContract.spec`, `memcpy_spec`, with
the inter-call staging blocks (`mv`/`addi`/`beqz` arg marshalling) and the final
store block (`0x80002b44..0x80002b88`: 3×`sd` into `vals[count]`, `sd` into
`names[count]`, `sw count+1`) as named machine bridges.

`Astrlen`/`Amalloc`/`Amemcpy` are the callee-entry seam predicates (the three
`*_pre`); `Bafter*` are the callee-exit seam predicates (the three `*_post`).
The whole append path reduces to: land `Astrlen` from `P` (prologue/scan exit),
thread the three callees, marshal each `*_post` to the next `*_pre`, then run the
store block to `Q`.  Exactly `divValueTail` scaled to three calls. -/
theorem envDefAppendContract
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {P Q : Config → Prop}
    (M : MallocContract A SL gpv headroom maxReq)
    (gm : (R : Register) → Option (RegisterType R))
    -- strlen call data
    (namePtr rStrlen : BitVec 64) (nameStr : String)
    (m0 : Std.ExtHashMap Nat (BitVec 8))
    -- malloc call data
    (exts : List (Nat × Nat)) (nMalloc : Nat) (spM rM : BitVec 64)
    (mMalloc : Std.ExtHashMap Nat (BitVec 8)) (hnM : nMalloc ≤ maxReq)
    -- memcpy call data
    (gc : (R : Register) → Option (RegisterType R))
    (rMemcpy dst src : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (halignC : rMemcpy.toNat % 4 = 0)
    (hrouteC : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ nMemcpy < 8 ∨
      (dst.toNat % 8 = 0 ∧ 8 * (nMemcpy / 8) ≤ 64))
    -- strlen preserves the carried frame (its missing preservation clause, named).
    -- The carried frame is `EnvDefFrame … spM gm` (the malloc-entry frame minus arg
    -- pins); on the strlen seam memory is still `m0` (strlen does not store).
    (strlenFramed : Triple
      (fun c => strlen_pre namePtr rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c => strlen_post rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    -- the four machine bridges — now FRAME-CARRYING
    (bridgeStrlenPre : Triple P
      (fun c => strlen_pre namePtr rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c))
    (bridgeMallocPre : Triple
      (fun c => strlen_post rStrlen nameStr m0 c ∧
        EnvDefFrame SL gpv headroom M.AInv exts spM gm c)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 nMalloc) ∧
        c.σ.regs.get? Register.x1 = some rM ∧ rM.toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some spM ∧ StackOK SL spM headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        M.AInv c.σ exts ∧ c.σ.mem = mMalloc))
    (bridgeMemcpyPre : Triple
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some rM ∧
        c.σ.regs.get? Register.x2 = some spM ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ exts) ∨
         (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
           p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p nMalloc ∧
           (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧
           M.AInv c.σ ((p, nMalloc) :: exts))) ∧
        (∀ a, ¬ M.privFoot a → ¬ (SL.lo ≤ a ∧ a < spM.toNat) →
          c.σ.mem[a]? = mMalloc[a]?))
      (PreDispatch gc rMemcpy dst src nMemcpy mMemcpy bs))
    (bridgeStore : Triple
      (fun c => ∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) Q) :
    Triple P Q :=
  -- strlen ≫ [malloc ≫ [memcpy ≫ store]]
  envDefStrlenSplice namePtr rStrlen nameStr m0 strlenFramed bridgeStrlenPre
    (envDefMallocSplice M gm exts nMalloc spM rM mMalloc hnM bridgeMallocPre
      (envDefMemcpySplice gc rMemcpy dst src nMemcpy mMemcpy bs halignC hrouteC
        bridgeMemcpyPre bridgeStore))

/-! ## The GROW path composed — `cap' ≫ realloc(names) ≫ realloc(vals) ≫ append-head`

The grow path (`0x80002b90..0x80002bcc`, `count == cap`) computes the new capacity
(`cap' = 2*cap`, or `8` from CAP-INIT), stores it, then calls `realloc` twice.  It
is two `ReallocOps.grow` splices in series plus the cap-compute prefix and the
inter-call reload/store staging, ending by falling into the APPEND head (`0xb1c`).

The two-successful-grow arena re-establishment (`realloc_grow2_arena`, `Grow2Exts`)
and the two-frame public-memory composition (`heapPublicFrame_trans`) — both landed
in `EnvDefineClose` — are what the grow BLOCK's post consumes; here they are the
suffix bridge's obligation, so the composition stays pure `callSeg` algebra. -/
theorem envDefGrowContract
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    {AInv : MState → List Extent → Prop} {privFoot : Nat → Prop}
    {P Q : Config → Prop}
    (RO : ReallocOps A SL gpv headroom maxReq AInv privFoot)
    (gN gV : (R : Register) → Option (RegisterType R))
    -- realloc(names): grow (namesOld, cap*8) → newcap*8
    (extsN : List Extent) (pNamesOld nNamesOld nNamesNew : Nat) (spN rN : BitVec 64)
    (mN : Vsa.MemRepr.Mem)
    (hleN : nNamesNew ≤ maxReq) (hltN : nNamesOld < nNamesNew)
    (hpN : pNamesOld ≠ 0) (hmemN : (pNamesOld, nNamesOld) ∈ extsN)
    -- realloc(vals): grow (valsOld, cap*24) → newcap*24, over the post-names ledger
    (extsV : List Extent) (pValsOld nValsOld nValsNew : Nat) (spV rV : BitVec 64)
    (mV : Vsa.MemRepr.Mem)
    (hleV : nValsNew ≤ maxReq) (hltV : nValsOld < nValsNew)
    (hpV : pValsOld ≠ 0) (hmemV : (pValsOld, nValsOld) ∈ extsV)
    -- the three machine bridges
    (bridgeCapCompute : Triple P
      (ReallocPre SL gpv headroom AInv extsN pNamesOld nNamesNew spN rN mN gN))
    (bridgeNamesToVals : Triple
      (fun c => ReallocPost gpv spN rN gN c ∧
        ReallocGrowResult A SL privFoot AInv extsN pNamesOld nNamesOld nNamesNew spN mN c.σ)
      (ReallocPre SL gpv headroom AInv extsV pValsOld nValsNew spV rV mV gV))
    (bridgeAppendHead : Triple
      (fun c => ReallocPost gpv spV rV gV c ∧
        ReallocGrowResult A SL privFoot AInv extsV pValsOld nValsOld nValsNew spV mV c.σ)
      Q) :
    Triple P Q :=
  -- realloc(names) ≫ [realloc(vals) ≫ append-head]
  envDefReallocNamesSplice RO gN extsN pNamesOld nNamesOld nNamesNew spN rN mN
    hleN hltN hpN hmemN bridgeCapCompute
    (envDefReallocValsSplice RO gV extsV pValsOld nValsOld nValsNew spV rV mV
      hleV hltV hpV hmemV bridgeNamesToVals bridgeAppendHead)

/-! ## The top-level `env_define` contract interface

`env_define_pre`/`env_define_post` are the interface the consumers
(`Call.closure`/`varDecl`/`assign`) require: a `Triple` from the entry `0x80002a5c`
with the ABI args (`env`/`name`/`&v`) to the return `ret` with the `Env` at `env`
now representing `Store.define f nameStr v`.  We reuse the established
`env_define_update_pre`/`env_define_update_post` shape (`EnvDefSpec3`) as the
canonical interface — the update-path pre/post already IS this shape (the post's
`FrameRepr` is the `Store.define` result for any path: update, append, or grow).

The full contract dispatches on the runtime path (name found → update; absent,
`count < cap` → append; absent, `count == cap` → grow).  `envDefContract` states
it, composed from the prologue (proved) ≫ the path taken, with each path's
composed contract (`envDefAppendContract`/`envDefGrowContract` above, or the
update-path Triple) supplied as a per-path segment.  Because the three paths land
the SAME `env_define_update_post`, the dispatch is a `Triple.cond`-style join
(here taken as the three per-path segment hypotheses reaching a common `Q`). -/

/-- **The composed `env_define` contract (dispatch skeleton).**  Given the three
per-path composed segments — update (`hUpdate`), append (`hAppend`), grow
(`hGrow`), each a `Triple` from its own path-entry predicate to the common
post `Q` — and a `dispatch` prefix landing whichever path-entry the runtime
takes, `env_define` reaches `Q`.  The path-entry predicates `Pup`/`Pap`/`Pgr`
are the three runtime cases; `dispatch` is the prologue+scan choosing among them.

This is the top-level Shape-D join: the hard call-composition is discharged
inside `hAppend`/`hGrow` (built from the `*Contract` theorems above over the real
`MallocContract`/`ReallocOps`/`strlen`/`memcpy` contracts); the remaining residual
is `dispatch` (prologue+scan, largely proved: `env_define_prologue` + the
`EnvDefSpec3` loop) and the per-path machine bridges inside each segment. -/
theorem envDefContract {P Pup Pap Pgr Q : Config → Prop}
    (dispatch : Triple P (fun c => Pup c ∨ Pap c ∨ Pgr c))
    (hUpdate : Triple Pup Q) (hAppend : Triple Pap Q) (hGrow : Triple Pgr Q) :
    Triple P Q := by
  refine Triple.seq dispatch ?_
  intro c hc
  rcases hc with h | h | h
  · exact hUpdate c h
  · exact hAppend c h
  · exact hGrow c h

#print axioms envDefStrlenSplice
#print axioms envDefMallocSplice
#print axioms envDefMemcpySplice
#print axioms envDefReallocNamesSplice
#print axioms envDefReallocValsSplice
#print axioms envDefAppendContract
#print axioms envDefGrowContract
#print axioms envDefContract

end Vsa.Sim
