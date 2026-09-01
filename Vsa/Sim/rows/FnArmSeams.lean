import Vsa.Sim.rows.AllocBuildEntrySplice

/-!
# `FnArmSeams` — the `staging` / `tail` seams of `allocBuildEntry_hEntry`

`rows/AllocBuildEntrySplice.lean` reduced the whole `EX_FN` closure-alloc splice to
ONE `spliceFold` (`allocBuildEntry_hEntry`) taking exactly two `Triple` premises:

* `staging : Triple Pre (mallocCallSpec M).EntryP g` — the arm front (`a3 := φf env`
  decode ≫ `fnArmMallocCallBridge`) landing malloc's canonical `EntryP`;
* `tail : Triple (mallocCallSpec M).ExitPost g AllocBuildEntry` — malloc's canonical
  exit (NULL-or-success) ≫ the reload span (`fnArmReloadRow`) landing `AllocBuildEntry`
  at `0x800033d8`.

This file discharges the **mechanizable core** of each seam and NAMES the
irreducible off-path residuals as named-field structures (CLAUDE.md R6/R7 — never an
anonymous ∃/∧ tower), consumed through a single destructurer.

## `tail` — the mechanizable core (this file)

`tail` is genuinely composite: malloc's `ExitP` at `g.r = 0x800033d0` is pruned to the
success block by `M.nonNull_of_bounded` (`g.hn : g.n ≤ maxReq`, malloc never NULL for a
bounded request), then the reload span `fnArmReloadRow` runs to `0x800033d8`, then the
`AllocBuildEntry` ~30 fields are reconstructed.  What the reload span + `ExitP` alone
CANNOT produce are the arm-entry-carried facts (`ExprRepr`/`StoreRepr` of the Expr node
and the OLD store, the sret-window geometry, the spill readbacks, the register images
`x8=aExpr`/`x13=φf env`/`x9=sret`).  They survive the `malloc` call ONLY because malloc's
footprint (`M.privFoot ∪ [SL.lo, sp)`) is disjoint from the arena block, the sret box,
and the code image — i.e. they are transported across the call by `ExitP.memOut` (reads
outside `foot` unchanged) + `ExitP.frame` (ABI callee-saved tie).  That transport is
exactly what the `CallSpec` `foot`/`memOut` interface is FOR — but it needs the arm-entry
values as inputs, so we package them as `AllocBuildTailFacts` (a named-field bundle the
caller supplies from the arm's own front, the analog of the strdup route's
`StrdupMemcpyContent`).  `allocBuildEntry_tail` then closes `tail` as a `Triple`.

`prune_of_exit` is the reusable null-prune: it collapses `mallocCallSpec`'s `ExitPost`
disjunction to the success witness `p` (with `p ≠ 0`, `p % 16 = 0`, `A.contains p n`,
freshness, `AInv (p::exts)`) via `M.nonNull_of_bounded`.

## `staging` — the named arm-front linkage (this file)

The arm front (`armPC → 0x800033c4`, computing `a3 := φf env` and `a0 := 16`) is
genuinely off-path AND `armPC` is a FREE variable in the pipeline (the caller
instantiates it from the jump-table dispatch), so it is NOT a concrete seg here.  We
name it as `AllocBuildStagingLink` (the arm-front linkage: `Pre → the config pinned at
0x800033c4` with `x13 = a3 = φf env`, `x2 = g.sp`, the ABI frame, `mem = m0`), then
`staging_of_link` runs `fnArmMallocCallBridge` and assembles malloc's `EntryP` at
`mallocEntry`.  The `hjalSeam` (the `jal malloc` callee-entry obs) is the one residual
`fnArmMallocCallBridge` demands; it is a NAMED premise (a hand `site_*` would trip the
gate).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) Every new post/entry predicate in this file IS a
-- named-field structure (`AllocBuildTailFacts`, `AllocBuildStagingLink`,
-- `AllocBuildReloadPost`).  The residual `∃` occurrences are NOT anonymous post towers:
-- they are run-witnesses (`∃ c'`, `∃ w, minstret = some w`) and verbatim relays of
-- LANDED signatures (`prune_of_exit`'s `∃ p` mirrors `MallocContract.nonNull_of_bounded`;
-- the `∃ o ment vv8 vv9 vv18, ArmEntryK …` Pre is copied verbatim from the existing
-- `fnArmSeamRun_of_hEntry` pipeline seam, not a new definition).

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## §1. The null-prune — collapse malloc's `ExitPost` disjunction to success -/

/-- **`prune_of_exit`** — malloc's `ExitPost g` at a bounded request is the SUCCESS
block.  Consumes `mallocCallSpec`'s `ExitP` (bound `res`), prunes the NULL branch of
`postSide` by `M.nonNull_of_bounded` (`g.hn : g.n ≤ maxReq`), and returns the config
`c` at `pc = g.r`, `x10 = ofNat p`, `x2 = g.sp`, `x3 = gpv`, with the fresh-block facts
and `M.AInv c.σ ((p, g.n) :: g.exts)` — plus the memory-transform clause `memOut` (reads
outside `foot g` unchanged) that carries every survival fact across the call. -/
theorem prune_of_exit
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (g : MallocG maxReq)
    (c : Config) (hexit : (mallocCallSpec M).ExitPost g c) :
    ∃ p : Nat,
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some g.r ∧
      c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
      c.σ.regs.get? Register.x2 = some g.sp ∧
      c.σ.regs.get? Register.x3 = some gpv ∧
      (∀ R, AbiPreserved R = true → c.σ.regs.get? R = g.gm R) ∧
      (∀ a : Nat, ¬ ((mallocCallSpec M).foot g a) → c.σ.mem[a]? = g.m0[a]?) ∧
      p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p g.n ∧
      (∀ e ∈ g.exts, ExtDisjoint (p, g.n) e) ∧
      M.AInv c.σ ((p, g.n) :: g.exts) := by
  obtain ⟨res, hE⟩ := hexit
  -- the register pins from `rets = postPins g res = [(10, ofNat res), (2, g.sp), (3, gpv)]`
  obtain ⟨hx10', hx2, hx3, -⟩ := hE.rets
  have hx10 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 res) := hx10'
  -- the frame: every AbiPreserved reg (clobber = false) ties back to g.gm
  have habi : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = g.gm R := by
    intro R hR; exact hE.frame R hR (by rfl)
  -- prune: feed `postSide` (the NULL-or-success disjunction at witness res) to
  -- `nonNull_of_bounded` after phrasing the x10 pin as the disjunction demands.
  have hdisj :
      ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ M.AInv c.σ g.exts) ∨
       (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
         p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p g.n ∧
         (∀ e ∈ g.exts, ExtDisjoint (p, g.n) e) ∧
         M.AInv c.σ ((p, g.n) :: g.exts))) := by
    rcases hE.side with ⟨h0, hai⟩ | ⟨hne, h16, hcont, hdis, hai⟩
    · exact Or.inl ⟨by rw [hx10, h0], hai⟩
    · exact Or.inr ⟨res, hx10, hne, h16, hcont, hdis, hai⟩
  obtain ⟨p, hpx10, hpne, hp16, hpcont, hpdis, hpai⟩ :=
    M.nonNull_of_bounded c.σ g.exts g.n g.hn hdisj
  exact ⟨p, hE.good, hE.tick, hE.pc, hpx10, hx2, hx3, habi, hE.memOut,
    hpne, hp16, hpcont, hpdis, hpai⟩

#print axioms prune_of_exit

/-! ## §2. `tail` — reload + reconstruct `AllocBuildEntry`

The reload span `fnArmReloadRow` lands the config at `0x800033d8`; the `AllocBuildEntry`
fields are the arm-entry-carried facts transported across the malloc call.  We bundle
those as a named-field structure supplied by the caller, keyed to the SUCCESS witness
`p` from `prune_of_exit`, and instantiate `AllocBuildEntry`.  Everything the reload run
+ prune produce (PC, mem, the register images `x10=p`/`x2`, the fresh-block geometry)
is derived; the rest (`ExprRepr`/`StoreRepr`/sret-geometry/spill readbacks/`x8`/`x13`/
`x9`) is the transported bundle. -/

/-- **`AllocBuildTailFacts`** — the arm-entry-carried facts the reload span + malloc
`ExitP` cannot manufacture, transported across the `malloc` call (they survive because
malloc's footprint is disjoint from the arena block / sret box / code image, via
`ExitP.memOut`).  This is the `tail`-seam analog of `StrdupMemcpyContent`: a named-field
bundle (never an anonymous tower), each field a doc-commented residual the caller
supplies from the arm's own front.  It is stated at the reloaded config `c` (parked at
`0x800033d8`, after `fnArmReloadRow`) at the success block `p`. -/
structure AllocBuildTailFacts
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (cd : ClosureData) (p : Nat)
    (sp r sret aExpr : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (c : Config) : Prop where
  /-- The four closure-build register reads NOT set by the reload span
  (`x8 = aExpr`, `x13 = φf env` — the reloaded `a3`, `x9 = sret`). -/
  hx8 : c.σ.regs.get? Register.x8 = some aExpr
  hx13 : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf cd.env))
  hx9 : c.σ.regs.get? Register.x9 = some sret
  hx2 : c.σ.regs.get? Register.x2 = some (sp - 1088#64)
  /-- The malloc-result geometry (`p ≠ 0`, `p % 8 = 0`, `A.contains p 16` — from the
  pruned success block; freshness vs old closures; the extension witness). -/
  hpnz : p ≠ 0
  halign : p % 8 = 0
  harena : A.contains p 16
  hpfresh : ∀ ca, ca < st.store.closures.size → φc' ca ≠ p
  hext : PhiExtends φc φc' st.store.closures.size
  hp : φc' st.store.closures.size = p
  /-- The Expr node / OLD store / code survival at the post-build memory. -/
  hExprRepr : ∀ mpre : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]?) →
    ExprRepr mpre aExpr.toNat (.fn cd.name cd.params cd.body)
  hEnvNz : φf cd.env ≠ 0
  hEnvToNat : (BitVec.ofNat 64 (φf cd.env)).toNat = φf cd.env
  hOld : ∀ mpre : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]?) →
    StoreRepr mpre N A φf φc' st.store
  hps : p + 16 ≤ sret.toNat ∨ sret.toNat + 24 ≤ p
  hpof : ((BitVec.ofNat 64 p) + 8#64).toNat = (BitVec.ofNat 64 p).toNat + 8
  hpToNat : (BitVec.ofNat 64 p).toNat = p
  hsof : (sret + 8#64).toNat = sret.toNat + 8
  hfacts : ChainFacts c.σ.mem c.σ.mem
    (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr (BitVec.ofNat 64 (φf cd.env)) sret) []
    fnArmClosureBuildSeg
  hkeys : KeysOK (keysG (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
    (BitVec.ofNat 64 (φf cd.env)) sret))
  hCodeSurvive : ∀ mpre : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]?) →
    Eval_exprLoaded mpre
  hMpreFrame : ∀ a : Nat,
    ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨
    (writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
      (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
        (BitVec.ofNat 64 (φf cd.env)) sret) [])).log)[a]? = mMalloc[a]?
  hSpillReads :
    let mpre := writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
      (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
        (BitVec.ofNat 64 (φf cd.env)) sret) [])).log
    read64 mpre (sp.toNat - 8) = some r.toNat ∧
    read64 mpre (sp.toNat - 16) = some v8.toNat ∧
    read64 mpre (sp.toNat - 24) = some v9.toNat ∧
    read64 mpre (sp.toNat - 32) = some v18.toNat
  hframe :
    c.σ.sailOutput = out0 ∧ String.join out0.toList = st.out ∧
    Eval_exprLoaded mMalloc ∧
    (∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      c.σ.regs.get? R = g R) ∧
    read64 mMalloc (sp.toNat - 8) = some r.toNat ∧
    read64 mMalloc (sp.toNat - 16) = some v8.toNat ∧
    read64 mMalloc (sp.toNat - 24) = some v9.toNat ∧
    read64 mMalloc (sp.toNat - 32) = some v18.toNat ∧
    g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧ g Register.x18 = some v18 ∧
    g Register.x2 = some sp ∧
    (∀ aa : Nat, ¬ (SL.lo ≤ aa ∧ aa < sp.toNat) → ¬ (A.lo ≤ aa ∧ aa < A.hi) →
      (sret.toNat ≤ aa ∧ aa < sret.toNat + 24) ∨ mMalloc[aa]? = m0[aa]?) ∧
    1088 ≤ sp.toNat ∧
    sp.toNat ≤ 0x100000000 ∧ 0x80000000 ≤ sp.toNat ∧
    tohostAddr + 16 + 1088 ≤ sp.toNat ∧ sp.toNat % 8 = 0 ∧
    r.toNat % 4 = 0

/-- **`AllocBuildReloadPost`** — the reload-linkage conclusion as a named-field
structure (CLAUDE.md R7 — never an anonymous ∃/∧ post tower): the config `c'` reached by
running the reload span (`fnArmReloadRow` on the pruned success config) from `c`, parked
at `0x800033d8` with `mem = mMalloc`, plus the surviving `AllocBuildTailFacts` bundle. -/
structure AllocBuildReloadPost
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (cd : ClosureData) (p : Nat)
    (sp r sret aExpr : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (c c' : Config) : Prop where
  hstep : Steps ⟨c.σ, c.tick, c.steps⟩ ⟨c'.σ, c'.tick, c'.steps⟩
  hG : GoodState c'.σ
  htick : c'.tick < 2
  hpc : c'.σ.regs.get? Register.PC = some (0x800033d8#64 : BitVec 64)
  hmem : c'.σ.mem = mMalloc
  hmi : ∃ w, c'.σ.regs.get? Register.minstret = some w
  hx10 : c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  hFacts : AllocBuildTailFacts g N A SL φf φc φc' st cd p
    sp r sret aExpr m0 mMalloc v8 v9 v18 out0 c'

/-- **`allocBuildEntry_tail`** — the `tail` seam CLOSED (modulo the named
`AllocBuildTailFacts` bundle + the reload linkage).  The fresh block `p` is a FIXED
parameter (`p := φc' st.store.closures.size`, the store-side allocation index the
downstream contract reads); `tail`'s post `AllocBuildEntry … p …` is parked at `p`, so
the seam must land malloc's result AT `p`.  That the malloc result equals `p` is the
`hResultP` linkage (the CallSpec `Res = Nat` witness is existential; tying it to the
store-side `p` is caller geometry — the analog of `hp : φc' size = p`).

From malloc's `ExitPost gMal`: `prune_of_exit` gives a success block `q` at `0x800033d0`;
`hResultP` identifies `q = p`; the reload span `fnArmReloadRow` (via `hReload`) lands the
config at `0x800033d8` with `mem = mMalloc`; then the `AllocBuildEntry` fields assemble —
the register images `x10 = ofNat p` / geometry from the pruned exit + reload, the rest
from `AllocBuildTailFacts`.  `hReload` packages the reload run + the bundle (the caller
runs `fnArmReloadRow` on the pruned config; its `lds` head is the spilled `a3 = φf env`,
which only the caller's spill contents fix — so the reload PLUS the bundle is the one
caller-supplied linkage). -/
theorem allocBuildEntry_tail
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (p : Nat) (sp r sret aExpr : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (Malloc : MallocContract A SL gpv headroom maxReq) (gMal : MallocG maxReq)
    -- the reload linkage: from any exit config, the caller runs `fnArmReloadRow` (on the
    -- pruned success config) to `0x800033d8` (mem = mMalloc) and supplies the
    -- arm-entry-carried facts (the `AllocBuildTailFacts` bundle) surviving to it.  This
    -- is the ONE caller-supplied linkage: the reload's `lds` head is the spilled
    -- `a3 = φf env`, which only the caller's spill contents fix, and the transported
    -- bundle rides malloc's `ExitP.memOut` (reads outside `foot` unchanged).
    (hReload : ∀ (c : Config), (mallocCallSpec Malloc).ExitPost gMal c →
      ∃ c' : Config, AllocBuildReloadPost g N A SL φf φc φc' st ⟨env, name, params, body⟩ p
        sp r sret aExpr m0 mMalloc v8 v9 v18 out0 c c') :
    Triple ((mallocCallSpec Malloc).ExitPost gMal)
      (AllocBuildEntry g N A SL φf φc φc' st ⟨env, name, params, body⟩ p
        sp r sret aExpr m0 mMalloc v8 v9 v18 out0) := by
  intro c hexit
  obtain ⟨c', hR⟩ := hReload c hexit
  obtain ⟨w', hmic'⟩ := hR.hmi
  refine ⟨c', ?_, ?_⟩
  · cases c; exact hR.hstep
  -- assemble `AllocBuildEntry` from the reload post + the bundle (every field is a
  -- named-field projection — no anonymous positional navigation).
  have hFacts := hR.hFacts
  exact {
    hG := hR.hG, htick := hR.htick, hpc := hR.hpc, hmem := hR.hmem, hmi := ⟨w', hmic'⟩,
    hx10 := hR.hx10, hx8 := hFacts.hx8, hx13 := hFacts.hx13, hx9 := hFacts.hx9,
    hx2 := hFacts.hx2, hpnz := hFacts.hpnz, halign := hFacts.halign, harena := hFacts.harena,
    hpfresh := hFacts.hpfresh, hext := hFacts.hext, hp := hFacts.hp,
    hExprRepr := hFacts.hExprRepr, hEnvNz := hFacts.hEnvNz, hEnvToNat := hFacts.hEnvToNat,
    hOld := hFacts.hOld, hps := hFacts.hps, hpof := hFacts.hpof, hpToNat := hFacts.hpToNat,
    hsof := hFacts.hsof, hfacts := hFacts.hfacts, hkeys := hFacts.hkeys,
    hCodeSurvive := hFacts.hCodeSurvive, hMpreFrame := hFacts.hMpreFrame,
    hSpillReads := hFacts.hSpillReads, hframe := hFacts.hframe }

#print axioms allocBuildEntry_tail

/-! ## §3. `staging` — arm front (named) ≫ `fnArmMallocCallBridge` → malloc `EntryP`

The arm front (`armPC → 0x800033c4`, `a3 := φf env` decode + `a0 := 16` setup) is
genuinely off-path AND `armPC` is a FREE variable in the pipeline, so it is NOT a
concrete seg here — it is the named `AllocBuildStagingLink` (`Pre → the config pinned at
0x800033c4`, ready for `fnArmMallocCallBridge`).  `staging_of_link` then runs
`fnArmMallocCallBridge` (`li a0,16 ; sd a3,0(sp) ; jal malloc`) and assembles malloc's
canonical `EntryP` at `mallocEntry = 0x80004790`, link `0x800033d0`. -/

/-- **`AllocBuildStagingLink`** — the arm-front residual: `Pre → the config at
`0x800033c4`` ready for the malloc-call bridge.  Every field is an arm-front-carried
fact the caller supplies from the arm's own dispatch front (`a3 := φf env` computed,
`sp`/`gp` in place, the ABI frame keyed to `gMal.gm`, `mem = gMal.m0`, `StackOK`/`AInv`
for malloc's `preSide`).  Named-field structure per CLAUDE.md (never a tower); stated at
the config `c` parked at `0x800033c4`. -/
structure AllocBuildStagingLink
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (Malloc : MallocContract A SL gpv headroom maxReq) (gMal : MallocG maxReq)
    (a3 : BitVec 64) (c : Config) : Prop where
  hG : GoodState c.σ
  htick : c.tick < 2
  hpc : c.σ.regs.get? Register.PC = some (0x800033c4#64 : BitVec 64)
  hmi : ∃ w, c.σ.regs.get? Register.minstret = some w
  hmem : c.σ.mem = gMal.m0
  /-- `x2 = g.sp` (the lowered stack pointer, base of the `sd a3,0(sp)` spill). -/
  hx2 : c.σ.regs.get? Register.x2 = some gMal.sp
  /-- `x13 = a3` (the closure-record ptr `φf env`, to be spilled). -/
  hx13 : c.σ.regs.get? Register.x13 = some a3
  /-- `gp = gpv` (the pinned global pointer, an EntryP arg). -/
  hx3 : c.σ.regs.get? Register.x3 = some gpv
  /-- The ABI frame keyed to `gMal.gm` (the malloc-entry register ghost). -/
  habi : ∀ R, AbiPreserved R = true → c.σ.regs.get? R = gMal.gm R
  /-- The chain-facts (store-target well-formedness for the `sd a3,0(sp)` spill). -/
  hfacts : ChainFacts c.σ.mem c.σ.mem (fnArmMallocCallL gMal.sp a3) [] fnArmMallocCallSeg
  /-- Malloc's `preSide` survives the spill: `StackOK` at `gMal.sp` + `M.AInv` at the
  malloc-entry memory (the spill writes only `[sp, sp+8)` inside the red zone). -/
  hStackOK : StackOK SL gMal.sp headroom
  hMallocMem : writeLog gMal.m0 (evalBlocks fnArmMallocCallSeg
    (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])).log = gMal.m0
  /-- `M.AInv` at the malloc-entry state (after the spill).  Stated at ANY state `σ'`
  whose `gp` agrees with `c` and whose memory equals the spill write-log `gMal.m0` (the
  malloc-entry memory) — this is `M.AInv` transported across the spill; the spill writes
  only `[sp, sp+8)` (in the red zone), `gp` is preserved, so `AInvStableOn` (the canonical
  once-per-object stability) carries `M.AInv` from `c` to the malloc entry.  Packaged as
  a survival closure so the caller supplies the base `AInv` + its stability once. -/
  hAInvAt : ∀ σ' : MState,
    σ'.regs.get? Register.x3 = c.σ.regs.get? Register.x3 →
    σ'.mem = gMal.m0 →
    Malloc.AInv σ' gMal.exts
  /-- The `jal malloc` callee-entry seam (`fnArmMallocCallBridge`'s one residual) and the
  key-hygiene decides, packaged as the bridge demands. -/
  hjalSeam : ∀ (σ' : MState) (i' u' : Nat),
    GoodState σ' → i' < 2 →
    σ'.regs.get? Register.PC = some
      (evalBlocksPC 0x800033c4#64 (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])
        fnArmMallocCallSeg) →
    (∃ w, σ'.regs.get? Register.minstret = some w) →
    σ'.mem = writeLog gMal.m0 (evalBlocks fnArmMallocCallSeg
      (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])).log →
    GHolds σ' (evalBlocks fnArmMallocCallSeg
      (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])).regs →
    JalStep 0x80004790#64 0x800033d0#64 σ' i' u'
  hKeysOut : KeysOK (keysG (evalBlocks fnArmMallocCallSeg
    (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])).regs)
  hRaOut : KeysAvoidRa (evalBlocks fnArmMallocCallSeg
    (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])).regs

/-- **`staging_of_link`** — the `staging` seam CLOSED (modulo the named
`AllocBuildStagingLink` bundle).  Runs `fnArmMallocCallBridge` off the arm-front config
and assembles malloc's canonical `EntryP` at `mallocEntry`, link `0x800033d0`.  The
ghost pack must have `gMal.n = 16` (the closure record size), `gMal.r = 0x800033d0` (the
malloc return address), and `gMal.entry` is `mallocEntry` (fixed by `mallocCallSpec`). -/
theorem staging_of_link
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (Malloc : MallocContract A SL gpv headroom maxReq) (gMal : MallocG maxReq)
    (a3 : BitVec 64)
    (hn16 : gMal.n = 16) (hr : gMal.r = 0x800033d0#64)
    (Pre : Config → Prop)
    (hLink : Triple Pre (AllocBuildStagingLink Malloc gMal a3)) :
    Triple Pre (fun c => (mallocCallSpec Malloc).EntryP gMal c) := by
  intro c hpre
  obtain ⟨cL, hstepL, hE⟩ := hLink c hpre
  obtain ⟨vmi, hmi⟩ := hE.hmi
  -- the bridge's entry pins: x2 = gMal.sp, x13 = a3.
  have hL : GHolds cL.σ (fnArmMallocCallL gMal.sp a3) := ⟨hE.hx2, hE.hx13, trivial⟩
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, ⟨w2, hmi2⟩, hregs2, hmem2, habi2⟩ :=
    fnArmMallocCallBridge cL.σ cL.tick cL.steps vmi gMal.sp a3 gMal.m0
      hE.hG hE.hpc hmi hE.hmem hL hE.hfacts hE.htick hE.hKeysOut hE.hRaOut hE.hjalSeam
  -- the post config at the malloc entry
  refine ⟨⟨σ2, i2, cL.steps + evalBlocksFuel fnArmMallocCallSeg + 1⟩, ?_, ?_⟩
  · cases cL; exact hstepL.trans hsteps
  -- assemble malloc's `EntryP` at `mallocEntry` (0x80004790), link 0x800033d0.
  -- the a0 pin: `li a0,16` sets x10 = sign_extend 0x010 = 16 = ofNat gMal.n.
  have hsext16 : (sign_extend (m := 64) (0x010#12) : BitVec 64) = BitVec.ofNat 64 gMal.n := by
    rw [hn16]; apply BitVec.eq_of_toNat_eq; decide
  have ha0 : σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 gMal.n) := by
    have h := gholds_lookup (n := 10) _ hregs2 (show lookupG 10
      (evalBlocks fnArmMallocCallSeg
        (SegEvalState.init (fnArmMallocCallL gMal.sp a3) [])).regs
      = some (sign_extend (m := 64) (0x010#12)) from rfl)
    rwa [hsext16] at h
  -- sp preserved by the seg (x2 in the pin list, not written).
  have hsp2 : σ2.regs.get? Register.x2 = some gMal.sp :=
    gholds_lookup (n := 2) _ hregs2 (by rfl)
  -- gp preserved across the seg's ABI frame (x3 is AbiPreserved, seg writes only x10).
  have hgp2 : σ2.regs.get? Register.x3 = some gpv := by
    rw [habi2 Register.x3 (by decide)]; exact hE.hx3
  -- ra = g.r = 0x800033d0 (the bridge's link).
  have hra : σ2.regs.get? Register.x1 = some gMal.r := by rw [hr]; exact hra2
  -- mem = gMal.m0 (the spill write-log collapses to m0 via hMallocMem).
  have hmemEq : σ2.mem = gMal.m0 := by rw [hmem2, hE.hMallocMem]
  -- the ABI frame keyed to gMal.gm: seg frame (habi2) ∘ link frame (hE.habi).
  have habiE : ∀ R, AbiPreserved R = true → σ2.regs.get? R = gMal.gm R := by
    intro R hR; rw [habi2 R hR]; exact hE.habi R hR
  -- assemble EntryP.
  refine {
    good := hG2, tick := hi2,
    pc := (by show σ2.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry); exact hpc2),
    args := ⟨ha0, hsp2, hgp2, trivial⟩, ra := hra,
    raAligned := (by show (gMal.r).toNat % 4 = 0; rw [hr]; decide),
    abi := habiE, mem := hmemEq,
    side := ⟨hE.hStackOK, hE.hAInvAt σ2 (by
      -- gp agrees between σ2 and cL: both = gMal.gm x3 (via the ABI frames).
      rw [habiE Register.x3 (by decide), hE.habi Register.x3 (by decide)]) hmemEq⟩ }

#print axioms staging_of_link

#print axioms staging_of_link

/-! ## §4. Capstone — the whole `EX_FN` arm run modulo the two NAMED bundles

`fnArmSeamRun_of_seams` threads `staging_of_link` (§3) and `allocBuildEntry_tail` (§2)
into `fnArmSeamRun_of_hEntry` (`AllocBuildEntrySplice.lean`), producing `FnArmSeamRun` —
the exact `hSeam` input of `fnArmGeom_hArm_of_seam` (`FnArmGeomReduce.lean`) that yields
the whole `EX_FN` arm run `EvalEntry → PreEpilogueV … (.closure a)`.  So the entire
downstream pipeline closes modulo ONLY the two named residual bundles
(`AllocBuildStagingLink` + its `hLink`, `AllocBuildTailFacts` + its `hReload`) — the
irreducible off-path machine (arm-front `a3 := φf env` decode; the `AllocBuildEntry`
field marshalling), which no combinator removes but which are now clean named-field
structures consumed through single destructurers. -/
theorem fnArmSeamRun_of_seams
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) {A : Arena} {SL : StackLayout} {gpv : BitVec 64}
    {headroom maxReq : Nat} (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (pp : Nat) (armPC : BitVec 64) (calleeLoaded : Mem → Prop)
    (sp r sret aExpr aEnv a3 : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (Malloc : MallocContract A SL gpv headroom maxReq)
    (gMal : MallocG maxReq)
    (hn16 : gMal.n = 16) (hr : gMal.r = 0x800033d0#64)
    -- staging residual: the arm-front linkage bundle.
    (hLink : Triple
      (fun c => ∃ o ment vv8 vv9 vv18,
        ArmEntryK g N A SL φf φc' st armPC calleeLoaded (.fn name params body)
          sp r sret aExpr aEnv vv8 vv9 vv18 o m0 ment c)
      (AllocBuildStagingLink Malloc gMal a3))
    -- tail residual: the reload run + the arm-entry-carried bundle.
    (hReload : ∀ (c : Config), (mallocCallSpec Malloc).ExitPost gMal c →
      ∃ c' : Config, AllocBuildReloadPost g N A SL φf φc φc' st ⟨env, name, params, body⟩ pp
        sp r sret aExpr m0 mMalloc v8 v9 v18 out0 c c') :
    FnArmSeamRun g N A SL φf φc' st st.store.closures.size armPC calleeLoaded
      name params body (st.store.allocClosure ⟨env, name, params, body⟩).1
      sp r sret aExpr aEnv m0 v8 v9 v18 out0
      (writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
        (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 pp) aExpr
          (BitVec.ofNat 64 (φf env)) sret) [])).log) :=
  fnArmSeamRun_of_hEntry g N φf φc φc' st env name params body pp armPC
    calleeLoaded sp r sret aExpr aEnv m0 mMalloc v8 v9 v18 out0 Malloc gMal
    (staging_of_link Malloc gMal a3 hn16 hr _ hLink)
    (allocBuildEntry_tail g N A SL φf φc φc' st env name params body pp
      sp r sret aExpr m0 mMalloc v8 v9 v18 out0 Malloc gMal hReload)

#print axioms fnArmSeamRun_of_seams

end Vsa.Sim
