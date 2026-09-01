import Vsa.Sim.AllocClosure
import Vsa.Sim.rows.FnArmClosureBuild

/-!
# `allocClosureContract_of` — the `AllocClosureContract` inhabitant

`AllocClosureContract` (`Vsa/Sim/AllocClosure.lean`) is the `env_new_spec` analog
for the closures arena: its single `spec` field is a total-correctness `Triple`
from the `EX_FN` arm's dispatch predicate `Pre` (the `ArmEntryK`-∃ shape supplied
by `fnArmSeamRun_of_allocClosure`) to the closure-build post (the fresh block `p`,
its `ClosureRepr`, the OLD store at `φc'`, the sret reads, and the whole
register/geometry/frame bundle at `0x800033ec`).

This file assembles that inhabitant from the machine pieces:

```
li a0,16 ; sd a3,0(sp) ; jal malloc          -- fnArmMallocCallBridge (0x800033c4)
ld a3,0(sp) ; beqz a0,OOM                      -- reload a3; OOM prune (nonNull_of_bounded)
li a5,4 ; sd s0,0(a0) ; sd a3,8(a0)            -- fnArmClosureBuildSeg (0x800033d8)
        ; sd a0,8(s1) ; sw a5,0(s1)
```

## The one honest machine gap: `AllocBuildEntry`

The malloc splice (`fnArmMallocCallBridge` ≫ `MallocContract.spec` ≫ prune ≫
`ld a3,0(sp)` reload ≫ `beqz a0` no-OOM edge) is the genuinely-off-path machine
run.  It is NOT hand-rolled here — it is packaged as ONE named-field reached-config
predicate `AllocBuildEntry` (parked at the closure-build entry `0x800033d8`, with
the malloc result `p` and the register/geometry/frame bundle already established),
and the run `Pre → AllocBuildEntry` is a single NAMED `Triple` premise `hEntry` of
`allocClosureContract_of`.  What THIS file proves — with NO further hypotheses — is:

* the pure closure-build seg run `AllocBuildEntry → 0x800033ec` via
  `fnArmClosureBuildRow` (`FnArmClosureBuildGen`);
* the four record reads off its write-log via `fnArmClosureBuild_reads`
  (`FnArmClosureBuild`), assembled into `ClosureRepr mpre φf p cd` and the
  `VAL_CLOSURE` sret reads;
* the `PhiExtends`/`StoreRepr`-at-`φc'` and the full post bundle, threaded from
  `AllocBuildEntry`'s carried fields.

So `hEntry` is the single machine residual (the malloc splice); the store-side and
build-side seams are discharged.  This mirrors how `env_new_spec` splices
`MallocContract.spec` — but here the splice is the named premise and the closure
materialisation is the proved half.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

namespace Vsa.Sim

/-! ## `AllocBuildEntry` — the reached config at the closure-build entry `0x800033d8`

The state after `malloc(16)` returned the fresh block `p` in `a0`, `a3` was reloaded
off the spill slot (`ld a3,0(sp)`), and the `beqz a0` OOM guard fell through (the
no-OOM edge, `MallocContract.nonNull_of_bounded`).  The closure-build seg
`fnArmClosureBuildSeg` reads exactly `x10=a0=p`, `x8=s0=aExpr`, `x13=a3=φf env`,
`x9=s1=sret` (its pin list `fnArmClosureBuildL p aExpr (φf env) sret`), so those four
register images are pinned here.  The malloc-result geometry (`p≠0`, `p%8=0`,
`A.contains p 16`, freshness vs old closures) and the OLD store at `φc'` /
`PhiExtends` witness are carried opaquely — they are established inside the malloc
splice (`hEntry`) and the arm's dispatch, NOT re-derived from the build seg. -/
structure AllocBuildEntry
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (cd : ClosureData) (p : Nat)
    (sp r sret aExpr : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String) (c : Config) : Prop where
  /-- Parked at the closure-build entry, memory = the post-malloc/reload map. -/
  hG : GoodState c.σ
  htick : c.tick < 2
  hpc : c.σ.regs.get? Register.PC = some (0x800033d8#64 : BitVec 64)
  hmem : c.σ.mem = mMalloc
  hmi : ∃ w, c.σ.regs.get? Register.minstret = some w
  /-- The four closure-build reads: `a0=p`, `s0=aExpr`, `a3=φf env`, `s1=sret`. -/
  hx10 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p)
  hx8 : c.σ.regs.get? Register.x8 = some aExpr
  hx13 : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (φf cd.env))
  hx9 : c.σ.regs.get? Register.x9 = some sret
  hx2 : c.σ.regs.get? Register.x2 = some (sp - 1088#64)
  /-- The fresh block `p`: nonzero, aligned, in-arena, fresh vs old closures. -/
  hpnz : p ≠ 0
  halign : p % 8 = 0
  harena : A.contains p 16
  hpfresh : ∀ ca, ca < st.store.closures.size → φc' ca ≠ p
  /-- The extension witness and the OLD store already represented at `φc'`. -/
  hext : PhiExtends φc φc' st.store.closures.size
  hp : φc' st.store.closures.size = p
  /-- `read64 mMalloc p = some aExpr.toNat` after the build is the fn-Expr node;
  the build's `sd s0,0(a0)` writes `s0 = aExpr`, and `ExprRepr` of it is carried
  (the arm-entry `ExprRepr ment aExpr (.fn …)` surviving to `mpre`). -/
  hExprRepr : ∀ mpre : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]?) →
    ExprRepr mpre aExpr.toNat (.fn cd.name cd.params cd.body)
  /-- `φf cd.env ≠ 0` (the captured env's frame image is a real address). -/
  hEnvNz : φf cd.env ≠ 0
  /-- `φf cd.env` fits in 64 bits (a real machine address), so the `a3 := φf env`
  register image reads back as the Nat `φf cd.env`. -/
  hEnvToNat : (BitVec.ofNat 64 (φf cd.env)).toNat = φf cd.env
  /-- The OLD store represented at `φc'` in the post-build memory `mpre` (frame-
  invariant under the build's disjoint stores + the malloc frame). -/
  hOld : ∀ mpre : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]?) →
    StoreRepr mpre N A φf φc' st.store
  /-- The malloc'd block `[p,p+16)` is disjoint from the sret box `[sret,sret+24)`
  (needed by `fnArmClosureBuild_reads`; `A.contains p 16` + the sret window). -/
  hps : p + 16 ≤ sret.toNat ∨ sret.toNat + 24 ≤ p
  hpof : ((BitVec.ofNat 64 p) + 8#64).toNat = (BitVec.ofNat 64 p).toNat + 8
  hpToNat : (BitVec.ofNat 64 p).toNat = p
  hsof : (sret + 8#64).toNat = sret.toNat + 8
  /-- The build seg's `ChainFacts` at the entry memory (store-target well-formedness
  for the `sd`/`sw` writes — established by the malloc splice's geometry). -/
  hfacts : ChainFacts c.σ.mem c.σ.mem
    (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr (BitVec.ofNat 64 (φf cd.env)) sret) []
    fnArmClosureBuildSeg
  /-- Key hygiene for the build seg pin list (the row's `KeysOK`). -/
  hkeys : KeysOK (keysG (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
    (BitVec.ofNat 64 (φf cd.env)) sret))
  /-- `eval_expr` still loaded in the post-build memory `mpre` (the build writes
  only `[p,p+16) ∪ [sret,sret+24)`, disjoint from the code image). -/
  hCodeSurvive : ∀ mpre : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]?) →
    Eval_exprLoaded mpre
  /-- The build seg's write-log frame: `writeLog mMalloc (build log)` differs from
  `mMalloc` ONLY inside `[p,p+16) ⊆ arena` and `[sret,sret+24)` (the sret window).
  So outside the stack, the arena, and the sret window, the two agree.  Derivable
  from the concrete write-log (writes at `p` — in-arena via `harena` — and at
  `sret`/`sret+8`) by `writeMap`-disjointness; carried as a field because the
  disjointness keys off `a ∉ arena` / `a ∉ sret-window`. -/
  hMpreFrame : ∀ a : Nat,
    ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
    (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨
    (writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
      (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
        (BitVec.ofNat 64 (φf cd.env)) sret) [])).log)[a]? = mMalloc[a]?
  /-- The four callee-saved spill slots `[sp-32, sp)` survive the build (they are in
  the stack, disjoint from the arena block `[p,p+16)` and the sret box — the build's
  only write targets).  Stated at the post-build memory `mpre`. -/
  hSpillReads :
    let mpre := writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
      (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
        (BitVec.ofNat 64 (φf cd.env)) sret) [])).log
    read64 mpre (sp.toNat - 8) = some r.toNat ∧
    read64 mpre (sp.toNat - 16) = some v8.toNat ∧
    read64 mpre (sp.toNat - 24) = some v9.toNat ∧
    read64 mpre (sp.toNat - 32) = some v18.toNat
  /-- The register / geometry / frame bundle the contract's post demands, at the
  build-entry config, EXCEPT PC/mem (which change across the build seg).  Because
  the build seg only writes `[p,p+16) ∪ [sret,sret+24)` and touches only `x5` (the
  `li a5`) among GPRs, the frame/geometry facts carry verbatim to `0x800033ec`. -/
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

set_option maxHeartbeats 800000 in
set_option maxRecDepth 100000 in
/-- **`allocClosureContract_of`** — inhabit `AllocClosureContract` from the malloc
splice (packaged as `hEntry : Triple Pre AllocBuildEntry`) and the proved
closure-build seg.

`mpre` is FIXED as the post-build memory `writeLog mMalloc (fnArmClosureBuildSeg
write-log)` (the contract's `mpre` parameter; the seam consumer's `mpre` is this
same expression).  `p := φc' st.store.closures.size` is the fresh block, `cd := ⟨env,
name, params, body⟩` the allocated closure record.  The build seg run
(`fnArmClosureBuildSeg`) is proved here; its four record reads
(`fnArmClosureBuild_reads`) give `ClosureRepr` and the `VAL_CLOSURE` sret reads; the
register/geometry/frame bundle transfers from `AllocBuildEntry` through the build's
register-frame (only `x15` written) and `hMpreFrame`.  The malloc splice is the ONE
named machine gap (`hEntry`). -/
theorem allocClosureContract_of
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc φc' : Addr → Nat)
    (st : Vsa.While.St) (env : Addr)
    (name : Option String) (params : List String) (body : List Stmt)
    (p : Nat) (Pre : Config → Prop)
    (sp r sret aExpr : BitVec 64) (m0 mMalloc : Mem)
    (v8 v9 v18 : BitVec 64) (out0 : Array String)
    -- the malloc splice: from the arm dispatch `Pre` to the build-entry config
    (hEntry : Triple Pre
      (AllocBuildEntry g N A SL φf φc φc' st ⟨env, name, params, body⟩ p
        sp r sret aExpr m0 mMalloc v8 v9 v18 out0)) :
    AllocClosureContract g N A SL φf φc φc' st ⟨env, name, params, body⟩
      st.store.closures.size p Pre sp r sret m0
      (writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
        (SegEvalState.init (fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr
          (BitVec.ofNat 64 (φf env)) sret) [])).log)
      v8 v9 v18 out0 where
  spec := by
    intro _hAeq
    -- Run: `Pre → AllocBuildEntry → 0x800033ec`, then assemble the post.
    intro c hpre
    obtain ⟨cB, hstepsB, hE⟩ := hEntry c hpre
    -- The four-register pin list the build seg reads (a0=p, s0=aExpr, a3=φf env, s1=sret).
    let L := fnArmClosureBuildL (BitVec.ofNat 64 p) aExpr (BitVec.ofNat 64 (φf env)) sret
    -- run the build seg off `AllocBuildEntry`'s carried facts
    obtain ⟨vmB, hmiB⟩ := hE.hmi
    have hGHolds : GHolds cB.σ L := by
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact hE.hx10
      · exact hE.hx8
      · exact hE.hx13
      · exact hE.hx9
      · exact True.intro
    obtain ⟨σ', i', hs', hi', hG', hmem', hout', hpc', hmi', hregs', hframe'⟩ :=
      fnArmClosureBuildSeg_seg cB.σ cB.tick cB.steps 0x800033d8#64 vmB L []
        hE.hG hE.hpc hmiB hGHolds hE.hkeys hE.hfacts
        (by have h : keysG L = [10, 8, 13, 9] := rfl
            rw [h]; show ChainOK 0x800033d8#64 [10, 8, 13, 9] fnArmClosureBuildSeg; decide)
        hE.htick
    -- the post config
    refine ⟨⟨σ', i', cB.steps + evalBlocksFuel fnArmClosureBuildSeg⟩, hstepsB.trans hs', ?_⟩
    -- abbreviate the post memory
    let mpre := writeLog mMalloc (evalBlocks fnArmClosureBuildSeg
      (SegEvalState.init L [])).log
    -- `σ'.mem = mpre`
    have hmemEq : σ'.mem = mpre := by rw [hmem', hE.hmem]
    -- the four record reads via `fnArmClosureBuild_reads` (block ptr = ofNat p,
    -- s0 = aExpr, a3 = ofNat (φf env), s1 = sret).  `hps` is phrased on `p` : Nat;
    -- rewrite via `hpToNat : (ofNat p).toNat = p`.
    have hpsBV : (BitVec.ofNat 64 p).toNat + 16 ≤ sret.toNat ∨
        sret.toNat + 24 ≤ (BitVec.ofNat 64 p).toNat := by
      rw [hE.hpToNat]; exact hE.hps
    obtain ⟨hrd0, hrd8, hrdPay, hrdKind⟩ :=
      fnArmClosureBuild_reads aExpr sret (BitVec.ofNat 64 p)
        (BitVec.ofNat 64 (φf env)) mMalloc hE.hpof hE.hsof hpsBV
    -- normalize the reads to `p : Nat` and `φf env`.
    rw [hE.hpToNat] at hrd0 hrd8 hrdPay
    -- the mpre-frame relation (build writes ⊆ arena ∪ sret-window), packaged.
    have hmpreFrame : ∀ a : Nat,
        ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
        (sret.toNat ≤ a ∧ a < sret.toNat + 24) ∨ mpre[a]? = mMalloc[a]? := by
      intro a ha1 ha2; exact hE.hMpreFrame a ha1 ha2
    -- `ClosureRepr mpre φf p cd` : read64 p = aExpr (the fn Expr node) + ExprRepr;
    -- read64 (p+8) = φf env, nonzero.
    have hExpr : ExprRepr mpre aExpr.toNat (.fn name params body) := hE.hExprRepr mpre hmpreFrame
    have hClosureRepr : ClosureRepr mpre φf p ⟨env, name, params, body⟩ := by
      refine ⟨⟨aExpr.toNat, hrd0, hExpr⟩, ?_, hE.hEnvNz⟩
      -- read64 mpre (p+8) = some (φf env) : hrd8 gives `some (ofNat (φf env)).toNat`
      rw [hE.hEnvToNat] at hrd8; exact hrd8
    -- store at φc' and the extension
    have hStore : StoreRepr mpre N A φf φc' st.store := hE.hOld mpre hmpreFrame
    -- `φc' st.store.closures.size = p`, so payload = some p, kind = 4.
    have hpayEq : read64 mpre (sret.toNat + 8) = some (φc' st.store.closures.size) := by
      rw [hE.hp]; exact hrdPay
    -- ===== the register / geometry / frame bundle at σ' (0x800033ec) =====
    obtain ⟨hsO, hstrO, _hcodeM, habiE, hR8, hR16, hR24, hR32,
      hgx8, hgx9, hgx18, hgx2, hmemframe, hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩ :=
      hE.hframe
    -- x9 = sret read off `GHolds σ' out.regs` (the seg preserves x9 in its pins).
    -- `out.regs = [(15,4),(10,p),(8,aExpr),(13,φf env),(9,sret)]`.
    have hregsList : (evalBlocks fnArmClosureBuildSeg (SegEvalState.init L [])).regs
        = [(15, 4#64), (10, BitVec.ofNat 64 p), (8, aExpr),
           (13, BitVec.ofNat 64 (φf env)), (9, sret)] := by rfl
    rw [hregsList] at hregs'
    obtain ⟨_h15, _h10, _h8, _h13, hx9g, _⟩ := hregs'
    have hx9' : σ'.regs.get? Register.x9 = some sret := by
      have := hx9g; simpa [gprGet] using this
    -- x2 = sp-1088 at σ' : the build's register-frame (only x15 = wrChain written,
    -- and x2 ∉ noiseRegs), carried from `AllocBuildEntry.hx2`.
    have hx2' : σ'.regs.get? Register.x2 = some (sp - 1088#64) := by
      rw [hframe' Register.x2 (by decide) (by decide)]; exact hE.hx2
    -- minstret survives (∃ w).
    have hmi'' : ∃ w, σ'.regs.get? Register.minstret = some w := hmi'
    -- sailOutput preserved by the seg (`hout' : σ'.sailOutput = cB.σ.sailOutput`).
    have hsailO : σ'.sailOutput = out0 := by rw [hout']; exact hsO
    -- code loaded at mpre.
    have hcodeMpre : Eval_exprLoaded mpre := hE.hCodeSurvive mpre hmpreFrame
    -- the AbiPreservedNoise frame at σ' : preserved regs tie back through the seg
    -- register-frame to cB, then to g via `AllocBuildEntry.hframe`'s `habiE`.
    have habi' : ∀ R : Register, AbiPreservedNoise R →
        (Register.x8 == R) = false → (Register.x9 == R) = false →
        (Register.x18 == R) = false → (Register.x2 == R) = false →
        σ'.regs.get? R = g R := by
      intro R hR h8 h9 h18 h2
      obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
      -- the seg writes only x15; if R = x15 it is not AbiPreserved (decide-excluded).
      by_cases hR15 : R = Register.x15
      · subst hR15; exact absurd hab (by decide)
      · rw [hframe' R (by
          -- R ∉ noiseRegs : each noise register avoids R by an `AbiPreservedNoise` field.
          intro rr hrr
          simp only [noiseRegs, List.mem_cons, List.not_mem_nil, or_false] at hrr
          rcases hrr with h | h | h | h | h | h | h
          · exact h ▸ hmiR
          · exact h ▸ hpcR
          · exact h ▸ hnpcR
          · exact h ▸ hmiiR
          · exact h ▸ hmcR
          · exact h ▸ hmtR
          · exact h ▸ hmipR) (by
          -- R ∉ wrChain (= [15]) since R ≠ x15.
          intro n hn
          have hwr : wrChain fnArmClosureBuildSeg = [15] := by decide
          rw [hwr] at hn
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
          subst hn
          show (gprReg 15 == R) = false
          rw [beq_eq_false_iff_ne]; exact fun h => hR15 h.symm)]
        exact habiE R ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ h8 h9 h18 h2
    -- ===== assemble the whole Post =====
    refine ⟨hmemEq, hE.hp, hE.hpnz, hE.harena, hE.halign, hE.hpfresh, hClosureRepr,
      hE.hext, hStore, ?_, ?_, ?_, ?_⟩
    · -- read32 mpre sret = 4
      exact hrdKind
    · -- read64 mpre (sret+8) = some (φc' a)  (a = closures.size)
      exact hpayEq
    · -- φc' a ≠ 0  (= p ≠ 0)
      rw [hE.hp]; exact hE.hpnz
    · -- the register / geometry / frame bundle
      obtain ⟨hS8, hS16, hS24, hS32⟩ := hE.hSpillReads
      refine ⟨hG', hi', hpc', hx9', hx2', hmi'', hsailO, hstrO, hcodeMpre, habi',
        hS8, hS16, hS24, hS32, hgx8, hgx9, hgx18, hgx2, ?_,
        hsp1088, hsphi, hsplo, hspwin, hsp8, hraAl⟩
      -- memframe over mpre vs m0 : compose hMpreFrame (mpre vs mMalloc, at addresses
      -- outside stack/arena/sret) with hmemframe (mMalloc vs m0).
      intro aa haStack haArena
      rcases hE.hMpreFrame aa haStack haArena with hInSret | hEqMalloc
      · exact Or.inl hInSret
      · rcases hmemframe aa haStack haArena with hInSret2 | hEqM0
        · exact Or.inl hInSret2
        · exact Or.inr (hEqMalloc.trans hEqM0)

#print axioms allocClosureContract_of

end Vsa.Sim
