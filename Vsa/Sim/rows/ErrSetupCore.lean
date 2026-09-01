import Vsa.Sim.rows.ErrSpillCore
import Vsa.Sim.SegReadback

/-!
# `ErrSetupCore` — the seg-GENERIC register-setup-prefix→jal bridge (Family B)

Eleven of the 19 distinct `jal runtime_error` sites are NOT preceded by a
contiguous pure-`sd` spill run (Family A / `ErrSpillCore.spillSeg_toJalErr`).
Instead the jal is immediately preceded by a run that COMPUTES the
`runtime_error` argument registers:

```
mv a0,sN         -- x10 := entry value of sN  (sN = s1/x9 or s2/x18)
li a4,0          -- x14 := 0                   (a computed constant)
auipc a2,…; addi a2,a2,…   -- x12 := message-pointer constant
…                -- possibly mv a1,sK / mv a3,… / li a3,0 / ld a3,0(sp) / addi a3,sp,…
```

so `wrChain ≠ []` (the seg writes `x10..x14`) and the entry predicate can NOT
carry `x10 = inp` as a *preserved* pin the way Family A does.  The crux is:

  * **`x10 = inp` is COMPUTED.**  `x10` at the jal is `mv a0,sN`'s value = the
    ENTRY value of `sN`.  So the entry predicate pins `x18(s2) = inp` (or
    `x9(s1) = inp`) and the seg's readback of `x10` off `GHolds σ' out.regs`
    (`SegReadback.gholds_lookup_ld` + `lookupG_runGM_snoc` + `srcVal_runGM_ne`)
    equals `inp`.  The M4-side residual is the *readback equality*
    `lookupG 10 out.regs = some inp` — the constant/mv value the seg computes.

  * **The `g` ghost-frame splits.**  `NotWrittenJmp` covers `x1,x2,x8,x9,x10,
    x18..x27` (+ every non-GPR).  The seg writes `x10..x14`; of those, only
    `x10` is in the `NotWrittenJmp` set that the frame would otherwise preserve,
    and `x11..x14` are ALSO `NotWrittenJmp` (nothing in the avoid list equals
    them) yet ARE written.  So the g-frame `∀ R, NotWrittenJmp R → regs R = g R`
    at the jal is NOT the pure entry-preserved carry Family A enjoys: it is
    supplied as ONE named residual `hgJal` about the seg POST (the M4 side
    chooses `g`, so pinning `g` on the computed regs to their computed values is
    exactly its job).

  * **Memory side.**  Every Family-B prefix here is STORE-free EXCEPT
    `0x80003cc4` (one `sw zero,8(s2)`); for the store-free ones `wrChain`'s
    memory log is empty so `σ'.mem = m0 = S.m0` trivially, and the loaded images
    survive verbatim.  The one store site carries the post-store memory as
    `S.m0 = writeLog m0 log` exactly as Family A did.

This file factors the shape into ONE seg-parametric lemma
`spillSetupSeg_toJalErr` over an arbitrary setup seg `bs`, with a NAMED-FIELD
entry structure `SetupArmPre` (per R7).  Per-site files then emit only the
`#derive_case` for `bs`, the `x10` readback, and a thin instantiation.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable Vsa
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Sim.Code (Runtime_errorLoaded LongjmpLoaded)
open Vsa.While
open Register

namespace Vsa.Sim

local notation "SpecSt" => Vsa.While.St

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## Readback peel for a MIDDLE writer

Family A's `SegReadback.lookupG_runGM_snoc` reads back a register whose writer is
the body's LAST instruction.  Family B's `x10` writer (`mv a0,sN`) is followed by
the `auipc/addi a2,a3` message-pointer instructions, so `x10`'s writer is in the
MIDDLE.  These peel the trailing non-writers of `n` off `lookupG n`, reducing the
middle-writer case to the snoc lemma — structurally, never reducing the fold. -/

/-- `lookupG n` is unchanged by a `stepGM` writing a DIFFERENT register (stores
write nothing; a non-store's `rd ≠ n` erase leaves `n`'s cell). -/
theorem lookupG_stepGM_ne (a : MInstr) (L : GRegs) (bs : List (BitVec 8)) (n : Nat)
    (h : n ≠ a.rd) : lookupG n (stepGM a L bs) = lookupG n L := by
  unfold stepGM
  split
  · rfl
  · rfl
  · rfl
  · rfl
  · show lookupG n ((a.rd, wvalM a L bs) :: eraseG a.rd L) = lookupG n L
    rw [lookupG, if_neg (by omega), lookupG_eraseG_ne n a.rd (by omega) L]

/-- `lookupG n` survives a whole `runGM body …` fold whose body never writes `n`. -/
theorem lookupG_runGM_ne (n : Nat) : ∀ (body : List MInstr),
    (∀ a ∈ body, a.rd ≠ n) → ∀ (L : GRegs) (lds : List (List (BitVec 8))),
      lookupG n (runGM body L lds) = lookupG n L := by
  intro body
  induction body with
  | nil => intro _ L lds; rfl
  | cons a rest ih =>
    intro h L lds
    rw [runGM, ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]
    exact lookupG_stepGM_ne a L (lds.headD []) n (Ne.symm (h a (List.mem_cons_self ..)))

/-- **The middle-writer readback.**  `body = pre ++ [a] ++ post` where `a` writes
`n` (a non-store `mv`/`addi`), `pre` and `post` never write `n`: `lookupG n` reads
back the writer's `wvalM` over the peeled-source pin state, peeling `post` with
`lookupG_runGM_ne` and `pre` with the source lemmas at the use site. -/
theorem lookupG_runGM_mid (pre : List MInstr) (a : MInstr) (post : List MInstr)
    (L : GRegs) (lds : List (List (BitVec 8)))
    (hstore : a.kind ≠ .sw ∧ a.kind ≠ .sd ∧ a.kind ≠ .sb ∧ a.kind ≠ .sh) (n : Nat)
    (hrd : a.rd = n)
    (hpost : ∀ b ∈ post, b.rd ≠ n) :
    lookupG n (runGM (pre ++ a :: post) L lds)
      = some (wvalM a (runGM pre L lds) ((ldsRunM pre lds).headD [])) := by
  induction pre generalizing L lds with
  | nil =>
    simp only [List.nil_append, runGM, ldsRunM]
    rw [lookupG_runGM_ne n post hpost (stepGM a L (lds.headD [])) (stepLdsM a.kind lds)]
    exact lookupG_stepGM_writer a L (lds.headD []) hstore n hrd
  | cons b rest ih =>
    simp only [List.cons_append, runGM, ldsRunM]
    exact ih (stepGM b L (lds.headD [])) (stepLdsM b.kind lds)

#print axioms lookupG_runGM_mid

/-- **The seg-generic register-setup-prefix entry predicate.**  A config parked at
a setup block entry `pc0` for an ARBITRARY setup seg `bs` ending at the jal PC
`pcJal` (bytes `b0..b3`).  Named-field (R7).  Differs from Family A's `SpillArmPre`
in exactly the two crux fields:

* `hx10read` — the seg's readback of `x10` off its OUTPUT reg map equals `inp`
  (the M4 residual: `x10` is computed by `mv a0,sN`, and `sN`'s entry value is
  `inp`; the concrete readback is proved per-site by `lookupG_runGM_snoc` +
  `srcVal_runGM_ne`, or supplied as the arm's named datum).
* `hgJal` — the whole jal-point `g` ghost-frame, read off the seg output: for
  every `NotWrittenJmp R`, the seg's post value of `R` (the frame-preserved entry
  value for the un-written ones, the computed value for `x11..x14`) equals `g R`.
  This is the genuine M4-side residual (the M4 side chooses `g`).  It is stated
  over the seg output `out.regs` + the entry state via `gprGet`, and the bridge
  turns it into the jal-point `regs R = g R` using `GHolds σ' out.regs`.

The other fields (`GoodState`/PC/minstret/`GHolds`/`KeysOK`/`ChainFacts`/`ChainOK`
/mem/tick/`WinRAM`/loaded-images/jal-byte-pins/end-PC) are exactly Family A's. -/
structure SetupArmPre (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8))) (bs : List BBlock)
    (pc0 pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) (c : Config) : Prop where
  hG : GoodState c.σ
  hmem : c.σ.mem = m0
  hpc : c.σ.regs.get? Register.PC = some pc0
  hmi : ∃ vm, c.σ.regs.get? Register.minstret = some vm
  hL : GHolds c.σ L
  hkeys : KeysOK (keysG L)
  hfacts : ChainFacts c.σ.mem c.σ.mem L lds bs
  hwf : ChainOK pc0 (keysG L) bs
  htick : c.tick < 2
  hwin : WinRAM (S.inp + 16#64)
  hm0eq : S.m0 = writeLog m0 (evalBlocks bs (SegEvalState.init L lds)).log
  hRE : Runtime_errorLoaded S.m0
  hLJ : LongjmpLoaded S.m0
  hb0 : S.m0[pcJal.toNat]? = some b0
  hb1 : S.m0[pcJal.toNat + 1]? = some b1
  hb2 : S.m0[pcJal.toNat + 2]? = some b2
  hb3 : S.m0[pcJal.toNat + 3]? = some b3
  hpcEq : evalBlocksPC pc0 (SegEvalState.init L lds) bs = pcJal
  -- the two Family-B crux residuals:
  hx10read : lookupG 10 (evalBlocks bs (SegEvalState.init L lds)).regs = some S.inp
  hgJal : ∀ R : Register, NotWrittenJmp R →
    (∀ σ' : MState, GHolds σ' (evalBlocks bs (SegEvalState.init L lds)).regs →
      (∀ Q : Register, (∀ rr ∈ noiseRegs, (rr == Q) = false) →
        (∀ n ∈ wrChain bs, (gprReg n == Q) = false) →
        σ'.regs.get? Q = c.σ.regs.get? Q) →
      σ'.regs.get? R = S.g R)

/-- **The seg-GENERIC register-setup-prefix bridge.**  Runs an arbitrary setup seg
`bs` via `segEval_sound`, exposing BOTH the raw frame clause AND `GHolds σ' out.regs`.
The `x10 = inp` conjunct is discharged by the readback residual `hx10read` through
`gholds_lookup_ld`; the whole g-frame is discharged by the named residual `hgJal`
applied to the exposed `GHolds`/frame.  This is exactly the `Triple SetupArmPre
(JalErrPre …)` that `<premise>_hsite_of_armBranch` (Family B) consumes. -/
theorem spillSetupSeg_toJalErr (S : ErrShared) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (L : GRegs) (lds : List (List (BitVec 8))) (bs : List BBlock)
    (pc0 pcJal : BitVec 64) (b0 b1 b2 b3 : BitVec 8) :
    Triple (SetupArmPre S m0 L lds bs pc0 pcJal b0 b1 b2 b3)
      (JalErrPre S.g S.inp S.m0 pcJal b0 b1 b2 b3) := by
  intro c hpre
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, hwf, htick, hwin,
    hm0eq, hRE, hLJ, hb0, hb1, hb2, hb3, hpcEq, hx10read, hgJal⟩ := hpre
  -- run the setup seg; keep BOTH the raw frame clause `hframe` and `GHolds σ' out.regs`.
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', ⟨w, hmi'⟩, hregs, hframe⟩ :=
    segEval_sound bs c.σ c.tick c.steps pc0 vm L lds
      hG hpc hmi hL hkeys hfacts hwf htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel bs⟩, hs, ?_⟩
  -- assemble `JalErrPre`.
  refine ⟨hG', ?_, ?_, ?_, ?_, ?_, hwin, ⟨w, hmi'⟩, hi', ?_, ?_, ?_, ?_, ?_⟩
  · exact hm0eq ▸ hRE
  · exact hm0eq ▸ hLJ
  · show σ'.mem = S.m0; rw [hmem', ← hm0eq]
  · show σ'.regs.get? Register.PC = _; rw [hpc']; exact congrArg some hpcEq
  · -- x10 = inp: read off `GHolds σ' out.regs` via the readback residual.
    show σ'.regs.get? Register.x10 = some S.inp
    have := gholds_lookup_ld (v := S.inp) L bs lds hregs hx10read
    -- `gprGet σ' 10 = some inp` is `σ'.regs.get? x10 = some inp` definitionally.
    exact this
  · -- the g ghost frame at the jal, via the named residual applied to the exposed post.
    intro R hR
    exact hgJal R hR σ' hregs hframe
  · show σ'.mem[pcJal.toNat]? = _; rw [hmem', ← hm0eq]; exact hb0
  · show σ'.mem[pcJal.toNat + 1]? = _; rw [hmem', ← hm0eq]; exact hb1
  · show σ'.mem[pcJal.toNat + 2]? = _; rw [hmem', ← hm0eq]; exact hb2
  · show σ'.mem[pcJal.toNat + 3]? = _; rw [hmem', ← hm0eq]; exact hb3

#print axioms spillSetupSeg_toJalErr

end Vsa.Sim
