import Vsa.Sim.rows.StrdupTailJalSeams
import Vsa.Sim.rows.StrdupEpilogueSeg
import Vsa.Sim.rows.StrcpyContractInhab
import Vsa.Sim.rows.StringifyStrdupTail
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.MemcpySpec
import Vsa.Sim.WriteLogNF
import Vsa.Sim.AllocSuccessAdapters

/-!
# `StrdupTailContractClose` — the malloc/memcpy/epilogue bridges + the contract instantiated

Half A of Task #80.  `stringifyStrdupTailContract`
(`Vsa/Sim/rows/StringifyStrdupTail.lean`) composed the shared `stringify` strdup
tail `0x80003044 → 0x80003084` (`strlen ≫ malloc ≫ memcpy ≫ epilogue`) as pure
`callSeg` algebra over the real framed callee contracts, leaving FOUR named
machine-bridge premises.  Wave 32 landed the three `jal` seams
(`strdupTail_{strlen,malloc,memcpy}_run`, `StrdupTailJalSeams.lean`) plus the
frame-carrying `bridgeStrlenPre` wrapper (`strdupTailBridgeStrlenPre_closed`).

This file supplies bridge wrappers and a conditional contract composition. The
actual successful malloc producer for the memcpy bridge remains open.
Each wrapper follows the `strdupTailBridgeStrlenPre_closed` idiom exactly: run the
landed `jal` seam, read the marshalled regs off the `GHolds` post, carry `sp`/`gp`/
ABI through the ABI frame, and survive `AInv` under the (gp-agree ∧ mem-agree)
`MallocContract`-interface stability.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.Alloc
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.Sim.Code (StringifyLoaded StrlenLoaded MemcpyLoaded)

namespace Vsa.Sim

-- discipline: allow(R7-conj-tower-def) the ∃s here are reached-Config run bundles
-- (∃ σ2 i2, Steps … ∧ …), the execution-notes-sanctioned `def : Prop := ∃ …` shape
-- (Prop structures reject Config data fields); the multi-fact posts ARE named-field
-- structures (`StrdupMemcpyContent`).

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## §1. `bridgeMallocPre` closed — the frame-carrying malloc-staging wrapper

`stringifyStrdupTailContract`'s `bridgeMallocPre` premise takes source `strlen_post
rStrlen str m0 ∧ CalleeFrame …` (with `rStrlen = 0x8000304c`, the malloc-staging
entry) to `MallocContract.spec`'s entry predicate at `mallocEntry`.  The machine
core is `strdupTail_malloc_run` (`addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp) ; jal
malloc`).  From `strlen_post`, `x10 = ofNat str.length` (the strlen result); the
staging computes `x10 = ofNat (str.length+1)` (the malloc size), spills it, and
lands at `mallocEntry` with `x1 = 0x8000305c`.

The malloc-staging touches only `x10`/`x12`/`x1` + the `8(sp)` spill — `x8`/s0 is
UNTOUCHED here (unlike env_define), so the malloc-entry ABI ghost equals the
strlen-frame ghost `gm` verbatim.  The spill writes memory, so the malloc-entry
memory is the write-log `mMalloc` (a caller-threaded ghost); the caller supplies
`StringifyLoaded mMalloc` (code region disjoint from the `spM+8` stack slot) and
`AInv`'s survival across the spill (`hAInvStableSpill`, spill outside the arena
footprint). -/

/-- **`bridgeMallocPre` discharged (frame-carrying).**  `mMalloc` is the caller's
malloc-entry memory ghost, required equal to the spill write-log (`hmMalloc`).
From `strlen_post ∧ CalleeFrame`, the `addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp) ; jal
malloc` staging lands `MallocContract.spec`'s entry predicate at `mallocEntry`.
`hjalmem` = `StringifyLoaded mMalloc` (the code pins survive the stack spill);
`hAInvStableSpill` = `AInv`'s (gp,mem)-agreement stability. -/
theorem strdupTailBridgeMallocPre_closed
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (spM : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (str : String) (m0 mMalloc : Std.ExtHashMap Nat (BitVec 8))
    (hmMalloc : mMalloc = writeLog m0 (evalBlocks strdupMallocArgSeg
      (SegEvalState.init (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [])).log)
    (hjalmem : StringifyLoaded (writeLog m0 (evalBlocks strdupMallocArgSeg
      (SegEvalState.init (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [])).log))
    -- the store-window `ChainFacts` (the `sd a2,8(sp)` lands above the HTIF window):
    -- the caller's stack-layout geometry, exactly the `cmpDispatchRow` `MemFacts` residue.
    (hfacts0 : ChainFacts m0 m0
      (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [] strdupMallocArgSeg)
    (hAInvStableSpill : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < (spM + 8#64).toNat ∨ (spM + 8#64).toNat + 8 ≤ a) →
        σa.mem[a]? = σb.mem[a]?) → AInv σa exts → AInv σb exts) :
    Triple
      (fun c => strlen_post (0x8000304c#64 : BitVec 64) str m0 c ∧
        CalleeFrame SL gpv headroom AInv exts spM gm c)
      (fun c =>
        GoodState c.σ ∧ c.tick < 2 ∧
        c.σ.regs.get? Register.PC = some (BitVec.ofNat 64 mallocEntry) ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 (str.length + 1)) ∧
        c.σ.regs.get? Register.x1 = some (0x8000305c#64 : BitVec 64) ∧
          (0x8000305c#64 : BitVec 64).toNat % 4 = 0 ∧
        c.σ.regs.get? Register.x2 = some spM ∧ StackOK SL spM headroom ∧
        c.σ.regs.get? Register.x3 = some gpv ∧
        (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
        AInv c.σ exts ∧ c.σ.mem = mMalloc) := by
  intro c hpre
  obtain ⟨hpost, hFrame⟩ := hpre
  obtain ⟨hG, hpc, hx10, hra, hmem⟩ := hpost
  obtain ⟨hsp, hstackOK, hgp, hAbi, hAInv, htick⟩ := hFrame
  obtain ⟨vmi, hmi⟩ : ∃ v, c.σ.regs.get? Register.minstret = some v := hG.minstret
  have hL : GHolds c.σ (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) :=
    ⟨hx10, hsp, trivial⟩
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, ⟨w2, hmi2⟩, hregs2, hmem2, habi2⟩ :=
    strdupTail_malloc_run c.σ c.tick c.steps vmi (BitVec.ofNat 64 str.length) spM m0
      hG hpc hmi hmem hL (hmem ▸ hfacts0) (hmem ▸ hjalmem) htick
  -- `x10 = ofNat (str.length+1)`: read the marshalled size off the `GHolds` post.
  have hsext1 : (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hsext0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hx10val : σ2.regs.get? Register.x10
      = some (BitVec.ofNat 64 str.length + sign_extend (m := 64) (0x001#12)
        + sign_extend (m := 64) (0x000#12)) :=
    gholds_lookup (n := 10) _ hregs2 (by rfl)
  have hx10out : σ2.regs.get? Register.x10 = some (BitVec.ofNat 64 (str.length + 1)) := by
    rw [hx10val, hsext1, hsext0, BitVec.add_zero]
    congr 1
    rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ← BitVec.ofNat_add]
  -- mem = mMalloc (the write-log)
  have hmemEq : σ2.mem = mMalloc := by rw [hmem2, hmMalloc]
  -- sp/gp preserved through the ABI frame
  have hsp2 : σ2.regs.get? Register.x2 = some spM := by
    rw [habi2 Register.x2 (by decide)]; exact hsp
  have hgp2 : σ2.regs.get? Register.x3 = some gpv := by
    rw [habi2 Register.x3 (by decide)]; exact hgp
  refine ⟨⟨σ2, i2, c.steps + evalBlocksFuel strdupMallocArgSeg + 1⟩, ?_, ?_⟩
  · cases c; exact hsteps
  · refine ⟨hG2, hi2, hpc2, hx10out, hra2, by decide, hsp2, hstackOK, hgp2, ?_, ?_, hmemEq⟩
    · intro R hR; rw [habi2 R (by exact hR)]; exact hAbi R hR
    · -- AInv survives: mem agrees with entry OUTSIDE the `[spM+8, spM+16)` spill
      -- window (the only bytes the `sd a2,8(sp)` staging touches), gp preserved.
      refine hAInvStableSpill c.σ σ2 ?_ ?_ hAInv
      · rw [hgp2, hgp]
      · intro a ha
        rw [hmemEq, hmMalloc, hmem]
        symm
        exact writeLog_out m0 _ a
          (by -- the concrete single-entry spill log is out of `[spM+8, spM+16)`.
              show OutL (evalBlocks strdupMallocArgSeg
                (SegEvalState.init (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [])).log a
              have hlog : (evalBlocks strdupMallocArgSeg
                (SegEvalState.init (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [])).log
                = [((spM + sign_extend (m := 64) (0x008#12)).toNat, 8,
                    BitVec.ofNat 64 str.length + sign_extend (m := 64) (0x001#12))] := by rfl
              rw [hlog]
              refine ⟨?_, trivial⟩
              have hsext8 : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
                apply BitVec.eq_of_toNat_eq; decide
              have he : (spM + sign_extend (m := 64) (0x008#12)).toNat = (spM + 8#64).toNat := by
                rw [hsext8]
              rw [he]; exact ha)

#print axioms strdupTailBridgeMallocPre_closed

/-! ## §2. Failure-aware composition boundary

`stringifyStrdupTailContract` executes `M.spec`, whose post permits NULL. Its
`StrdupTailMemcpyBridge` premise must handle that whole post. The successful
staging reader below cannot discharge that premise. Migrating the external
producer requires entry budget, concrete placement, and code at the actual
malloc call, then passing its selected successful endpoint to staging. -/

/-- The existing nullable-post bridge required by `stringifyStrdupTailContract`.
It remains an explicit residual; `strdupTailMemcpyBridge_of` supplies the distinct
success-input bridge below. The target records the reseated s0 ghost. -/
def StrdupTailMemcpyBridge
    (SL : StackLayout) (A : Arena) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (exts extsC : List (Nat × Nat))
    (spM spC : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (privFoot : Nat → Prop)
    (rM rMemcpy dst src : BitVec 64) (nMemcpy nMalloc : Nat)
    (mMalloc mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) : Prop :=
  Triple
    (fun c =>
      GoodState c.σ ∧ c.tick < 2 ∧
      c.σ.regs.get? Register.PC = some rM ∧
      c.σ.regs.get? Register.x2 = some spM ∧
      c.σ.regs.get? Register.x3 = some gpv ∧
      (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
      ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ AInv c.σ exts) ∨
       (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
         p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p nMalloc ∧
         (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧
         AInv c.σ ((p, nMalloc) :: exts))) ∧
      (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < spM.toNat) →
        c.σ.mem[a]? = mMalloc[a]?))
    (fun c => PreDispatch (ghostReseatS0 gm dst) rMemcpy dst src nMemcpy mMemcpy bs c ∧
      CalleeFrame SL gpv headroom AInv extsC spC (ghostReseatS0 gm dst) c)

/-! ## §2b. Read a selected successful malloc result -/

/-- The non-null pointer belongs to the same successful return configuration. -/
theorem strdupMemcpy_prune_null
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    {credits : Nat} {out : Array String}
    {gm : (R : Register) → Option (RegisterType R)} {sp r : BitVec 64} {m0 : Mem}
    (c : Config) (exts : List (Nat × Nat)) (nMalloc : Nat)
    (hpost : MallocSuccessExit A SL gpv maxReq credits M.AInv M.privFoot
      gm exts nMalloc sp r m0 out c) :
    ∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧ p ≠ 0 ∧
      p % 16 = 0 ∧ A.contains p nMalloc ∧
      (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧ M.AInv c.σ ((p, nMalloc) :: exts) :=
  hpost.result

#print axioms strdupMemcpy_prune_null

/-- **Gap-1 witness (a2-reload).**  Running the `lds`-generic `strdupTail_memcpy_run`
at the SINGLETON `[sizeBytes]` reloads the spilled size: `x12` at the memcpy entry is
`bytesVal MKind.ld sizeBytes`, pinned to `ofNat nMemcpy` by `hReadback`.  This
DISCHARGES the a2-reload (the mechanism the §2 doc named as unbuilt), and also lands
`x10`/`x11`/PC/`ra` at the memcpy entry — every `PreDispatch` register field. -/
theorem strdupMemcpyArg_a2_reload
    (σ : MState) (i u : Nat) (vminstret spM a0 src : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (sizeBytes : List (BitVec 8))
    (nMemcpy : Nat)
    (hReadback : bytesVal MKind.ld sizeBytes = BitVec.ofNat 64 nMemcpy)
    (hG : GoodState σ) (hpc : σ.regs.get? Register.PC = some (0x8000305c#64 : BitVec 64))
    (hminstret : σ.regs.get? Register.minstret = some vminstret)
    (hmem : σ.mem = m0)
    (hL : GHolds σ (strdupMemcpyArgL spM a0 src))
    (hfacts : ChainFacts σ.mem σ.mem (strdupMemcpyArgL spM a0 src) [sizeBytes] strdupMemcpyArgSeg)
    (hjalmem : StringifyLoaded (writeLog m0
      (evalBlocks strdupMemcpyArgSeg (SegEvalState.init (strdupMemcpyArgL spM a0 src) [sizeBytes])).log))
    (hi : i < 2) :
    ∃ (σ2 : MState) (i2 : Nat),
      Steps ⟨σ, i, u⟩ ⟨σ2, i2, u + evalBlocksFuel strdupMemcpyArgSeg + 1⟩ ∧ i2 < 2 ∧
        GoodState σ2 ∧
      σ2.regs.get? Register.PC = some (0x80006bc8#64 : BitVec 64) ∧
      σ2.regs.get? Register.x10 = some a0 ∧
      σ2.regs.get? Register.x11 = some src ∧
      σ2.regs.get? Register.x12 = some (BitVec.ofNat 64 nMemcpy) ∧
      σ2.regs.get? Register.x1 = some (0x80003070#64 : BitVec 64) ∧
      (∃ w, σ2.regs.get? Register.minstret = some w) := by
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, ⟨w2, hmi2⟩, hregs2, hmem2, _habi2⟩ :=
    strdupTail_memcpy_run σ i u vminstret spM a0 src m0 [sizeBytes]
      hG hpc hminstret hmem hL hfacts hjalmem hi
  have hsext0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨σ2, i2, hsteps, hi2, hG2, hpc2, ?_, ?_, ?_, hra2, ⟨w2, hmi2⟩⟩
  · exact gholds_lookup (n := 10) _ hregs2 (by rfl)
  · -- `mv a1,s1` = `addi x11,x9,0`: the reflected value carries `+ sign_extend 0`.
    have h := gholds_lookup _ hregs2 (show lookupG 11
      (evalBlocks strdupMemcpyArgSeg
        (SegEvalState.init (strdupMemcpyArgL spM a0 src) [sizeBytes])).regs
      = some (src + sign_extend (m := 64) (0x000#12)) from rfl)
    rwa [hsext0, BitVec.add_zero] at h
  · have h := gholds_lookup _ hregs2 (show lookupG 12
      (evalBlocks strdupMemcpyArgSeg
        (SegEvalState.init (strdupMemcpyArgL spM a0 src) [sizeBytes])).regs
      = some (bytesVal MKind.ld sizeBytes) from rfl)
    rw [hReadback] at h
    exact h

#print axioms strdupMemcpyArg_a2_reload

/-- **The frame-ghost OBSTRUCTION, machine-checked (Law 4).**  If `StrdupTailMemcpyBridge`
held for a `gm` with `gm x8 = some sOld`, then at any state satisfying its pre (which
pins `s0 = gm x8 = sOld` via `AbiPreserved x8`) whose memcpy-entry post pins
`s0 = gm x8 = sOld` too, the intervening `mv s0,a0` — which sets `s0 = a0` (the malloc
result `dst`) — would force `sOld = dst`.  We isolate the incompatibility as a pure
fact: the bridge's PRE and TARGET both pin `s0 = gm x8`, but the staging RESEATS s0,
so the two are simultaneously satisfiable only when the entry s0 already equals the
fresh malloc result — false in general.  This is the over-constraint; the fix is to
thread `gm[x8 := dst]` in the contract's memcpy target, an amendment to the READ-ONLY
`stringifyStrdupTailContract`. -/
theorem strdupMemcpy_frame_obstruction
    (gm : (R : Register) → Option (RegisterType R)) (sOld dst : BitVec 64)
    -- the bridge PRE frame (inherited from the malloc post, `∀ R AbiPreserved →
    -- get? R = gm R`, `AbiPreserved x8 = true`) pins the STAGING-entry s0 = `gm x8`:
    (hgmS0 : gm Register.x8 = some sOld)
    -- the bridge TARGET `CalleeFrame … gm` (SAME gm, `AbiPreserved x8 = true`) pins the
    -- MEMCPY-entry s0 = `gm x8`; but `mv s0,a0` reseated s0 to the malloc result `dst`:
    (hTargetPinsReseat : (some dst : Option (BitVec 64)) = gm Register.x8) :
    -- ⇒ the two same-gm frame pins force the entry s0 to equal the fresh malloc result:
    sOld = dst := by
  rw [hgmS0] at hTargetPinsReseat; exact (Option.some.inj hTargetPinsReseat).symm

#print axioms strdupMemcpy_frame_obstruction

/-! ## §2c. Staging from a successful malloc return

The staging run uses the supplied reload bytes and preserves the ABI under
`ghostReseatS0 gm dst`. The caller still supplies the pointer identity, byte
readback, chain facts, code, and memcpy content. The external nullable-post
composition remains unconnected to this successful reader. -/

/-- **The memcpy-CALL content residuals** — the `PreDispatch`/`CalleeFrame` fields the
strdup staging cannot manufacture (they are the memcpy callee's OWN precondition over
the fresh block + copy source), supplied by the caller at the memcpy-entry state `σ2`.
Named-field structure per CLAUDE.md (never an anonymous ∃/∧ tower).  Each field says
what supplies it:
- `loaded`: the memcpy code region is resident (`StringifyLoaded ⊇ MemcpyLoaded` on the
  staging write-log — the caller's code-image fact, as for the malloc/strlen bridges);
- `regions`: `Regions dst src nMemcpy` — the fresh malloc block is disjoint/in-RAM/
  above-HTIF/off-the-memcpy-code (from the malloc post's `A.contains`/`ExtDisjoint` + the
  arena's RAM geometry);
- `npos`: `0 < nMemcpy` (= `str.length + 1 > 0`, always);
- `meminv`: `MemInv dst src nMemcpy bs 0 mMemcpy σ2.mem` — the copy invariant at entry
  (source `[src,src+n)` reads `bs`, outside untouched — from the buffer's `CString` +
  the freshly-malloc'd, uninitialised-but-disjoint dst region);
- `hframe`: the memcpy-entry snapshot `∀ R, NotWrittenB R → get? R = ghostReseatS0 gm dst R`
  (the non-ABI live registers the memcpy dispatch reads — beyond `AbiExceptS0`, this is the
  caller's frame witness at the call site);
- `stackOK`/`ainvC`: `StackOK SL spM headroom` (an `sp`-value property, unchanged) and
  `AInv σ2 extsC` (the allocator invariant at the memcpy entry over `extsC`). -/
structure StrdupMemcpyContent
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (extsC : List (Nat × Nat))
    (spM : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (dst src : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (σ2 : MState) : Prop where
  loaded : MemcpyLoaded σ2.mem
  regions : Regions dst src nMemcpy
  npos : 0 < nMemcpy
  meminv : MemInv dst src nMemcpy bs 0 mMemcpy σ2.mem
  hframe : ∀ R : Register, NotWrittenB R → σ2.regs.get? R = ghostReseatS0 gm dst R
  stackOK : StackOK SL spM headroom
  ainvC : AInv σ2 extsC

/-- **The strdup-tail `bridgeMemcpyPre` PRE** (factored named predicate, so the
malloc-pointer link `hPtrDst` below can be stated over it without duplicating the
∧-tower).  This is exactly `StrdupTailMemcpyBridge`'s source. -/
def StrdupMemcpyBridgePre
    (SL : StackLayout) (A : Arena) (gpv : BitVec 64)
    (AInv : MState → List (Nat × Nat) → Prop) (exts : List (Nat × Nat))
    (spM : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (privFoot : Nat → Prop) (rM : BitVec 64) (nMalloc : Nat)
    (mMalloc : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.tick < 2 ∧
  c.σ.regs.get? Register.PC = some rM ∧
  c.σ.regs.get? Register.x2 = some spM ∧
  c.σ.regs.get? Register.x3 = some gpv ∧
  (∀ R, AbiPreserved R = true → c.σ.regs.get? R = gm R) ∧
  ((c.σ.regs.get? Register.x10 = some (0#64 : BitVec 64) ∧ AInv c.σ exts) ∨
   (∃ p, c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) ∧
     p ≠ 0 ∧ p % 16 = 0 ∧ A.contains p nMalloc ∧
     (∀ e ∈ exts, ExtDisjoint (p, nMalloc) e) ∧
     AInv c.σ ((p, nMalloc) :: exts))) ∧
  (∀ a, ¬ privFoot a → ¬ (SL.lo ≤ a ∧ a < spM.toNat) →
    c.σ.mem[a]? = mMalloc[a]?)

/-- Memcpy entry and its frame at the single staging endpoint. -/
structure StrdupMemcpyReady
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List Extent → Prop) (exts : List Extent) (sp : BitVec 64)
    (gm : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (n : Nat) (m0 : Mem) (bs : Nat → BitVec 8)
    (c : Config) : Prop where
  dispatch : PreDispatch (ghostReseatS0 gm dst) r dst src n m0 bs c
  frame : CalleeFrame SL gpv headroom AInv exts sp (ghostReseatS0 gm dst) c

/-- The staging bridge consumes a successful allocator return. The failure-aware
`StrdupTailMemcpyBridge` remains a separate residual of the old composition. -/
def StrdupTailSuccessMemcpyBridge
    (SL : StackLayout) (A : Arena) (gpv : BitVec 64) (headroom maxReq credits : Nat)
    (AInv : MState → List Extent → Prop) (exts extsC : List Extent)
    (spM spC : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (privFoot : Nat → Prop) (rM rMemcpy dst src : BitVec 64) (nMemcpy nMalloc : Nat)
    (mMalloc mMemcpy : Mem) (out : Array String) (bs : Nat → BitVec 8) : Prop :=
  Triple
    (MallocSuccessExit A SL gpv maxReq credits AInv privFoot
      gm exts nMalloc spM rM mMalloc out)
    (StrdupMemcpyReady SL gpv headroom AInv extsC spC gm
      rMemcpy dst src nMemcpy mMemcpy bs)

/-- Execute memcpy staging from the selected successful malloc post. -/
theorem strdupTailMemcpyBridge_of
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq)
    {credits : Nat} {out : Array String}
    (extsC : List (Nat × Nat)) (spC : BitVec 64)
    (gm : (R : Register) → Option (RegisterType R))
    (dst src : BitVec 64) (nMemcpy nMalloc : Nat)
    (mMalloc mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8)
    (sizeBytes : List (BitVec 8))
    (hReadback : bytesVal MKind.ld sizeBytes = BitVec.ofNat 64 nMemcpy)
    -- Identify the selected successful pointer with the caller's destination.
    (hPtrDst : ∀ (σ : MState) (p : Nat),
      σ.regs.get? Register.x10 = some (BitVec.ofNat 64 p) → p ≠ 0 → p % 16 = 0 →
      A.contains p nMalloc → (∀ e ∈ extsC, ExtDisjoint (p, nMalloc) e) →
      M.AInv σ ((p, nMalloc) :: extsC) →
      σ.regs.get? Register.x10 = some dst)
    -- the source pointer `s1`/x9 (the scratch buffer): callee-saved, tied to `gm x9`.
    -- `AbiPreserved x9 = true`, so the pre's ABI frame gives `get? x9 = gm x9 = some src`.
    (hSrc : gm Register.x9 = some src)
    -- the a2-reload code-image + chain facts, over the bridge-entry memory `m0`:
    (hjalmem : ∀ (m0 : Std.ExtHashMap Nat (BitVec 8)), StringifyLoaded (writeLog m0
      (evalBlocks strdupMemcpyArgSeg
        (SegEvalState.init (strdupMemcpyArgL spC dst src) [sizeBytes])).log))
    (hfacts : ∀ (m0 : Std.ExtHashMap Nat (BitVec 8)),
      ChainFacts m0 m0 (strdupMemcpyArgL spC dst src) [sizeBytes] strdupMemcpyArgSeg)
    -- the memcpy-CALL content residuals at the memcpy-entry state (named bundle):
    (hcontent : ∀ (σ2 : MState),
      σ2.regs.get? Register.PC = some (0x80006bc8#64 : BitVec 64) →
      σ2.regs.get? Register.x10 = some dst →
      σ2.regs.get? Register.x11 = some src →
      σ2.regs.get? Register.x12 = some (BitVec.ofNat 64 nMemcpy) →
      StrdupMemcpyContent SL gpv headroom M.AInv extsC spC gm dst src nMemcpy mMemcpy bs σ2) :
    StrdupTailSuccessMemcpyBridge SL A gpv headroom maxReq credits
      M.AInv extsC extsC spC spC gm M.privFoot (0x8000305c#64) (0x80003070#64)
      dst src nMemcpy nMalloc mMalloc mMemcpy out bs := by
  intro c hpre
  have hG := hpre.returned.good
  have htick := hpre.returned.tick
  have hpc := hpre.returned.pc
  have hsp := hpre.returned.sp
  have hgp := hpre.returned.gp
  have hAbi := hpre.returned.frame
  -- Read the selected successful endpoint, then identify its pointer with `dst`.
  obtain ⟨p, hx10p, hpne, hp16, hcontains, hdisjp, hainvp⟩ :=
    strdupMemcpy_prune_null M c extsC nMalloc hpre
  have hx10dst : c.σ.regs.get? Register.x10 = some dst :=
    hPtrDst c.σ p hx10p hpne hp16 hcontains hdisjp hainvp
  obtain ⟨vmi, hmi⟩ : ∃ v, c.σ.regs.get? Register.minstret = some v := hG.minstret
  -- x9 = src: s1 is callee-saved (`AbiPreserved x9`), tied to `gm x9 = some src`.
  have hx9src : c.σ.regs.get? Register.x9 = some src := by
    rw [hAbi Register.x9 (by decide)]; exact hSrc
  -- the staging entry regs: x2 = spC, x10 = dst (a0 = malloc result), x9 = src.
  have hL : GHolds c.σ (strdupMemcpyArgL spC dst src) := ⟨hsp, hx10dst, hx9src, trivial⟩
  -- run the memcpy staging to the memcpy entry `0x80006bc8` at the a2-reload singleton.
  obtain ⟨σ2, i2, hsteps, hi2, hG2, hpc2, hra2, ⟨w2, hmi2⟩, hregs2, hmem2, habi2⟩ :=
    strdupTail_memcpy_run c.σ c.tick c.steps vmi spC dst src c.σ.mem [sizeBytes]
      hG hpc hmi rfl hL (hfacts c.σ.mem) (hjalmem c.σ.mem) htick
  -- read the register deltas off the GHolds post (mv-carries `+ sign_extend 0`).
  have hsext0 : (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  have hx10' : σ2.regs.get? Register.x10 = some dst :=
    gholds_lookup (n := 10) _ hregs2 (by rfl)
  have hx11' : σ2.regs.get? Register.x11 = some src := by
    have h := gholds_lookup _ hregs2 (show lookupG 11
      (evalBlocks strdupMemcpyArgSeg
        (SegEvalState.init (strdupMemcpyArgL spC dst src) [sizeBytes])).regs
      = some (src + sign_extend (m := 64) (0x000#12)) from rfl)
    rwa [hsext0, BitVec.add_zero] at h
  have hx12' : σ2.regs.get? Register.x12 = some (BitVec.ofNat 64 nMemcpy) := by
    have h := gholds_lookup _ hregs2 (show lookupG 12
      (evalBlocks strdupMemcpyArgSeg
        (SegEvalState.init (strdupMemcpyArgL spC dst src) [sizeBytes])).regs
      = some (bytesVal MKind.ld sizeBytes) from rfl)
    rw [hReadback] at h; exact h
  have hx8' : σ2.regs.get? Register.x8 = some dst := by
    have h := gholds_lookup (n := 8) _ hregs2 (show lookupG 8
      (evalBlocks strdupMemcpyArgSeg
        (SegEvalState.init (strdupMemcpyArgL spC dst src) [sizeBytes])).regs
      = some (dst + sign_extend (m := 64) (0x000#12)) from rfl)
    rwa [hsext0, BitVec.add_zero] at h
  have hx2' : σ2.regs.get? Register.x2 = some spC :=
    gholds_lookup (n := 2) _ hregs2 (by rfl)
  -- gp preserved through the `AbiExceptS0` frame (x3 is AbiPreserved, ≠ x8).
  have hx3' : σ2.regs.get? Register.x3 = some gpv := by
    rw [habi2 Register.x3 (by decide)]; exact hgp
  -- the memcpy-CALL content residuals at the entry state.
  have hct := hcontent σ2 hpc2 hx10' hx11' hx12'
  obtain ⟨hloaded, hregions, hnpos, hmeminv, hframe, hstackOK, hainvC⟩ := hct
  -- assemble the target: PreDispatch (ghostReseatS0 gm dst) ∧ CalleeFrame … (ghostReseatS0 gm dst).
  refine ⟨⟨σ2, i2, c.steps + evalBlocksFuel strdupMemcpyArgSeg + 1⟩, ?_, ?_, ?_⟩
  · cases c; exact hsteps
  · exact { good := hG2, loaded := hloaded, pc := hpc2, a0 := hx10', a1 := hx11',
            a2 := hx12', ra := hra2, minstret := ⟨w2, hmi2⟩, tick := hi2,
            regions := hregions, npos := hnpos, meminv := hmeminv, hframe := hframe }
  · -- CalleeFrame … (ghostReseatS0 gm dst)
    refine ⟨hx2', hstackOK, hx3', ?_, hainvC, hi2⟩
    -- the reseated ABI frame: x8 = dst = ghostReseatS0 gm dst x8; else = gm R.
    intro R hR
    by_cases hR8 : R = Register.x8
    · subst hR8; rw [hx8', ghostReseatS0_x8]
    · -- R ≠ x8, AbiPreserved: AbiExceptS0 R = true ⇒ σ2 R = c.σ R = gm R = ghostReseatS0 gm dst R.
      rw [ghostReseatS0_ne gm dst hR8]
      have habiExcept : AbiExceptS0 R = true := by
        show (AbiPreserved R && !(R == Register.x8)) = true
        rw [hR]; simp [beq_eq_false_iff_ne.mpr hR8]
      rw [habi2 R habiExcept]; exact hAbi R hR

#print axioms StrdupMemcpyContent
#print axioms strdupTailMemcpyBridge_of

/-! ## §3. `bridgeEpilogue` closed — the `ld ra ; mv a0,s0 ; ret` return + CString readback

`stringifyStrdupTailContract`'s `bridgeEpilogue` takes `(∃ g',
memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs) ∧ CalleeFrame …` to
`StrdupTailExit rRet str`.  The machine core is `strdupEpilogueRow` (the `ld ra ;
mv a0,s0 ; ld s0/s1 ; addi sp,sp,112 ; ret` span, `0x80003070 → 0x80003084`, no
stores).  The memcpy byte-post lands EXACTLY at the epilogue entry PC (`rMemcpy =
0x80003070`); its `NotWrittenB` frame preserves `s0`/x8 (= `new = dst`, saved by the
memcpy prefix) and `sp`/x2, so the epilogue `mv a0,s0` returns `dst` as the fresh
result.

The CString readback: the memcpy byte-post copied `nMemcpy = str.length + 1` bytes
(the whole C-string INCLUDING the NUL) into `[dst, dst+nMemcpy)`, so `CString
mem dst str` follows byte-for-byte (`cstring_shift_copy` over the copied window).
The epilogue does not store, so the exit memory equals the byte-post memory and the
CString survives.

The DATA the epilogue entry needs beyond the byte-post — the spill images `lds`
(the saved `ra`/`s0`/`s1` the `ld`s reload), the reloaded-`ra` jr-target `= rRet`,
`s0 = dst`, `sp = spC`, and the byte→CString transport — are a caller-supplied
bundle `hEntry` (the caller landed the frame spills on the prologue).  This is the
`bridgeStrlenPre_closed`-class packaging, over the `jr`-terminated epilogue. -/

/-- **`bridgeEpilogue` discharged.**  From the memcpy byte-post `∧ CalleeFrame`, the
`ld ra ; mv a0,s0 ; ret` epilogue lands `StrdupTailExit rRet str` (`x10 = dst ≠ 0`,
`CString mem dst str`).  `hEntry` bundles the spill-image data + the byte→CString
readback (the caller's prologue frame layout): given the byte-post state, it yields
the epilogue-entry pins (`s0 = dst`, `sp = spC`, the restore loads `lds` with jr-
target `rRet`), the `ChainFacts`, `dst ≠ 0`, and `CString (byte-post mem) dst str`. -/
theorem strdupTailBridgeEpilogue_closed
    (SL : StackLayout) (gpv : BitVec 64) (headroom : Nat)
    (AInv : MState → List (Nat × Nat) → Prop) (extsC : List (Nat × Nat))
    (spC : BitVec 64) (gm : (R : Register) → Option (RegisterType R))
    (rMemcpy dst rRet : BitVec 64) (nMemcpy : Nat)
    (mMemcpy : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (str : String)
    (hrMemcpy : rMemcpy = 0x80003070#64) (hdstne : dst ≠ 0#64)
    -- the caller's prologue-frame bundle: from the byte-post state, the epilogue
    -- entry data (spill images + jr-target `rRet` + `s0 = dst`, `sp = spC`) and the
    -- byte→CString transport, all keyed to the copied window.
    (hEntry : ∀ (g' : (R : Register) → Option (RegisterType R)) (c : Config),
      memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c →
      ∃ lds : List (List (BitVec 8)),
        GHolds c.σ (strdupEpilogueL spC dst) ∧
        ChainFacts c.σ.mem c.σ.mem (strdupEpilogueL spC dst) lds strdupEpilogueSeg ∧
        evalBlocksPC 0x80003070#64 (SegEvalState.init (strdupEpilogueL spC dst) lds)
          strdupEpilogueSeg = rRet ∧
        (writeLog c.σ.mem (evalBlocks strdupEpilogueSeg
          (SegEvalState.init (strdupEpilogueL spC dst) lds)).log = c.σ.mem) ∧
        CString c.σ.mem dst.toNat str) :
    Triple
      (fun c => (∃ g', memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs c) ∧
        CalleeFrame SL gpv headroom AInv extsC spC (ghostReseatS0 gm dst) c)
      (StrdupTailExit rRet str) := by
  intro c hpre
  obtain ⟨⟨g', hbyte⟩, _hFrame⟩ := hpre
  obtain ⟨hGb, hpcb, ha0b, hrab, hcopied, houtside, htickb, hframeb⟩ := hbyte
  obtain ⟨lds, hL, hfacts, hjr, hnostore, hcstr⟩ := hEntry g' c ⟨hGb, hpcb, ha0b, hrab, hcopied, houtside, htickb, hframeb⟩
  -- run the epilogue row over the byte-post state.
  have hpc0 : c.σ.regs.get? Register.PC = some (0x80003070#64 : BitVec 64) := by
    rw [hpcb, hrMemcpy]
  have hkeys : KeysOK (keysG (strdupEpilogueL spC dst)) := by
    have h : keysG (strdupEpilogueL spC dst) = [2, 8] := rfl
    rw [h]; decide
  obtain ⟨c', hsteps, hepost⟩ :=
    strdupEpilogueRow spC dst lds c.σ.mem c
      ⟨hGb, rfl, hpc0, hGb.minstret, hL, hkeys, hfacts, htickb⟩
  obtain ⟨hGe, hmeme, hpce, hx10e⟩ := hepost
  refine ⟨c', hsteps, hGe, ?_, dst.toNat, ?_, ?_, ?_⟩
  · rw [hpce, hjr]
  · rw [hx10e]; congr 1; exact (BitVec.ofNat_toNat 64 dst).symm ▸ rfl
  · -- `dst ≠ 0` ⇒ `dst.toNat ≠ 0`
    intro h; exact hdstne (by
      apply BitVec.eq_of_toNat_eq; rw [h]; rfl)
  · -- CString: the epilogue does not store (`hnostore`), so exit mem = byte-post mem.
    rw [hmeme, hnostore]; exact hcstr

#print axioms strdupTailBridgeEpilogue_closed

/-! ## §4. `stringifyStrdupTailContract` instantiated

The strlen, malloc-entry, and epilogue wrappers are supplied below. The nullable
`StrdupTailMemcpyBridge` remains a premise. The success-input bridge does not
satisfy it: the external producer still executes failure-aware `M.spec`. -/

/-- Conditional composition through the existing failure-aware allocator spec.
The caller still owes `hMemcpyBridge`; this theorem does not connect the new
successful staging reader to an actual allocator execution. -/
theorem stringifyStrdupTailContract_closed
    {A : Arena} {SL : StackLayout} {gpv : BitVec 64} {headroom : Nat}
    (str : String)
    (M : MallocContract A SL gpv headroom (str.length + 1))
    (gm : (R : Register) → Option (RegisterType R))
    (rRet : BitVec 64)
    (bufPtr : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (exts extsC : List (Nat × Nat)) (spM spC : BitVec 64)
    (mMalloc mMemcpy : Std.ExtHashMap Nat (BitVec 8))
    (dst src : BitVec 64) (bs : Nat → BitVec 8)
    (halignC : (0x80003070#64 : BitVec 64).toNat % 4 = 0)
    (hrouteCbyte : (src.toNat ^^^ dst.toNat) % 8 ≠ 0 ∨ (str.length + 1) < 8)
    (hdstne : dst ≠ 0#64)
    -- strlen-frame stability (leaf reader):
    (hAInvStableStrlen : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, σa.mem[a]? = σb.mem[a]?) → M.AInv σa exts → M.AInv σb exts)
    -- malloc-frame spill stability + code survival:
    (hmMalloc : mMalloc = writeLog m0 (evalBlocks strdupMallocArgSeg
      (SegEvalState.init (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [])).log)
    (hjalmemMalloc : StringifyLoaded (writeLog m0 (evalBlocks strdupMallocArgSeg
      (SegEvalState.init (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [])).log))
    (hfactsMalloc : ChainFacts m0 m0
      (strdupMallocArgL (BitVec.ofNat 64 str.length) spM) [] strdupMallocArgSeg)
    (hAInvStableSpill : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < (spM + 8#64).toNat ∨ (spM + 8#64).toNat + 8 ≤ a) →
        σa.mem[a]? = σb.mem[a]?) → M.AInv σa exts → M.AInv σb exts)
    -- memcpy-frame stability (byte-window):
    (hAInvStableFootC : ∀ (σa σb : MState),
      σa.regs.get? Register.x3 = σb.regs.get? Register.x3 →
      (∀ a : Nat, (a < dst.toNat ∨ dst.toNat + (str.length + 1) ≤ a) → σa.mem[a]? = σb.mem[a]?) →
      M.AInv σa extsC → M.AInv σb extsC)
    -- the §2 memcpy bridge residual (its two suppliers documented at its def):
    (hMemcpyBridge : StrdupTailMemcpyBridge SL A gpv headroom M.AInv exts extsC spM spC gm
      M.privFoot (0x8000305c#64) (0x80003070#64) dst src (str.length + 1) (str.length + 1)
      mMalloc mMemcpy bs)
    -- the §3 epilogue entry bundle (prologue frame layout + byte→CString readback):
    (hEpilogueEntry : ∀ (g' : (R : Register) → Option (RegisterType R)) (c : Config),
      memcpy_bytepath_post g' (0x80003070#64) dst (str.length + 1) mMemcpy bs c →
      ∃ lds : List (List (BitVec 8)),
        GHolds c.σ (strdupEpilogueL spC dst) ∧
        ChainFacts c.σ.mem c.σ.mem (strdupEpilogueL spC dst) lds strdupEpilogueSeg ∧
        evalBlocksPC 0x80003070#64 (SegEvalState.init (strdupEpilogueL spC dst) lds)
          strdupEpilogueSeg = rRet ∧
        (writeLog c.σ.mem (evalBlocks strdupEpilogueSeg
          (SegEvalState.init (strdupEpilogueL spC dst) lds)).log = c.σ.mem) ∧
        CString c.σ.mem dst.toNat str) :
    Triple (StrdupTailStrlenEntry SL gpv headroom M.AInv exts spM gm bufPtr str m0)
      (StrdupTailExit rRet str) :=
  stringifyStrdupTailContract M gm str rRet
    bufPtr (0x8000304c#64) m0
    exts (str.length + 1) spM (0x8000305c#64) mMalloc (Nat.le_refl _)
    (0x80003070#64) dst src (str.length + 1) mMemcpy bs
    halignC extsC spC hrouteCbyte hAInvStableFootC
    (calleeFrameStrlen SL gpv headroom M.AInv exts spM gm bufPtr (0x8000304c#64) str m0
      hAInvStableStrlen)
    (strdupTailBridgeStrlenPre_closed SL gpv headroom M.AInv exts spM gm bufPtr str m0
      hAInvStableStrlen)
    (strdupTailBridgeMallocPre_closed SL gpv headroom M.AInv exts spM gm str m0 mMalloc
      hmMalloc hjalmemMalloc hfactsMalloc hAInvStableSpill)
    hMemcpyBridge
    (strdupTailBridgeEpilogue_closed SL gpv headroom M.AInv extsC spC gm
      (0x80003070#64) dst rRet (str.length + 1) mMemcpy bs str rfl hdstne hEpilogueEntry)

#print axioms stringifyStrdupTailContract_closed

end Vsa.Sim
