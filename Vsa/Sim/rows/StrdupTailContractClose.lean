import Vsa.Sim.rows.StrdupTailJalSeams
import Vsa.Sim.rows.StrdupEpilogueSeg
import Vsa.Sim.rows.StrcpyContractInhab
import Vsa.Sim.rows.StringifyStrdupTail
import Vsa.Sim.MemcpySpec4
import Vsa.Sim.MemcpySpec
import Vsa.Sim.WriteLogNF

/-!
# `StrdupTailContractClose` — the malloc/memcpy/epilogue bridges + the contract instantiated

Half A of Task #80.  `stringifyStrdupTailContract`
(`Vsa/Sim/rows/StringifyStrdupTail.lean`) composed the shared `stringify` strdup
tail `0x80003044 → 0x80003084` (`strlen ≫ malloc ≫ memcpy ≫ epilogue`) as pure
`callSeg` algebra over the real framed callee contracts, leaving FOUR named
machine-bridge premises.  Wave 32 landed the three `jal` seams
(`strdupTail_{strlen,malloc,memcpy}_run`, `StrdupTailJalSeams.lean`) plus the
frame-carrying `bridgeStrlenPre` wrapper (`strdupTailBridgeStrlenPre_closed`).

This file lands the remaining three bridge wrappers and instantiates the contract.
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
open Vsa.Sim.Code (StringifyLoaded StrlenLoaded)

namespace Vsa.Sim

set_option maxHeartbeats 1600000
set_option maxRecDepth 1000000

/-! ## §1. `bridgeMallocPre` closed — the frame-carrying malloc-staging wrapper

`stringifyStrdupTailContract`'s `bridgeMallocPre` premise takes source `strlen_post
rStrlen str m0 ∧ EnvDefFrame …` (with `rStrlen = 0x8000304c`, the malloc-staging
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
From `strlen_post ∧ EnvDefFrame`, the `addi a2,a0,1 ; mv a0,a2 ; sd a2,8(sp) ; jal
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
        EnvDefFrame SL gpv headroom AInv exts spM gm c)
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

/-! ## §2. `bridgeMemcpyPre` — the OOM-guard + memcpy-staging bridge, named residual

`stringifyStrdupTailContract`'s `bridgeMemcpyPre` takes the malloc-post shape (the
malloc disjunction + the outside-footprint mem-agreement with `mMalloc`) to
`PreDispatch gm rMemcpy dst src nMemcpy mMemcpy bs ∧ EnvDefFrame …`.  The machine
core is `strdupTail_memcpy_run` (`ld a2,8(sp) ; mv s0,a0 ▷ beqz(false) ; mv a1,s1 ;
jal memcpy`, `AbiExceptS0`-framed because `mv s0,a0` reseats `s0`).

**Law-4 residual — TWO genuine gaps this bridge cannot close from the landed
pieces**, both named here rather than assumed away:

1. **The a2-reload.**  `PreDispatch.a2` demands `x12 = ofNat nMemcpy`, read back from
   the `sd a2,8(sp)` spill the malloc-staging wrote into `mMalloc`.  But
   `strdupTail_memcpy_run` runs the seg with `lds = []` — the seg model does NOT
   reconstruct the reloaded size from `mMalloc`'s memory (`ld a2,8(sp)` reads the
   empty loads list, not `mMalloc[spM+8]`).  Closing it needs a `lds`-carrying
   memcpy-staging run whose `lds` head is the spilled-size image, OR a
   `writeLog`/`ld` readback lemma over `mMalloc`.  See
   `experiments/observations.md#strdup-memcpy-a2-reload`.

2. **The NULL-branch exclusion.**  The malloc-post disjunction includes the NULL
   branch (`x10 = 0`), on which the seg's `beqz a0 → 80003140` is TAKEN (to the OOM
   error path, NOT the memcpy entry).  The contract's `bridgeMemcpyPre` target is
   unconditionally `PreDispatch ∧ EnvDefFrame` at the memcpy entry, so it is only
   provable if NULL is excluded — which needs the arena's no-OOM guarantee
   (`nMalloc ≤ maxReq ⇒ malloc ≠ NULL`), a `MallocContract` property the arena
   supplies but the disjunction alone does not.

We NAME the whole bridge as the typed residual `StrdupTailMemcpyBridge` (the exact
`bridgeMemcpyPre` Triple shape parameterised over the contract's ghosts).  Its
suppliers are (1) the a2-reload and (2) the no-OOM exclusion above; everything else
(the staging run, the `AbiExceptS0` frame, `src = s1` marshalling) is the landed
`strdupTail_memcpy_run`. -/

/-- **The strdup-tail `bridgeMemcpyPre` residual** — the exact Triple
`stringifyStrdupTailContract` demands, parameterised over its ghosts.  Suppliers:
the a2-reload (a `lds`-carrying memcpy-staging run) and the arena no-OOM exclusion
(a `MallocContract` non-null guarantee).  Machine core = `strdupTail_memcpy_run`. -/
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
    (fun c => PreDispatch gm rMemcpy dst src nMemcpy mMemcpy bs c ∧
      EnvDefFrame SL gpv headroom AInv extsC spC gm c)

/-! ## §3. `bridgeEpilogue` closed — the `ld ra ; mv a0,s0 ; ret` return + CString readback

`stringifyStrdupTailContract`'s `bridgeEpilogue` takes `(∃ g',
memcpy_bytepath_post g' rMemcpy dst nMemcpy mMemcpy bs) ∧ EnvDefFrame …` to
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

/-- **`bridgeEpilogue` discharged.**  From the memcpy byte-post `∧ EnvDefFrame`, the
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
        EnvDefFrame SL gpv headroom AInv extsC spC gm c)
      (StrdupTailExit rRet str) := by
  intro c hpre
  obtain ⟨⟨g', hbyte⟩, hFrame⟩ := hpre
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

All four bridges are now supplied: `bridgeStrlenPre` = `strdupTailBridgeStrlenPre_closed`
(wave 32), `strlenFramed` = `envDefStrlenFramed`, `bridgeMallocPre` =
`strdupTailBridgeMallocPre_closed` (§1), `bridgeMemcpyPre` = the named residual
`StrdupTailMemcpyBridge` (§2, its two suppliers documented), `bridgeEpilogue` =
`strdupTailBridgeEpilogue_closed` (§3).  The contract HOLDS modulo only the
entry-config supplier `P` and the §2 memcpy-bridge residual (a2-reload + no-OOM). -/

/-- **`stringifyStrdupTailContract` instantiated.**  From the strlen-entry predicate
`StrdupTailStrlenEntry` as `P`, the three landed bridge wrappers, `envDefStrlenFramed`,
and the named `StrdupTailMemcpyBridge` residual, the whole strdup tail reaches
`StrdupTailExit rRet str`.  The memcpy bridge is the ONE remaining machine object
(its suppliers: the a2-reload and the arena no-OOM exclusion, §2). -/
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
    (envDefStrlenFramed SL gpv headroom M.AInv exts spM gm bufPtr (0x8000304c#64) str m0
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
