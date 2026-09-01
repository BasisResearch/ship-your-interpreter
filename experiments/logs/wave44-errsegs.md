# Wave 44 — errsegs lane (M6 decode: the two open exit-path segments)

HEAD 8991fdd (wave 43). Lane: discharge `Crt0ExitSeg` + `MainErrorSeg`
(the two OPEN segments of `errorTailChain_of_segments`, `Vsa/Sim/ExitPath.lean`).

## Decoded spans (from experiments/disasm.txt)

### Crt0ExitSeg (0x80000038 → 0x80000180)
```
80000038: j    80004764 <exit>          -- a0=70; `j` = jal x0 (valid block terminator)
── exit() body ──
80004764: addi sp,sp,-16
80004768: li   a1,0
8000476c: sd   s0,0(sp)
80004770: sd   ra,8(sp)
80004774: mv   s0,a0                    -- s0 := a0 = 70
80004778: jal  __call_exitprocs         -- 800070a8  ── EXTERNAL CALL #1
8000477c: ld   a5,1184(gp)  <__stdio_exit_handler>
80004780: beqz a5,80004788
80004784: jalr a5                        -- stdio flush ── EXTERNAL CALL #2 (conditional)
80004788: mv   a0,s0                     -- a0 := s0 = 70
8000478c: jal  80000180 <_exit>          -- ── CALL #3 → _exit entry 0x80000180
```
`__call_exitprocs` (0x800070a8): NON-trivial — acquires
`__retarget_lock_acquire_recursive`, loads `__atexit` (0x8001b9f8); if null jumps
straight to `__retarget_lock_release_recursive` and returns. Whether `__atexit` is
null at boot is a whole-program data/bss + runtime-registration invariant, NOT
decidable from the span. The stdio-exit-handler `jalr a5` is likewise a
data-dependent indirect call. Both, plus the `jal _exit`, are OPAQUE callee
regions whose bytes/semantics are out of a decode wave's scope.

### MainErrorSeg (0x800045ec → 0x80000038)
```
800045ec: bnez a0,80004600              -- a0=1 TAKEN (block terminator .br BNE true)
── B1 @0x80004600 ──
80004600: ld   a5,0(s0)                 -- s0 = &_impure_ptr
80004604: addi a2,sp,496
80004608: auipc a1,0x15
8000460c: addi a1,a1,-40                -- a1 = &fmt
80004610: ld   a0,24(a5)                -- a0 = stderr FILE*
80004614: jal  800061c0 <fprintf>       -- ── EXTERNAL CALL (output-neutral: stderr ≠ tohost)
── B2 @0x80004618 ──
80004618: li   a0,70                     -- exit status 70
8000461c: j    800045f0                  -- (block .j) → main epilogue
── B3 @0x800045f0 ──
800045f0: ld   ra,760(sp)               -- ra ← main's crt0 link 0x80000038
800045f4: ld   s0,752(sp)
800045f8: addi sp,sp,768
800045fc: ret                            -- jr ra → 0x80000038
```
ONE external call (`jal fprintf`), output-neutral (`FprintfStderrNeutral`).

## Structural verdict (Law 2)
Both spans contain external calls (`fprintf`; `__call_exitprocs`/stdio-handler/
`_exit`) whose forward-simulation is out of scope for a decode wave AND whose
bytes are not pinned in `Code`. Per CLAUDE.md Law 2 a genuine gap is a NAMED
typed premise with a doc comment. So each segment =
`callSeg`(DeriveCallSeg) over: decoded straight-line prefix/suffix
(`bblocks_sound_bt`, mirroring `interpContSeg_of`) + a NAMED callee-neutrality
contract. This is exactly how `ExitPath.lean` itself handles fprintf
(`FprintfStderrNeutral`) and how `errorTailHalts` handles `SnprintfContract`.

## FINAL STATUS
Both open exit-path segments DISCHARGED (conditional on named residuals), axiom-clean
`{propext, Classical.choice, Quot.sound}` on all 5 exported theorems; oleans built;
my 2 files pass check_discipline (the sole gate FAIL is StoreWF.lean, another lane).
SnprintfContract probed (breakdown + observations entry, NOT built).

## Progress
- [x] **Crt0ExitSeg LANDED** — `Vsa/Sim/rows/ErrSegCrt0.lean`, GREEN, axiom-clean
  `[propext, Classical.choice, Quot.sound]`. Structure:
  - `crt0JSeg` = `#derive_case` one-block chain, empty body, `j exit` terminator
    (word 0x72c0406f, imm21 0x0472c). Decodes inline (self-verifying).
  - `crt0ExitPre_of` = ONE `bblocks_sound_bt` over `crt0JSeg`:
    `Triple (AtCrt0Exit out) (AtExitEntry out)`, conditional on `Crt0JFrame`
    (the byte-pins `ChainFacts` residual — NO crt0/`_start` Code module exists,
    so the 4 code bytes @0x80000038 are named; analogue of `InterpContFrame`).
    End PC via `chainEndPC_eq_bt` (NoJr, concrete); a0=70 via `gholds_lookup`;
    output unchanged via `bblocks_sound_bt`'s sailOutput frame.
  - `ExitInteriorNeutral out : Triple (AtExitEntry out) (AtExitProlog out)` =
    NAMED contract for the whole opaque exit() interior (0x80004764→0x80000180):
    `__call_exitprocs` (locked __atexit loop) + optional stdio-handler `jalr a5`
    + `jal _exit`; status a0=70 stashed in s0 and restored, output-neutral.
  - `crt0ExitSeg_of (hframe : Crt0JFrame) (hint : ExitInteriorNeutral) : Crt0ExitSeg out`
    = `Triple.seq (crt0ExitPre_of hframe) hint`.
  Named residuals left: `Crt0JFrame` (byte pins) + `ExitInteriorNeutral` (interior).
- [x] **MainErrorSeg LANDED** — `Vsa/Sim/rows/ErrSegMain.lean`, GREEN, axiom-clean
  `[propext, Classical.choice, Quot.sound]`. Structure = `callSeg`
  (prefix ≫ fprintf ≫ suffix):
  - `mainErrPreSeg` = `#derive_case` 2-block chain (B0 bnez-taken → B1 5-instr
    fprintf-arg body, fall-through to jal-fprintf site 0x80004614). `mainErrPre_of`
    = ONE `bblocks_sound_bt` : `Triple (AtMainRet out) (AtFprintfCall out)`.
    Pin list `preL = [(10,1),(8,s0v),(2,spv)]` (loads read s0; addi reads sp — bases
    pinned as ghosts, domRunM adds each load's rd). End PC 0x80004614 via
    `chainEndPC_eq_bt` (NoJr). Output via bblocks sailOutput frame.
  - `mainErrSufSeg` = HAND-BUILT concrete records `seB2`/`seB3` (li a0,70; j; epilogue;
    jr ra) — NOT `#derive_case`, because the `jr ra` end-PC readback (`srcVal 1`)
    and a0=70 readback need `simp only [seB2,seB3,…]` on concrete TInstr records
    (mkLine-threaded #derive_case bodies get stuck). `mainErrSuf_of` = ONE
    `bblocks_sound_bt` : `Triple (AtMainErrRet out) (AtCrt0Exit out)`. End PC =
    restored ra = 0x80000038 (pinned via sufLds). a0=70 from the li. Pin `sufL=[(2,spv2)]`.
  - `FprintfStderrNeutral out : Triple (AtFprintfCall out) (AtMainErrRet out)` = the
    NAMED output-neutral fprintf contract (stderr FILE* ≠ tohost; exactly the fact
    ExitPath.lean's comment names `FprintfStderrNeutral`).
  - `MainErrFrame out` = the prefix+suffix byte-pin `ChainFacts` residual (from
    `MainLoaded`; main code IS in Code/Main.lean covering 0x800045ec..0x8000461c —
    so this frame is dischargeable, named to bound scope) + the ra-slot pin 0x80000038.
  - `mainErrorSeg_of (hframe : MainErrFrame) (hfp : FprintfStderrNeutral) : MainErrorSeg out`
    = `callSeg (mainErrPre_of hframe) hfp (mainErrSuf_of hframe)`.
  Named residuals: `MainErrFrame` (byte pins, MainLoaded-dischargeable) +
  `FprintfStderrNeutral` (the genuine device-map gap).

GOTCHAS captured:
- `#derive_case terminator` takes a FULL hand `TInstr` `⟨pc,word,b0..b3,kind,rs2,rs1,
  imm13,imm21,imm12⟩`, NOT a `(pc,word)` pair (mkBlock wraps `some $t` verbatim).
- A `/-- -/` doc comment cannot precede `#derive_case` (command, not decl) — use `--`.
- `bblocks_sound_bt` gives `σ'.sailOutput = σ.sailOutput` (needed for output=out);
  `segToTriple` DROPS it — so output-carrying segs must use `bblocks_sound_bt` directly.
- `SrcOK rs1 dom` requires every register READ in a body to be pinned (in dom) or x0;
  domRunM adds each non-store `rd` to dom, so only the initial bases need pinning.
- register-readback via `srcVal`/`lookupG` over a `runChain` needs CONCRETE TInstr
  records (`simp only [blockDefs,…]`); `#derive_case` mkLine bodies get stuck.

## Wiring lines (for coordinator; NOT applied)
Vsa.lean (near the other rows/ErrSeg / ExitPath imports):
  import Vsa.Sim.rows.ErrSegCrt0
  import Vsa.Sim.rows.ErrSegMain
scripts/check_all.sh axiom list:
  Vsa.Sim.crt0ExitSeg_of      # ErrSegCrt0 (Crt0ExitSeg from decoded j-seam + ExitInteriorNeutral; residuals Crt0JFrame + ExitInteriorNeutral)
  Vsa.Sim.mainErrorSeg_of     # ErrSegMain (MainErrorSeg = prefix ≫ FprintfStderrNeutral ≫ suffix; residuals MainErrFrame + FprintfStderrNeutral)

## ErrShared wiring note
`Vsa/Sim/rows/ErrFamilyAssembly.lean`'s `ErrSharedInputs` had `segMain`/`segCrt0`
as OPEN fields (raw `MainErrorSeg out`/`Crt0ExitSeg out`). Those are now SUPPLIED by
`mainErrorSeg_of`/`crt0ExitSeg_of` modulo the smaller residuals (`MainErrFrame` +
`FprintfStderrNeutral` + `Crt0JFrame` + `ExitInteriorNeutral`). Coordinator can
reduce `ErrSharedInputs.segMain`/`.segCrt0` to those 4 named residuals.

## SnprintfContract probe (task 3) — work breakdown

`SnprintfContract` (`Vsa/Sim/JmpSpec.lean:1450`) is a ONE-field structure
(`segment : Triple …`) covering `runtime_error` entry `0x80002da8` → the `jal
longjmp` site `0x8000703c`-post (i.e. through the `jal longjmp` @0x80002df0), with
the load-bearing post = **the jmp_buf `[inp+16, inp+128)` (15 read64 slots)
preserved** + longjmp args set (`a0=inp+16, a1=1`) + `ra` 4-aligned + standing
invariants + blanket `NotWrittenJmp` ghost frame.

Decoded span (`experiments/disasm.txt`, 0x80002da8..0x80002df0):
```
80002da8 addi sp,sp,-224      ┐ prologue (8 instrs, straight-line)
80002dac sd  s0,208(sp)       │  — a #derive_case seg / bblocks_sound_bt
80002db0 sd  s1,200(sp)       │
80002db4 mv  s0,a0            │  s0 := a0 (runtime_error's 1st arg = fmt? / err ctx)
80002db8 mv  s1,a1            │  s1 := a1 (2nd arg)
80002dbc mv  a0,sp           │  a0 := &body scratch
80002dc0 li  a1,192          │  size 192
80002dc4 sd  ra,216(sp)      ┘
80002dc8 jal snprintf         ── CALL #1  snprintf(body, 192, <inherited a2=fmt>, …)
80002dcc li  a1,256          ┐ between-calls marshalling (6 instrs)
80002dd0 mv  a4,sp           │  a4 := &body
80002dd4 mv  a3,s1           │  a3 := s1 (orig a1)
80002dd8 addi a0,s0,224      │  a0 := err_msg = s0+224
80002ddc auipc a2,0x16       │  a2 := &fmt2 (0x80019318)
80002de0 addi a2,a2,1340     ┘
80002de4 jal snprintf         ── CALL #2  snprintf(err_msg, 256, fmt2, s1, body)
80002de8 addi a0,s0,16       ┐ epilogue-to-longjmp (3 instrs)
80002dec li  a1,1            │  a1 := 1
80002df0 jal longjmp          ┘ CALL #3 → 0x8000703c (longjmp; part of the post PC)
```

### Work breakdown (4 pieces)
1. **Prologue seg** (0x80002da8→0x80002dc8): 8 straight-line instrs ending at the
   `jal snprintf` site. `#derive_case`/`bblocks_sound_bt` (~like my prefix). Reads
   sp; writes s0,s1,ra,a0,a1 to stack/regs. FREE-ish (one seg + frame).
2. **snprintf call #1 contract** (@0x80002dc8): `jal snprintf` + whole snprintf body,
   into `body` scratch (a0=sp). The load-bearing property is ONLY that it does NOT
   write the jmp_buf `[inp+16,inp+128)` (disjoint: body is on `sp`, err_msg at s0+224,
   jmp_buf at inp+16 — all disjoint given the frame geometry) and preserves the ghost
   frame. **BLOCKER: the landed `snprintf_lld_spec` (SnprintfSpec42) is SPECIFIC to the
   `"%lld"` format** (`x12 = 0x800192c0` = the %lld .rodata, formats `intToString`).
   runtime_error's call #1 uses the CALLER-INHERITED format (a2 not set in prologue —
   runtime_error(fmt,…) forwards fmt), call #2 uses a fixed non-%lld format 0x80019318.
   So NEITHER call is the %lld specialization. What's needed is a GENERAL
   snprintf FRAME contract: "snprintf(dst, n, fmt, …) terminates, writes only
   `[dst, dst+n)`, preserves everything disjoint + the ghost frame, output-neutral"
   — a MUCH weaker property than `snprintf_lld_spec`'s full byte-exact rendering, but
   NOT currently stated. `snprintf_lld_spec` proves the STRONG rendering for %lld only;
   it does not give a format-generic frame lemma.
3. **Between-calls seg** (0x80002dcc→0x80002de4): 6 straight-line instrs. `#derive_case`.
4. **snprintf call #2 contract** (@0x80002de4) + **epilogue-to-longjmp seg**
   (0x80002de8→0x80002df0 `jal longjmp`): same general-snprintf-frame need as (2),
   then a 2-instr seg + the `jal longjmp` seam (BridgeSeg/jalStep) landing the post PC
   0x8000703c with a0=inp+16, a1=1.

### Verdict
The SnprintfContract is NOT dischargeable from the landed snprintf machinery as-is:
`snprintf_lld_spec` is the %lld byte-exact capstone, but runtime_error needs a
**format-generic snprintf frame/jmp_buf-preservation contract** for TWO calls with
non-%lld formats. Recommended factoring: extract a `SnprintfFrameContract dst n`
(terminates + writes ⊆ [dst,dst+n) + disjoint-preservation + output-neutral + ghost
frame) as a NAMED premise (2 instances), served eventually by generalizing the
snprintf frame reasoning already inside `snprintf_lld_spec`'s residual ledger (the
byte-exact rendering is overkill — only the footprint bound is load-bearing). The 3
decode segs (prologue/between/epilogue) + the `jal longjmp` seam are mechanical
(#derive_case + BridgeSeg). Estimated: 3 segs (~free each) + 1 jal seam +
2× `SnprintfFrameContract` NAMED premises + the jmp_buf-disjointness geometry.
NOT built this wave (out of the errseg decode lane's scope; flagged for the M3 lane).
</content>
