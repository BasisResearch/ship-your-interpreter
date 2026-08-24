# M3 — the error path: `runtime_error` → `longjmp` → `interp_run` setjmp continuation → diagnostic print → `exit(70)`

Standing brief for the Layer-3/Layer-5 error-path proof agents. Analysis only
(no `.lean` written). Every address, offset, and encoding below is quoted from
`experiments/disasm.txt` (objdump of `c/while-riscv-htif.elf`); where `c/*.c`
and the binary disagree, **the binary wins** — and the two agree everywhere here
except on struct field *offsets* (the C header lays out `on_error` at C-offset 16,
`err_msg` at C-offset 224; the binary confirms both).

Spec idiom follows `experiments/M3-pilot-design.md`: `StepObs` observational
wrappers, a per-function `Ust`/`St` config predicate carrying the **blanket
ghost-frame conjunct** (`hframe : ∀ R, NotWritten R → get? R = g R`), noise
absorbed existentially (`minstret` ∃-bound, `tick < 2`, `mcycle/mtime/mip` never
mentioned), `Triple` composition.

---

## 0. Executive summary

- **jmp_buf layout.** `setjmp`/`longjmp` are newlib RV64 soft-float asm. The
  buffer is **112 bytes**, 15 GPR slots, **no FP / no fcsr**: `ra`@0, `s0`@8,
  `s1`@16, `s2`@24 … `s11`@96, `sp`@104. The buffer is the `on_error` field of
  the `Interp` struct at **struct offset 16** (`&in->on_error == in + 16`); the
  `Interp` itself lives in `main`'s stack frame (`addi a0,sp,272` in `main`), so
  the jmp_buf is a **stack window** `[in+16, in+128)`, not static.
- **Continuation contract.** `longjmp(in->on_error,1)` restores `ra,s0–s11,sp`
  from the buffer and materializes `a0 = (a1==0 ? 1 : a1) = 1`, then `ret`s to
  the saved `ra` — which is `interp_run`'s return address from the original
  `jal setjmp` (`0x80004428`). Execution re-enters interp_run **at the
  instruction after the setjmp call**, `bnez a0, 0x80004508`; since `a0=1` it
  branches to the error handler (zero `call_depth`, set return value `s5=1`, run
  the epilogue, `ret` to `main` with `a0=1`).
- **Diagnostic footprint.** `main` sees interp_run return 1 and calls
  `fprintf(stderr, "%s\n", in->err_msg)`. `fprintf → _vfprintf_r` (**3395
  insts**) → (for the `"%s\n"` format) `__sprint_r → __sfvwrite_r` (311 insts) →
  indirect `__swrite` (34) → `_write_r` (23) → `_write` (12) → one HTIF console
  store per byte. Then `main` `return 70`, crt0 `tail exit`, `exit`
  (`__call_exitprocs`, `__stdio_exit_handler`) → `_exit` → **HTIF exit store**
  `tohost = (70<<1)|1 = 141`; `htif_exit_code = payload>>1 = 70`. This is the
  proven `htif_store_exit` shape (M2). **`_vfprintf_r` at 3395 insts is far too
  large to forward-simulate**, so Layer-5's error simulation must route around
  constraining the diagnostic text (as the plan intends: `Halts c out 70` for
  SOME out).
- **Decode-table gaps (FLAGGED).** The six *core* error-path functions
  (`runtime_error`, `setjmp`, `longjmp`, `interp_run`, `_exit`, `exit`,
  `fprintf`, `_vfprintf_r`, `__sfvwrite_r`, `__sprint_r`, `__call_exitprocs`)
  are **fully covered** by the 8,187-word DecodeTable. But **42 distinct words
  are missing** — from `main`, `_write`, `__swrite`, `_write_r`, and one
  `vfprintf` tail-jump — because `disasm_reachable.py` roots at `interp_run` and
  follows only *direct* `jal`; it skips `main` (above interp_run) and the
  **indirect-`jalr`** write chain (`__swrite`/`_write_r`/`_write`). All 42 are
  ordinary RV64I forms (addi/sd/ld/jal/j/lh/beqz/bnez/auipc/li with distinct
  immediates); none exotic. They must be added to the DecodeTable before the
  exit path proves. Full list in §1.5.
- **Risks.** (a) `_vfprintf_r` and `__sfvwrite_r` *contain* `_malloc_r` call
  sites — but they are on the float/wide-char (`%a`,`%f`,`%ls`) and
  *buffered-stream* branches, **not** taken for unbuffered stderr with a `"%s\n"`
  format. Must be proved unreached, not assumed. (b) `__swrite` reaches
  `_write_r` via an **indirect** `jalr a5` (the FILE's `_write` cookie) in
  `__sfvwrite_r` — needs a decode-table entry + a target-resolution argument.
  (c) stderr must be `__SNBF` (unbuffered) at the fprintf; verify from `__sinit`
  or the `_impure_ptr` stderr flags. Details in §6.

---

## 1. Address maps

Instruction classes use the M2 battery vocabulary: **ALU** (OP/OP-IMM/LUI/AUIPC
incl. `mv`,`li`,`seqz`,`slti`,`sext.w`), **branch** (BRANCH: beq/bne/blt/bge/…,
and pseudo `beqz`/`bnez`/`blez`/`bgeu`), **jump** (JAL/JALR incl. `j`,`jal`,
`jalr`,`ret`,`jr`,`tail`), **load** (LOAD: ld/lw/lh/lbu/…), **store** (STORE:
sd/sw/…). "DT" = present in the 8,187-word DecodeTable (checked against
`reachable_words.txt`).

### 1.1 `runtime_error` — `0x80002da8 … 0x80002df0` (19 insts, DT: all present)

```
80002da8: f2010113  addi sp,sp,-224          ALU    prologue
80002dac: 0c813823  sd   s0,208(sp)          STORE  save s0
80002db0: 0c913423  sd   s1,200(sp)          STORE  save s1
80002db4: 00050413  mv   s0,a0               ALU    s0 = in  (Interp*)
80002db8: 00058493  mv   s1,a1               ALU    s1 = line
80002dbc: 00010513  mv   a0,sp               ALU    a0 = &body[192] (stack)
80002dc0: 0c000593  li   a1,192              ALU    size
80002dc4: 0c113c23  sd   ra,216(sp)          STORE  save ra
80002dc8: 67d020ef  jal  80005c44 <snprintf> JUMP   snprintf(body,192,fmt,a1,a2)
80002dcc: 10000593  li   a1,256              ALU    size = sizeof err_msg
80002dd0: 00010713  mv   a4,sp               ALU    a4 = body
80002dd4: 00048693  mv   a3,s1               ALU    a3 = line
80002dd8: 0e040513  addi a0,s0,224           ALU    a0 = &in->err_msg  (C-off 224)
80002ddc: 00016617  auipc a2,0x16            ALU    fmt hi
80002de0: 53c60613  addi a2,a2,1340          ALU    a2 = 0x80019318 "runtime error [line %d]: %s"
80002de4: 661020ef  jal  80005c44 <snprintf> JUMP   snprintf(err_msg,256,fmt,line,body)
80002de8: 01040513  addi a0,s0,16            ALU    a0 = &in->on_error (C-off 16) = jmp_buf
80002dec: 00100593  li   a1,1                ALU    a1 = 1  (longjmp value)
80002df0: 24c040ef  jal  8000703c <longjmp>  JUMP   longjmp(&in->on_error, 1)  — no return
```

Notes: `runtime_error` never returns (`longjmp` diverts). The two `snprintf`
calls format the message; only the **second** (into `err_msg`) matters for the
observable diagnostic. `err_msg` lives at C-offset 224 (`addi a0,s0,224`),
confirming the header layout after the 112-byte jmp_buf: `globals`@0,
`call_depth`@8, `on_error`@16..127, `err_msg`@224? — no: header has err_msg
right after on_error. The binary's 224 offset means the *compiled* struct pads
`on_error` (declared `jmp_buf` = 112 B) to reach err_msg at 224 (16 + 112 = 128;
padding to 224 implies the compiler's `jmp_buf` typedef is larger than the 112 B
`setjmp` actually writes — newlib's `_JBLEN` reserves extra slots that this
`setjmp` leaves untouched). **The proof only needs: setjmp writes `[in+16,
in+128)`; err_msg starts at `in+224`; the two regions are disjoint.**

### 1.2 `setjmp` — `0x80006ffc … 0x80007038` (16 insts, DT: all present)

```
80006ffc: 00153023  sd   ra,0(a0)      STORE  jb[0]  = ra
80007000: 00853423  sd   s0,8(a0)      STORE  jb[8]  = s0
80007004: 00953823  sd   s1,16(a0)     STORE  jb[16] = s1
80007008: 01253c23  sd   s2,24(a0)     STORE  jb[24] = s2
8000700c: 03353023  sd   s3,32(a0)     STORE  jb[32] = s3
80007010: 03453423  sd   s4,40(a0)     STORE  jb[40] = s4
80007014: 03553823  sd   s5,48(a0)     STORE  jb[48] = s5
80007018: 03653c23  sd   s6,56(a0)     STORE  jb[56] = s6
8000701c: 05753023  sd   s7,64(a0)     STORE  jb[64] = s7
80007020: 05853423  sd   s8,72(a0)     STORE  jb[72] = s8
80007024: 05953823  sd   s9,80(a0)     STORE  jb[80] = s9
80007028: 05a53c23  sd   s10,88(a0)    STORE  jb[88] = s10
8000702c: 07b53023  sd   s11,96(a0)    STORE  jb[96] = s11
80007030: 06253423  sd   sp,104(a0)    STORE  jb[104]= sp
80007034: 00000513  li   a0,0          ALU    return 0  (first passage)
80007038: 00008067  ret                JUMP   ret
```

15 stores + `li a0,0` + `ret`. **No fp stores, no fcsr, no `csrr`.** Confirms
RV64I soft-float. Buffer occupancy = `[a0, a0+112)`.

### 1.3 `longjmp` — `0x8000703c … 0x8000707c` (17 insts, DT: all present)

```
8000703c: 00053083  ld   ra,0(a0)      LOAD   ra  = jb[0]
80007040: 00853403  ld   s0,8(a0)      LOAD   s0  = jb[8]
80007044: 01053483  ld   s1,16(a0)     LOAD   s1  = jb[16]
80007048: 01853903  ld   s2,24(a0)     LOAD   s2  = jb[24]
8000704c: 02053983  ld   s3,32(a0)     LOAD   s3  = jb[32]
80007050: 02853a03  ld   s4,40(a0)     LOAD   s4  = jb[40]
80007054: 03053a83  ld   s5,48(a0)     LOAD   s5  = jb[48]
80007058: 03853b03  ld   s6,56(a0)     LOAD   s6  = jb[56]
8000705c: 04053b83  ld   s7,64(a0)     LOAD   s7  = jb[64]
80007060: 04853c03  ld   s8,72(a0)     LOAD   s8  = jb[72]
80007064: 05053c83  ld   s9,80(a0)     LOAD   s9  = jb[80]
80007068: 05853d03  ld   s10,88(a0)    LOAD   s10 = jb[88]
8000706c: 06053d83  ld   s11,96(a0)    LOAD   s11 = jb[96]
80007070: 06853103  ld   sp,104(a0)    LOAD   sp  = jb[104]
80007074: 0015b513  seqz a0,a1         ALU    a0 = (a1 == 0) ? 1 : 0
80007078: 00b50533  add  a0,a0,a1      ALU    a0 = a0 + a1   (= a1 if a1≠0, else 1)
8000707c: 00008067  ret                JUMP   ret to restored ra
```

Return-value materialization: `seqz a0,a1; add a0,a0,a1` implements the C rule
"`setjmp` returns `val`, or 1 if `val==0`". With `longjmp` arg `a1=1`:
`seqz → a0=0`, `add → a0=1`. **Reads `[a0,a0+112)`; writes `ra,s0–s11,sp,a0`;
redirects PC to the loaded `ra`.**

### 1.4 `interp_run` setjmp region — the relevant segments (103 insts total; DT: all present)

Entry + setjmp call + dispatch + error branch + epilogue (the parts the error
path touches; the statement loop `0x80004458..0x80004504` is normal-path and not
reproduced):

```
--- prologue + jmp_buf address setup ---
800043ec: f5010113  addi sp,sp,-176         ALU    prologue
800043f0: 00a13023  sd   a0,0(sp)           STORE  spill in (Interp*) to 0(sp)
800043f4: 01050513  addi a0,a0,16           ALU    a0 = &in->on_error  (C-off 16)
800043f8: 0a113423  sd   ra,168(sp)         STORE  save ra
800043fc: 0a813023  sd   s0,160(sp)         STORE  save s0
80004400: 08913c23  sd   s1,152(sp)         STORE  save s1
80004404: 09213823  sd   s2,144(sp)         STORE  save s2
80004408: 09313423  sd   s3,136(sp)         STORE  save s3
8000440c: 09413023  sd   s4,128(sp)         STORE  save s4
80004410: 07513c23  sd   s5,120(sp)         STORE  save s5
80004414: 07613823  sd   s6,112(sp)         STORE  save s6
80004418: 00b13c23  sd   a1,24(sp)          STORE  spill stmts
8000441c: 00c13823  sd   a2,16(sp)          STORE  spill count
80004420: 00d13423  sd   a3,8(sp)           STORE  spill repl_mode
--- THE setjmp CALL SITE ---
80004424: 3d9020ef  jal  80006ffc <setjmp>  JUMP   setjmp(&in->on_error); ra_saved = 0x80004428
--- setjmp continuation (BOTH first-return a0=0 and longjmp-return a0=1 land here) ---
80004428: 0e051063  bnez a0,80004508        BRANCH if a0!=0 → error handler (0x80004508)
8000442c: 01013783  ld   a5,16(sp)          LOAD   a5 = count            (first pass, a0=0)
80004430: 00050a93  mv   s5,a0              ALU    s5 = 0  (return-value accumulator)
80004434: 0ef05063  blez a5,80004514        BRANCH if count<=0 → epilogue
   … normal statement loop 0x80004438 … 0x80004504 …
--- ERROR HANDLER (reached only via longjmp, a0=1) ---
80004508: 00013783  ld   a5,0(sp)           LOAD   a5 = in  (reload spilled Interp*)
8000450c: 00100a93  li   s5,1               ALU    s5 = 1  (interp_run returns 1)
80004510: 0007a423  sw   zero,8(a5)         STORE  in->call_depth = 0   (C-off 8)
--- EPILOGUE (shared) ---
80004514: 0a813083  ld   ra,168(sp)         LOAD   restore ra
80004518: 0a013403  ld   s0,160(sp)         LOAD   restore s0
8000451c: 09813483  ld   s1,152(sp)         LOAD   restore s1
80004520: 09013903  ld   s2,144(sp)         LOAD   restore s2
80004524: 08813983  ld   s3,136(sp)         LOAD   restore s3
80004528: 08013a03  ld   s4,128(sp)         LOAD   restore s4
8000452c: 07013b03  ld   s6,112(sp)         LOAD   restore s6
80004530: 000a8513  mv   a0,s5              ALU    a0 = s5  (return value: 1 on error)
80004534: 07813a83  ld   s5,120(sp)         LOAD   restore s5
80004538: 0b010113  addi sp,sp,176          ALU    deallocate frame
8000453c: 00008067  ret                     JUMP   ret to main (0x800045ec)
```

Key: the `jal setjmp` at `0x80004424` saves `ra = 0x80004428`. `longjmp`
restores exactly that `ra` (setjmp wrote it into `jb[0]`), so control resumes at
`0x80004428` `bnez a0` — the **setjmp-return-again point**. First passage has
`a0=0` (setjmp's `li a0,0`), falls through to the normal loop; longjmp passage
has `a0=1`, branches to `0x80004508`.

**Critical subtlety for the continuation contract:** `sp` at `0x80004428` on the
longjmp passage is the value `setjmp` saved into `jb[104]` — which is
interp_run's own `sp` *after* its prologue (`sp = entry_sp - 176`), because
setjmp was called with that sp live. So the error handler's `ld ra,168(sp)` etc.
read interp_run's own saved-register slots correctly; the frame is intact. The
callee-saved regs `s0–s11` at `0x80004428` are whatever `longjmp` loaded from
`jb[8..96]` — i.e. their values *at the setjmp call*, because setjmp saved them
and no intervening code legitimately changed the buffer. So the epilogue restores
`ra,s0–s6,s5` from interp_run's *stack* slots (not the jmp_buf) — the jmp_buf
copies of s0–s6 are immediately overwritten by the epilogue loads, which is fine.

### 1.5 The diagnostic-print + exit path

`main` (`0x80004588`, 46 insts) — error tail only:

```
--- interp_run returned; a0 = 1 ---
800045e8: e05ff0ef  jal  800043ec <interp_run>   JUMP
800045ec: 00051a63  bnez a0,80004600             BRANCH  a0!=0 → error tail
   … (a0==0 success path 0x800045f0..) …
--- ERROR TAIL: fprintf(stderr, "%s\n", in->err_msg); return 70 ---
80004600: 00043783  ld   a5,0(s0)                LOAD   a5 = _impure_ptr
80004604: 1f010613  addi a2,sp,496               ALU    a2 = &in->err_msg (in@sp+272, +224 = sp+496)
80004608: 00015597  auipc a1,0x15                ALU    fmt hi
8000460c: fd858593  addi a1,a1,-40               ALU    a1 = 0x800195e0 = "%s\n"
80004610: 0187b503  ld   a0,24(a5)               LOAD   a0 = _impure_ptr->_stderr (FILE*, off 24)
80004614: 3ad010ef  jal  800061c0 <fprintf>      JUMP   fprintf(stderr,"%s\n",err_msg)
80004618: 04600513  li   a0,70                   ALU    a0 = 70
8000461c: fd5ff06f  j    800045f0                 JUMP   → epilogue → ret 70 to crt0
```

crt0 (`c/src/crt0.S`): `call main` then `tail exit`. So `main`'s `ret` with
`a0=70` lands in `exit`.

`fprintf` (`0x800061c0`, 20 insts, DT: all present): packs varargs into
`32(sp)…`, loads `_impure_ptr`, `jal 0x8000a884 <_vfprintf_r>`, `ret`.

`_vfprintf_r` (`0x8000a884`, **3395 insts**, DT: all present). For the `"%s\n"`
format the taken sub-path is: parse `%s`, call `__sprint_r` to flush the
`%s` argument through the FILE, emit the literal `\n`. The relevant callees on
the `%s` sub-path only:
- `__sprint_r` (`0x…`, 15 insts, DT: all present) → `__sfvwrite_r`.
- `__sfvwrite_r` (`0x8000de8c`, 311 insts, DT: all present).
- `strlen` (measure the `%s` argument).

`_vfprintf_r`'s **other** callees exist in its body but are *not* on the
`"%s\n"` path: `__eqdf2 __ledf2 __gedf2 __unorddf2 __muldf3 __subdf3 __trunctfdf2
__floatsidf __fixdfsi frexp _dtoa_r` (float `%f/%g/%e/%a`), `_wcsrtombs_r
_wcrtomb_r` (wide `%ls`), and **`_malloc_r`/`_free_r`** (at `0x8000c97c`,
`0x8000d020` — the `_dtoa_r` / grouping buffers). See §6 risk (a).

`__sfvwrite_r` write dispatch (`0x8000de8c`): tests FILE flags —
`andi a5,a3,8` (`__SNBF`, unbuffered, `0x8000deac`) and `andi a5,a3,2`
(`__SLBF`, line-buffered, `0x8000ded8`). For **unbuffered stderr** it takes the
`jalr a5` direct-write branch at `0x8000df1c` (calls the FILE's `_write` cookie
= `__swrite`), **bypassing** the buffered path's `_malloc_r` (`0x8000e02c`) /
`memmove` / `memcpy` code.

Indirect write cookie → `__swrite` (`0x8000efd4`, 34 insts, DT: **10 words
missing**) → (`j 0x800104fc`) `_write_r` (`0x800104fc`, 23 insts, DT: **1 word
missing**) → `jal 0x8000003c` `_write`:

`_write` (`0x8000003c`, 12 insts, DT: **6 words missing** — see below) — the
HTIF console loop:

```
8000003c: 02060463  beqz a2,80000064          BRANCH  len==0 → done
80000040: 10100713  li   a4,257               ALU     a4 = 0x101
80000044: 00c586b3  add  a3,a1,a2             ALU     a3 = buf+len (end)
80000048: 03071713  slli a4,a4,0x30           ALU     a4 = (DEV_CONSOLE|CMD_WRITE)=0x0101<<48
8000004c: 0005c783  lbu  a5,0(a1)             LOAD    a5 = *p
80000050: 00158593  addi a1,a1,1              ALU     p++
80000054: 00e7e7b3  or   a5,a5,a4             ALU     a5 = cmd | byte
80000058: 0001b817  auipc a6,0x1b             ALU     tohost hi
8000005c: caf83423  sd   a5,-856(a6)          STORE   *tohost = a5  → 0x8001ad00  (HTIF console store)
80000060: fed596e3  bne  a1,a3,8000004c       BRANCH  loop until p==end
80000064: 00060513  mv   a0,a2                ALU     return len
80000068: 00008067  ret                       JUMP
```

Each iteration is **one 8-byte HTIF console store** `tohost = 0x0101_0000_0000_00XX`
(device 1, cmd 1, byte XX). This is the byte-at-a-time output; the Layer-0 HTIF
console lemma (sibling of `htif_store_exit`, M2 §"htif_putc") characterizes it.

`exit` (`0x80004764`, 11 insts, DT: all present):

```
80004764: ff010113  addi sp,sp,-16
80004768: 00000593  li   a1,0
8000476c: 00813023  sd   s0,0(sp)
80004770: 00113423  sd   ra,8(sp)
80004774: 00050413  mv   s0,a0                a0 = 70 (exit code) → s0
80004778: 131020ef  jal  800070a8 <__call_exitprocs>   run atexit handlers
8000477c: 4a01b783  ld   a5,1184(gp) # __stdio_exit_handler
80004780: 00078463  beqz a5,80004788          BRANCH  if handler==0 skip
80004784: 000780e7  jalr a5                    JUMP    call __stdio_exit_handler (indirect)
80004788: 00040513  mv   a0,s0                ALU     a0 = 70
8000478c: 9f5fb0ef  jal  80000180 <_exit>      JUMP    _exit(70)
```

`__call_exitprocs` (`0x800070a8`, 92 insts, DT: all present). `while-riscv-htif`
registers no atexit handlers from user code; `__atexit` list may be empty ⇒
early return (`beqz s2, 0x8000717c`). `__stdio_exit_handler` may be NULL (only
set by `__sinit` if stdio was used with buffering); if set it flushes streams
(another `_fflush_r → __sfvwrite → __swrite → _write` chain — but stderr already
flushed, stdout unbuffered ⇒ nothing to write). See §6 risk (d).

`_exit` (`0x80000180`, 6 insts, DT: all present) — **the HTIF exit store**:

```
80000180: 02051713  slli a4,a0,0x20           ALU    a4 = code << 32
80000184: 01f75793  srli a5,a4,0x1f           ALU    a5 = (code<<32)>>31 = code<<1
80000188: 0017e793  ori  a5,a5,1              ALU    a5 = (code<<1)|1
8000018c: 0001b717  auipc a4,0x1b             ALU    tohost hi
80000190: b6f73a23  sd   a5,-1164(a4)         STORE  *tohost = (code<<1)|1  → 0x8001ad00
80000194: 0000006f  j    80000194             JUMP   spin (never returns)
```

For `code=70`: `a5 = (70<<1)|1 = 141 = 0x8d`. Store to `tohost` (0x8001ad00).
Per M2 `htif_store_exit`: `htif_done := true`, `htif_exit_code := payload>>1 =
141>>1 = 70`, and `stepOnce` returns `.inl (some 70, used+1)` ⇒
**`Machine.Halts c out 70`**. The final `j .` self-loop is never fetched because
the exit store already terminated the machine on that step.

### 1.5.1 Missing DecodeTable words (42 distinct) — FLAGGED GAP

Cause: `disasm_reachable.py` roots at `interp_run`, follows only direct `jal`;
`main` is a *caller* of interp_run (above it) and `_write`/`__swrite`/`_write_r`
are reached via the **indirect `jalr a5`** in `__sfvwrite_r`, so none entered the
closure. All 42 are standard RV64I; add to DecodeTable before proving the exit
path. By function:

- **`main`** (25): `d0010113 addi sp,-768` · `2e813823 sd s0,752(sp)` ·
  `46018413 addi s0,gp,1120` · `2e113c23 sd ra,760(sp)` · `314010ef jal setvbuf`
  · `11010513 addi a0,sp,272` · `d55ff0ef jal interp_init` · `00c10593` ·
  `10000693` · `61c50513` · `00012623 sw zero,12(sp)` · `874fe0ef jal
  parse_program` · `00c12603 lw a2,12(sp)` · `e05ff0ef jal interp_run` ·
  `2f813083 ld ra,760(sp)` · `2f013403` · `30010113 addi sp,768` · `1f010613
  addi a2,sp,496` · `fd858593 addi a1,-40` · `3ad010ef jal fprintf` · `04600513
  li a0,70` · `fb858593 addi a1,-72` · `38d010ef jal fprintf` · `04100513 li
  a0,65`. (The `0x800045e8 jal interp_run` word and the two `fprintf` words are
  the load-bearing ones for the error tail.)
- **`_write`** (6): `02060463 beqz a2,+0x28` · `10100713 li a4,257` ·
  `00c586b3 add a3,a1,a2` · `0001b817 auipc a6,0x1b` · `caf83423 sd a5,-856(a6)`
  (the console store) · `fed596e3 bne a1,a3,-…` (loop). **All load-bearing.**
- **`__swrite`** (10): `01059783 lh` · `00068313 mv t1,a3` · `1007f693 andi
  a3,a5,256` · `00060893 mv a7,a2` · `02069863 bnez` · `01271583 lh a1,18(a4)` ·
  `00088613 mv a2,a7` · `4dc0106f j _write_r` · `404010ef jal _lseek_r` ·
  `01071783 lh a5,16(a4)`.
- **`_write_r`** (1): `b1def0ef jal _write`.
- **`vfprintf`** wrapper (1): `ae1fc06f j _vfprintf_r` (the thin `vfprintf`
  entry at 0x8000dd90 — not on main's path, main uses `fprintf`; include only if
  a caller uses `vfprintf`).

No missing word is an unusual opcode; each is `addi/sd/ld/lh/lw/sw/jal/j/auipc/
li/mv/beqz/bnez/add/andi/srli/slli/ori` with a distinct 32-bit encoding.
Regenerate the table over the union `reachable-from-interp_run ∪ {main, _write,
__swrite, _write_r}` (and `vfprintf` if needed).

---

## 2. The jmp_buf layout (authoritative, from the binary)

| slot | offset (bytes) | setjmp store (§1.2) | longjmp load (§1.3) | register |
|------|----------------|---------------------|---------------------|----------|
| 0 | 0   | `sd ra,0(a0)`   | `ld ra,0(a0)`   | `ra`  (x1)  |
| 1 | 8   | `sd s0,8(a0)`   | `ld s0,8(a0)`   | `s0`  (x8/fp) |
| 2 | 16  | `sd s1,16(a0)`  | `ld s1,16(a0)`  | `s1`  (x9)  |
| 3 | 24  | `sd s2,24(a0)`  | `ld s2,24(a0)`  | `s2`  (x18) |
| 4 | 32  | `sd s3,32(a0)`  | …               | `s3`  (x19) |
| 5 | 40  | `sd s4,40(a0)`  | …               | `s4`  (x20) |
| 6 | 48  | `sd s5,48(a0)`  | …               | `s5`  (x21) |
| 7 | 56  | `sd s6,56(a0)`  | …               | `s6`  (x22) |
| 8 | 64  | `sd s7,64(a0)`  | …               | `s7`  (x23) |
| 9 | 72  | `sd s8,72(a0)`  | …               | `s8`  (x24) |
| 10| 80  | `sd s9,80(a0)`  | …               | `s9`  (x25) |
| 11| 88  | `sd s10,88(a0)` | …               | `s10` (x26) |
| 12| 96  | `sd s11,96(a0)` | …               | `s11` (x27) |
| 13| 104 | `sd sp,104(a0)` | `ld sp,104(a0)` | `sp`  (x2)  |

- **Total written: 112 bytes** `[jb, jb+112)` = slots 0..13. **No FP registers,
  no `fcsr`, no `mstatus`/CSR** are saved — this is newlib's RV64 **soft-float**
  `setjmp`. (The soft-float ABI has no callee-saved fs* registers to preserve;
  had it been hard-float, newlib would `fsd fs0..fs11` after the GPRs. Absent
  here — confirmed by the pure `sd`/`ld` sequences.)
- **Not saved: `gp`, `tp`** (ABI-fixed, never restored), the temporaries/args
  `t*`/`a*` (caller-saved), and the tick/CSR machine state (irrelevant — GoodState
  pins it and longjmp doesn't touch it).
- **Buffer address = `&in->on_error` = `in + 16`.** `in` (the `Interp*`) is
  `main`'s stack-local (`addi a0,sp,272` in `main`, `in @ main_sp+272`), so the
  jmp_buf is a **stack window** `[main_sp+288, main_sp+400)`. Both setjmp
  (`0x800043f4 addi a0,a0,16`) and runtime_error (`0x80002de8 addi a0,s0,16`)
  compute the same address from their respective `Interp*` in `a0`/`s0`.
- **`err_msg` is at `in + 224`** (`addi a0,s0,224` in runtime_error,
  `addi a2,sp,496 = (main_sp+272)+224` in main), disjoint from the jmp_buf
  window `[in+16, in+128)`. The gap `[in+128, in+224)` is `jmp_buf` typedef
  padding (`_JBLEN` slots setjmp leaves untouched) — irrelevant to the proof.

### Restore + return-value materialization (longjmp)

`longjmp(jb, a1=1)`: loads `ra,s0–s11,sp` from `jb`, then
`seqz a0,a1; add a0,a0,a1` ⇒ `a0 = (a1==0) ? 1 : a1`. With `a1=1` ⇒ `a0=1`.
`ret` jumps to the restored `ra = 0x80004428` (interp_run's post-setjmp PC).

---

## 3. The setjmp-continuation contract

State that holds at the **return-again point** `0x80004428` (`bnez a0, …`) on the
longjmp passage (`a0=1`):

- **PC = `0x80004428`.** (Restored `ra` from `jb[0]`, which setjmp wrote as
  `0x80004428` = address after `jal setjmp`.)
- **`a0 = 1`.** (`longjmp`'s materialization; drives `bnez` taken → error
  handler `0x80004508`.)
- **`sp = jb[104]` = interp_run's post-prologue sp** (`entry_sp − 176`). This is
  the value setjmp captured, so interp_run's own saved-register slots
  (`168(sp)…112(sp)` and the `0(sp)` Interp* spill) are addressable and hold the
  values interp_run stored in its prologue. **The frame is fully intact.**
- **`ra,s0–s11` = jb copies** (their values at the setjmp call). The error
  handler + epilogue immediately reload `ra,s0–s6,s5` from interp_run's *stack*
  slots (`0x80004514…`), so the jb copies of s0–s6/s5 don't matter; **s7–s11 and
  s3–s4** flow through unchanged from the jb (interp_run does restore s2,s3,s4 in
  the epilogue too — see `0x80004520/24/28`; s7–s11 are neither saved by
  interp_run nor used ⇒ their jb values = caller's values, correctly preserved
  end-to-end). Net: **all callee-saved registers are restored to their values at
  interp_run entry** — matching the plan's contract "callee-saved registers
  restored".
- **Memory:** the jmp_buf window `[in+16,in+128)` was written by setjmp and read
  by longjmp; `err_msg` `[in+224, in+480)` was written by the two `snprintf`s in
  `runtime_error`; nothing else on the buffer changed.

**Error dispatch on the nonzero return:** `bnez a0, 0x80004508`. At `0x80004508`:
`ld a5,0(sp)` reloads `in` (spilled at prologue `sd a0,0(sp)`), `li s5,1`
(interp_run return value = 1), `sw zero,8(a5)` sets `in->call_depth = 0`
(C-offset 8, the `call_depth` field — matches C `in->call_depth = 0`), then falls
into the shared epilogue `0x80004514` which restores callee-saveds, `mv a0,s5`
(a0=1), and `ret`s to main. **interp_run returns 1.** Contrast the first passage
(`a0=0`): `bnez` not taken, `mv s5,a0` (s5=0), run the statement loop.

---

## 4. The diagnostic-print + exit(70) path (call chain + footprint)

```
interp_run error branch  → returns a0=1 to main (0x800045ec)
main 0x80004600:  fprintf(stderr, "%s\n", in->err_msg)          [scope: newlib]
  fprintf 0x800061c0 (20)   → _vfprintf_r 0x8000a884 (3395)
    _vfprintf_r  "%s\n" path → strlen (measure arg)
                              → __sprint_r (15) → __sfvwrite_r 0x8000de8c (311)
      __sfvwrite_r (unbuffered stderr) → jalr a5 = __swrite 0x8000efd4 (34)
        __swrite → (j) _write_r 0x800104fc (23) → (jal) _write 0x8000003c (12)
          _write → per-byte HTIF console store  tohost = 0x0101<<48 | byte  (0x8001ad00)
main 0x80004618:  a0 = 70;  j epilogue;  ret 70 → crt0 `tail exit`
  exit 0x80004764 (11) → __call_exitprocs 0x800070a8 (92)   [likely empty list]
                       → [__stdio_exit_handler if set: flush → (nothing to write)]
                       → _exit 0x80000180 (6)
                           → HTIF EXIT store  tohost = (70<<1)|1 = 141  (0x8001ad00)
                             ⇒ htif_exit_code = 70 ⇒ Halts c out 70
```

### Footprint (decides Layer-5 strategy)

| function | insts | on `%s\n` path? | note |
|---|---|---|---|
| `main` (error tail) | ~7 | yes | above interp_run; not in `Loaded` scope but on the Layer-5 sim |
| `fprintf` | 20 | yes | thin wrapper |
| **`_vfprintf_r`** | **3395** | yes (small sub-slice) | **too large to simulate in full** |
| `__sprint_r` | 15 | yes | |
| `__sfvwrite_r` | 311 | yes (unbuffered slice) | float/buffered branches skipped |
| `strlen` | ~10 | yes | already spec'd (Layer-3 `strlen_spec`) |
| `__swrite` | 34 | yes | 10 DT words missing |
| `_write_r` | 23 | yes | 1 DT word missing |
| `_write` | 12 | yes | 6 DT words missing; per-byte HTIF store loop |
| `exit` | 11 | yes | |
| `__call_exitprocs` | 92 | yes | likely early-exits (empty atexit) |
| `_exit` | 6 | yes | HTIF exit store |

`_vfprintf_r`'s 3395 instructions make **whole-function forward simulation
infeasible** for Layer 5. Two viable routings, both consistent with the plan's
"`Halts c out 70` for SOME out (text unconstrained)":

1. **Route around output entirely (recommended).** Layer 5 need not simulate the
   diagnostic *content*. Prove only that (a) from the setjmp-error branch,
   interp_run returns 1; (b) main reaches the `exit(70)` call *regardless of what
   fprintf writes*, i.e. fprintf terminates and returns (it does — no infinite
   loops on a bounded string), leaving `out` = "entry output ++ some string";
   (c) `_exit` performs the HTIF exit store ⇒ `Halts c out 70`. This requires a
   **`fprintf`/`_vfprintf_r` termination + output-monotonicity spec**
   (`vfprintf_spec`: from a well-formed FILE and a valid format+args, it runs to
   `ret` in finitely many steps, `output` only grows, memory outside its scratch
   is preserved) — proved *once*, existentially over the emitted bytes. The
   3395-inst body is verified as **termination + frame**, never as
   character-exact output. This still needs the DT gap closed (write chain) but
   avoids constraining text.

2. **Full simulation (not recommended).** Verify `_vfprintf_r` character-exact
   for the `"%s\n"` case. ~3.7k insts of newlib format-dispatch; disproportionate
   for a deliberately-unconstrained diagnostic.

**Recommendation: routing (1).** It matches the plan ("diagnostics contain line
numbers the deep embedding doesn't carry") and keeps the 3395-inst body out of
the character-exact proof. The **only** character-exact obligation on the exit
path is the single `_exit` HTIF store (already `htif_store_exit`).

---

## 5. Proposed Lean spec shapes (statements only)

Idiom: `M3-pilot-design.md` — `Triple`, `Ust`/`St` config predicate with the
blanket ghost-frame `hframe`, `StepObs` steps, `tick < 2`, `minstret` ∃-bound.
`P`/`Q` name exactly the memory regions read/written. Written but not shown:
`NotWritten` abbrevs per function.

### 5.1 `longjmp_spec`

`longjmp` reads the 112-byte jmp_buf, writes `ra,s0–s11,sp,a0`, redirects PC.
Parameterize by the buffer address `jb`, its 14 stored values, the longjmp arg
`v`, and pinned memory `m0`.

```
-- jb : BitVec 64  (address of jmp_buf, = in+16)
-- saved : slot → value :  ra0 s0v s1v … s11v spv   (14 ghost values)
-- v : BitVec 64  (a1, the longjmp value; here v = 1)
-- m0 : Mem       (pinned; longjmp writes NO memory)
-- g : ghost frame (registers at entry)

def longjmp_pre (jb : BitVec 64) (ra0 … spv : BitVec 64) (v m0 g) (c) : Prop :=
  GoodState c.σ ∧ CodeLoadedLongjmp c.σ ∧ c.σ.mem = m0 ∧
  PC c = 0x8000703c ∧ x10 c = jb ∧ x11 c = v ∧ c.tick < 2 ∧
  (∃ n, minstret c = some n) ∧
  -- jmp_buf holds the saved values (read-set):
  Reads8 m0 (jb+0) ra0 ∧ Reads8 m0 (jb+8) s0v ∧ … ∧ Reads8 m0 (jb+104) spv ∧
  (∀ R, NotWrittenLongjmp R → c.σ.regs.get? R = g R)

def longjmp_post (jb ra0 … spv v m0 g) (c) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧                         -- no stores
  PC c = ra0 ∧                                           -- ret to restored ra
  x1 c = ra0 ∧ x8 c = s0v ∧ x9 c = s1v ∧ … ∧ x27 c = s11v ∧ x2 c = spv ∧
  x10 c = (if v = 0 then 1 else v) ∧                     -- materialized return
  c.tick < 2 ∧ (∃ n, minstret c = some n) ∧
  (∀ R, NotWrittenLongjmp R → c.σ.regs.get? R = g R)

theorem longjmp_spec : Triple (longjmp_pre jb ra0 … spv v m0 g)
                              (longjmp_post jb ra0 … spv v m0 g)
```

`NotWrittenLongjmp` = complement of `{x1,x8,x9,x18..x27,x2,x10, PC,nextPC,
minstret,minstret_increment,mcycle,mtime,mip}`. Reads: `[jb, jb+112)`. Writes:
none to memory.

### 5.2 `setjmp_spec` (the initial 0-return passage inside interp_run)

Two roles. For Layer-4 (normal path) the relevant fact is the **0-return
passage**: setjmp writes the 14 slots and returns `a0=0`. (The return-again
passage is *not* a call of setjmp — it's longjmp's `ret`; covered by
`longjmp_spec` + the interp_run dispatch, §5.4.)

```
-- jb : buffer address (= in+16).  vals : the live ra,s0..s11,sp at the call.
def setjmp_pre (jb ra0 … spv m0 g) (c) : Prop :=
  GoodState c.σ ∧ CodeLoadedSetjmp c.σ ∧ c.σ.mem = m0 ∧
  PC c = 0x80006ffc ∧ x10 c = jb ∧
  x1 c = ra0 ∧ x8 c = s0v ∧ … ∧ x27 c = s11v ∧ x2 c = spv ∧
  WritableWindow m0 jb 112 ∧                     -- jb..jb+112 in RAM, disjoint from code/tohost
  c.tick < 2 ∧ (∃ n, minstret c = some n) ∧
  (∀ R, NotWrittenSetjmp R → c.σ.regs.get? R = g R)

def setjmp_post (jb ra0 … spv m0 g) (c) : Prop :=
  GoodState c.σ ∧ PC c = ra0 ∧ x10 c = 0 ∧       -- returns 0 on the initial passage
  -- memory: exactly the 14 slots updated, else = m0
  c.σ.mem = writeBuf m0 jb [ra0, s0v, s1v, …, s11v, spv] ∧
  Reads8 c.σ.mem (jb+0) ra0 ∧ … ∧ Reads8 c.σ.mem (jb+104) spv ∧
  c.tick < 2 ∧ (∃ n, minstret c = some n) ∧
  (∀ R, NotWrittenSetjmp R → c.σ.regs.get? R = g R)

theorem setjmp_spec : Triple (setjmp_pre jb ra0 … spv m0 g)
                            (setjmp_post jb ra0 … spv m0 g)
```

`NotWrittenSetjmp` = complement of `{x10, PC,nextPC,minstret,…tick regs}` (setjmp
writes only `a0` among GPRs; `ra,s0–s11,sp` are *read*, unchanged). Writes memory
`[jb, jb+112)`. The post exposes `writeBuf … = the exact values longjmp will
later read`, tying `setjmp_post` to `longjmp_pre`'s `Reads8` conjuncts.

### 5.3 `runtime_error_spec`

`runtime_error` calls two `snprintf`s (into `body`@sp and `err_msg`@in+224) then
`longjmp(&in->on_error, 1)`. Since it never returns, its spec is a **transfer
triple**: from entry it reaches (via longjmp) interp_run's `0x80004428` with a0=1
and callee-saveds restored to their setjmp-time values. The plan's phrasing
"transfers control to interp_run's setjmp continuation with callee-saved
registers restored".

```
-- in : Interp* ;  the jmp_buf at in+16 was populated by interp_run's setjmp
--   with saved values ra0=0x80004428, s0v…s11v = interp_run's live callee-saveds, spv.
def runtime_error_pre (in ra0 s0v … s11v spv m0 g) (c) : Prop :=
  GoodState c.σ ∧ CodeLoadedRuntimeError c.σ ∧ CodeLoadedSnprintf c.σ ∧
  CodeLoadedLongjmp c.σ ∧
  PC c = 0x80002da8 ∧ x10 c = in ∧               -- a0 = Interp*, a1 = line, a2 = fmt, …
  -- jmp_buf at in+16 holds the setjmp continuation (populated earlier):
  Reads8 c.σ.mem (in+16+0) 0x80004428 ∧ Reads8 c.σ.mem (in+16+8) s0v ∧ … ∧
  Reads8 c.σ.mem (in+16+104) spv ∧
  WritableWindow c.σ.mem (in+224) 256 ∧           -- err_msg scratch (written by snprintf)
  DisjointWindows (in+16) 112 (in+224) 256 ∧
  ScratchStack c … ∧                              -- body[192] on runtime_error's own frame
  c.tick < 2 ∧ (∃ n, minstret c = some n)

def runtime_error_post (in ra0 s0v … s11v spv m0 g) (c) : Prop :=
  -- lands at interp_run's return-again point, error side
  GoodState c.σ ∧ PC c = 0x80004428 ∧ x10 c = 1 ∧
  x1 c = 0x80004428 ∧ x8 c = s0v ∧ … ∧ x27 c = s11v ∧ x2 c = spv ∧
  -- memory: err_msg region updated (content NOT pinned), jmp_buf preserved, else old
  MemChangedOnly c.σ.mem m0 (in+224) 256 ∧        -- Q leaves err_msg bytes existential
  c.tick < 2 ∧ (∃ n, minstret c = some n)

theorem runtime_error_spec : Triple (runtime_error_pre …) (runtime_error_post …)
```

Honest P/Q memory footprint: **reads** the jmp_buf `[in+16, in+128)`; **writes**
`err_msg [in+224, in+480)` (content left unconstrained via `MemChangedOnly`) and
`body[192]` on its own stack frame. It composes with `longjmp_spec` (the tail
`jal longjmp` at `0x80002df0`) — the longjmp reads the jmp_buf conjuncts the pre
pins. The `snprintf` internals are absorbed by an `snprintf_spec` that (like the
plan's `intToString`) guarantees termination + `err_msg` in-bounds + frame; the
error path does **not** constrain the formatted string.

### 5.4 interp_run dispatch + `vfprintf_spec` (routing-around, §4.1)

For Layer 5 the composed error derivation needs:
- `interp_run_error_spec`: `Triple` from `0x80004428` with `a0=1` → interp_run
  `ret`s `a0=1` with `in->call_depth=0` and callee-saveds restored (the §1.4
  error handler + epilogue; ~11 insts, pure ALU/load/store/branch/jump).
- `vfprintf_spec` (**termination + monotone-output + frame**, NOT character-exact):
  ```
  theorem vfprintf_spec :
    Triple (vfprintf_pre file fmt args m0 g)          -- well-formed FILE (unbuffered),
                                                        -- valid fmt+args, scratch stack
           (fun c => GoodState c.σ ∧ PC c = ret_addr ∧ -- returns to caller
                     (∃ emitted, Machine.output c.σ = out0 ++ emitted) ∧  -- SOME text
                     FrameOutsideScratch c.σ.mem m0 ∧ c.tick < 2)
  ```
  Existential `emitted` is the whole point — the diagnostic text is unconstrained.
- `exit_spec` / `_exit_spec`: composes `__call_exitprocs` (empty-list early
  return) → `_exit` HTIF store ⇒ `Halts c out 70` via `htif_store_exit`.

---

## 6. Risks / blockers

**(a) `_vfprintf_r`/`__sfvwrite_r` contain `_malloc_r` call sites.**
`_vfprintf_r` calls `_malloc_r` at `0x8000c97c` and `0x8000d020` (the `_dtoa_r`
and digit-grouping scratch, on `%f/%g/%e/%a` and grouping paths).
`__sfvwrite_r` calls `_malloc_r` at `0x8000e02c` (buffered-stream growth). **For
the error path the format is `"%s\n"` and stderr is unbuffered**, so *neither*
malloc site is reached. But this is not free: the routing-around `vfprintf_spec`
must **prove the malloc branches unreachable** for this format+FILE, or the
Layer-2 malloc hypothesis leaks into the error path. Mitigation: the `%s`
sub-path is a small, decidable slice of `_vfprintf_r`'s dispatch; the
unbuffered-stderr flag test (`andi …,8` at `0x8000deac`) selects the direct-write
branch by `decide` once the FILE flags are pinned. **Action: pin `stderr._flags`
(the `__SNBF` bit) in `vfprintf_pre`; prove the float/buffered edges dead.**

**(b) Indirect `jalr a5` to the write cookie.** `__sfvwrite_r` calls the FILE's
`_write` function via `jalr a5` (`0x8000df1c`, also `0x8000e12c`, `0x8000e24c`),
where `a5` = `FILE->_write` = `&__swrite`. This is one of the 18 `indirect_sites`
in `disasm_reachable.json`. **Needs (i) the `jalr` word in the DecodeTable
[present — `000780e7` is covered], and (ii) a target-resolution lemma** proving
`FILE->_write == 0x8000efd4` from the pinned FILE object (set by `__sinit`).
Similar `jalr a5` in `exit` (`0x80004784`) for `__stdio_exit_handler`.

**(c) DecodeTable gap: 42 words (§1.5.1).** The reachability tool missed `main`
(caller of interp_run) and the indirect write chain `_write/__swrite/_write_r`.
All 42 are ordinary RV64I; **blocker until regenerated.** Fix: extend
`disasm_reachable.py`'s roots to include `main` and resolve the 18
`indirect_sites` targets (esp. `__swrite`), then re-run `gen_decode_table.py`.
Until then, no exit-path triple type-checks (missing `decode_<word>` lemmas).

**(d) `exit` → `__call_exitprocs` / `__stdio_exit_handler`.** `__call_exitprocs`
(92 insts) walks the `__atexit` list; `while-riscv-htif` registers no user
atexit handlers, so the list should be empty ⇒ early return (`beqz s2,
0x8000717c`). **Verify `__atexit` head is NULL at exit** (it is unless
`register_fini`/`atexit` ran — `register_fini` at `0x80007090` has `li a5,0;
beqz a5` ⇒ no-op in this build). `__stdio_exit_handler` (a `jalr` indirect) is
set by `__sinit` to `_cleanup_r` (flush all streams) *if* stdio initialized.
Since main used stdio (setvbuf/fprintf), `__sinit` ran ⇒ handler likely non-NULL
⇒ it flushes stdout/stderr. **Both are unbuffered/already-flushed**, so the flush
writes nothing new — but this adds another `_fflush_r → __sfvwrite_r` traversal
that the exit spec must show is output-neutral (empty write). Not a correctness
threat, but extra footprint. Mitigation: `exit_spec` proves the flush emits zero
bytes (unbuffered FILEs have `_p == _bf._base`, nothing to flush).

**(e) setjmp/longjmp buffer aliasing with `err_msg`.** Proved disjoint (§2):
jmp_buf `[in+16, in+128)`, err_msg `[in+224, in+480)`. The `runtime_error`
`snprintf` into err_msg cannot clobber the jmp_buf, so `longjmp`'s reads are
valid. `DisjointWindows` conjunct in `runtime_error_pre` discharges this by
`decide` on the concrete offsets. **No aliasing risk** given the layout facts.

**(f) No fcsr/FP saved — confirmed safe.** setjmp saves no `fcsr` and no fs*
registers (§1.2, §2). Soft-float build ⇒ nothing to restore ⇒ `longjmp` correctly
reconstitutes the continuation with 14 GPR slots only. **Not a risk** (was a
flagged unknown; resolved: no FP state).

**(g) `sp` restore correctness.** longjmp restores `sp = jb[104]` =
interp_run's post-prologue sp. Because `runtime_error` and its snprintf callees
run on their *own* deeper frames (below interp_run's sp), restoring interp_run's
sp discards those frames wholesale — standard longjmp semantics, sound. The
proof must carry that interp_run's stack slots `[sp, sp+176)` still hold the
prologue-saved values at the return-again point (nothing between setjmp and the
error overwrote interp_run's own frame — the intervening exec_stmt/eval_expr
calls used deeper frames). **Encode as a stack-frame-preserved invariant across
the error subtree** (Layer-4/5 obligation, not a per-function spec).

---

## Appendix — quick address index

| symbol | addr | insts | DT | role |
|---|---|---|---|---|
| `runtime_error` | 0x80002da8 | 19 | ok | snprintf×2 + longjmp(1) |
| `setjmp` | 0x80006ffc | 16 | ok | save ra,s0–s11,sp; ret 0 |
| `longjmp` | 0x8000703c | 17 | ok | restore; a0=(v?v:1); ret |
| `interp_run` | 0x800043ec | 103 | ok | setjmp@0x424, dispatch@0x428, err@0x508 |
| `main` | 0x80004588 | 46 | **25 miss** | fprintf err tail @0x4600, ret 70 |
| `fprintf` | 0x800061c0 | 20 | ok | → _vfprintf_r |
| `vfprintf` | 0x8000dd90 | 6 | 1 miss | thin wrapper (not on main path) |
| `_vfprintf_r` | 0x8000a884 | 3395 | ok | format engine (route around) |
| `__sprint_r` | (in vfprintf cluster) | 15 | ok | → __sfvwrite_r |
| `__sfvwrite_r` | 0x8000de8c | 311 | ok | unbuffered → jalr __swrite |
| `__swrite` | 0x8000efd4 | 34 | **10 miss** | → _write_r |
| `_write_r` | 0x800104fc | 23 | 1 miss | → _write |
| `_write` | 0x8000003c | 12 | **6 miss** | per-byte HTIF console store |
| `exit` | 0x80004764 | 11 | ok | atexit + stdio flush + _exit |
| `__call_exitprocs` | 0x800070a8 | 92 | ok | atexit walk (empty ⇒ early ret) |
| `_exit` | 0x80000180 | 6 | ok | **HTIF exit store (70<<1)\|1** |

HTIF mailbox `tohost` = `0x8001ad00` (= `Vsa.Sim.tohostAddr`, M2). Console store
loop in `_write`; exit store in `_exit`; both characterized by the M2 HTIF
lemmas (`htif_store_exit` for exit; the console-store sibling for `_write`).
