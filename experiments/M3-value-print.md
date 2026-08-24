# M3 — the constrained output path: `native_print`/`native_println` → `value_print` → fputc/fputs/fwrite/fprintf → stdout FILE → `__sfvwrite_r`/`__swbuf_r` → `__swrite`/`_write_r`/`_write` → per-byte HTIF console store

Standing brief for the Layer-3/Layer-4 **output-correspondence** proof agents. Analysis
only (no `.lean` written). Every address, offset, and encoding below is quoted from
`experiments/disasm.txt` (objdump of `c/while-riscv-htif.elf`); jump-table targets and
rodata strings verified with `riscv-none-elf-objdump -s -j .rodata`. Where `c/src/*.c`
and the binary disagree, **the binary wins** — and here the compiler diverges from the C
in two spots (VAL_NULL and no-name VAL_FN emit via `fwrite`, not `fputs` as the source's
`fputs("null",out)` implies; noted in §1.1).

This is the CONSTRAINED sibling of two existing briefs — read both:
- `experiments/M3-setjmp-longjmp.md §4` maps the **stderr fwrite** path
  (`__sfvwrite_r`→`__swrite`→`_write_r`→`_write`→HTIF); that write chain is **byte-identical**
  to this brief's stdout path and **most of it transfers directly**. The only difference is
  the FILE object (stdout vs stderr) and the entry primitives (here fputc/fputs/fwrite/fprintf
  vs there fprintf only). That brief was allowed to route AROUND output (existential text);
  **this brief cannot** — `native_print`/`native_println` output must equal the spec bytes
  exactly.
- `experiments/M3-snprintf-lld.md` maps the `%lld` decimal core for the **string-sink**
  `_svfprintf_r`. The VAL_INT arm of `value_print` reaches the **real-FILE** `_vfprintf_r`
  (`0x8000a884`), whose decimal loop is a **structurally identical copy** of the sink one
  (§4). The `intToString` correspondence and the verified div cluster transfer wholesale.

Spec idiom follows `experiments/M3-pilot-design.md`: `Triple` composition, per-function
`Ust`/`St` config predicate with the **blanket ghost-frame conjunct**
(`hframe : ∀ R, NotWritten R → get? R = g R`), `StepObs` steps, noise absorbed
existentially (`minstret` ∃-bound, `tick < 2`, `mcycle/mtime/mip` never mentioned).

---

## 0. Executive summary

- **THE BUFFERING VERDICT: stdout is UNBUFFERED (`__SNBF`).** `main` (`0x80004588`) calls
  `setvbuf(stdout, NULL, _IONBF, 0)` at `0x800045ac`. Confirmed from the binary:
  `li a2,2` (`0x8000459c`) and `_IONBF == 2` in the toolchain's `stdio.h`
  (`/Users/kirancodes/toolchains/…/riscv-none-elf/include/stdio.h:122`;
  `_IOFBF=0, _IOLBF=1, _IONBF=2`). `main` passes `a0 = _impure_ptr->_stdout` (off 16,
  `ld a0,16(a5)`), `a1 = NULL` buf, `a3 = 0` size. `setvbuf`'s `_IONBF` tail
  (`0x80005ad8`) sets `_flags |= 0x2` (`__SNBF`, `ori a3,a5,2` @`0x80005ae8`),
  `_bf._base = _p = &FILE._nbuf` (`addi a2,s0,119; sd a2,0(s0); sd a2,24(s0)`),
  `_bf._size = 1` (`li a1,1; sw a1,32(s0)`), and **allocates NO buffer** (the `malloc`
  at `0x80005a40` is on the buffered-mode arm only). So stdout is unbuffered: `_flags`
  carries `__SNBF|__SWR`, `_bf._size = 1`, `_bf._base = &_nbuf` (a 1-byte cell inside
  the FILE struct itself).

- **OUTREPR CONSEQUENCE (the design question, RESOLVED — no generalization needed).**
  Because stdout is unbuffered, **every byte is flushed to the HTIF console on the same
  print call that produces it** — there is no static/heap accumulation buffer that defers
  output to a later flush boundary. `Machine.output σ = String.join σ.sailOutput.toList`
  (`Vsa/Machine.lean:36`) grows by exactly one character per HTIF console store (M2's
  `htif_store_putchar`), and the per-byte store loop in `_write` runs synchronously inside
  the fputc/fputs/fwrite/fprintf call. Therefore `OutRepr σ st := Machine.output σ = st.out`
  (`Vsa/RuntimeRepr.lean:145`) **can hold per-print, exactly as currently written** — the
  spec's per-print-call `out` append matches the machine's per-print HTIF stores
  1:1. **The feared "OutRepr must be generalized to machine-output + pending-buffer" does
  NOT arise for this binary**, precisely because `main` forces `_IONBF`. (Had `main`
  omitted the setvbuf, stdout to an HTIF device would default via `__swhatbuf_r` to
  block/line buffering, and the generalization WOULD be required. It is worth pinning
  the `__SNBF` flag in the invariant as a *guard* so the proof breaks loudly if the
  binary ever changes.) See §2 for the full argument and §6(a) for the one residual
  subtlety (`__swbuf_r` writes the byte into `_nbuf` *then* flushes, so the console store
  and the spec append are separated by ~1 store — still same call, still monotone).

- **value_print control flow (51 insts, `0x800028fc…0x800029c4`).** A **relative jump
  table** at `0x80019f10` (6 signed-int32 offsets from that base) dispatches on `v.kind`
  (`lw a4,0(a0)`; `li a5,5; bltu a5,a4,…ret` bounds-checks kind ≤ 5). Per kind (targets
  computed + verified against the disassembly, §1.1):
  - **VAL_NULL (0)** → `0x8000295c`: `fwrite("null",1,4,out)` (NOT fputs; compiler
    rewrote the constant-string fputs). String `0x80019018 = "null"`.
  - **VAL_BOOL (1)** → `0x80002974`: `fputs(b ? "true":"false", out)`. Strings
    `0x80019008="true"`, `0x80019010="false"`.
  - **VAL_INT (2)** → `0x80002990`: `fprintf(out, "%lld", v.as.i)` (`a1 = 0x800192c0 =
    "%lld"`). ★ the constrained decimal path (§4).
  - **VAL_STR (3)** → `0x800029a4`: `fputs(v.as.s, out)`.
  - **VAL_FN (4)** → `0x80002928`: loads `fn->fn_expr->as.fn.name` (`ld` chain
    `0(a0)→0→8`); if name≠0 `fprintf(out,"<fn %s>",name)` (`0x800192c8`); else
    `fwrite("<fn>",1,4,out)` (`0x80002948` region → `0x800192d0="<fn>"`).
  - **VAL_NATIVE (5)** → `0x80002948`: `fprintf(out,"<native fn %s>", name)`
    (`0x800192d8`).
  All arms take `out` in `a1` and **tail-call** the primitive (`j fprintf` / `j fputs` /
  `j fwrite`) — value_print has no epilogue on those arms (the tail-jump reuses value_print's
  own return address). Only the bounds-check-fail arm `ret`s (`0x800029ac`).

- **native_print / native_println call sites + the trailing newline.**
  `native_print` (`0x80002ed4`, 42 insts): args `a0=in`(→s4), `a2=argc`(→s3), `a3=argv`
  (Value* array, **24-byte stride**). `blez a2,0x80002f60` skips the loop when argc≤0.
  The loop copies each 24-byte Value onto the stack (`a0=sp`), loads `a1 =
  _impure_ptr->_stdout` (off 16), and `jal value_print`. **A separator space is printed
  BEFORE every value except the first**: the loop *enters* at `0x80002f1c` (skipping the
  separator), and the back-edge `0x80002f0c` does `fputc(' '=32, stdout)` before the next
  value. Output = `v0 ' ' v1 ' ' … v(n-1)`, **no trailing space/newline**. Returns
  `value_null()`. `native_println` (`0x80002f7c`, 17 insts): calls `native_print`, then
  `fputc('\n'=10, stdout)` (`0x80002fa0`), then returns `value_null()`. **The ONLY
  difference between print and println is the single trailing `fputc(10)`** — the
  load-bearing newline fact.

- **Full chain + insn counts** (all counts from the disassembly; §3):
  ```
  native_print 0x80002ed4 (42) / native_println 0x80002f7c (17)
    value_print 0x800028fc (51)      ── dispatch by v.kind ──
      VAL_NULL / VAL_FN(no name):  fwrite 0x80005260 (7) → _fwrite_r 0x80005078 (122)
                                     → __muldi3 0x80004640 (9, VERIFIED)  [size*nmemb]
                                     → __sfvwrite_r 0x8000de8c (311)
      VAL_BOOL / VAL_STR:          fputs 0x80006500 (5) → _fputs_r 0x800063b8 (82)
                                     → __sfvwrite_r 0x8000de8c (311)
      VAL_INT / VAL_FN(named) / VAL_NATIVE:
                                   fprintf 0x800061c0 (20) → _vfprintf_r 0x8000a884 (3395)
                                     [%lld: __hidden___udivdi3 0x800046ac (18, VERIFIED),
                                            __umoddi3 0x800046f4 (13, VERIFIED)]
                                     → __sfvwrite_r 0x8000de8c (311)   [the %s / literal flush]
      separator/newline:           fputc 0x800062e0 (54) → _putc_r 0x8000e6a4 (67)
                                     → __swbuf_r 0x8000f0c8 (85)   [unbuffered: store _nbuf + flush]
                                       → _fflush_r 0x8000edcc (50) → __sflush_r 0x8000eb70 (151)
    ── all four sinks converge on the unbuffered write dispatch ──
    __sfvwrite_r (unbuffered, __SNBF) → jalr a5 = FILE._write (off 64) = __swrite
      __swrite 0x8000efd4 (34) → (j) _write_r 0x800104fc (23) → (jal) _write 0x8000003c (12)
        _write → per-byte HTIF console store  tohost = 0x0101<<48 | byte  (0x8001ad00)
  ```

- **DECODE COVERAGE (checked programmatically vs `reachable_words.txt ∪
  exit_path_words.txt`, 8250 words).** Every function on the per-print output path is
  **fully covered, 0 missing**: value_print (0/40 distinct), native_print (0/39),
  native_println (0/16), fputc (0/37), fputs (0/5), _fputs_r (0/63), fwrite (0/7),
  _fwrite_r (0/85), fprintf (0/20), _vfprintf_r (0/1703), _putc_r (0/55), __swbuf_r
  (0/72), __swsetup_r (0/74), __sfvwrite_r (0/231), __swrite (0/34), _write_r (0/19),
  _write (0/12), __sflush_r (0/118), _fflush_r (0/41), value_null (0/3), __muldi3 (0/9),
  __hidden___udivdi3 (0/18), __umoddi3 (0/9). The `__swrite`/`_write_r`/`_write` gap
  flagged by the setjmp brief (42 missing) is **now closed** by `exit_path_words.txt`.
  **The ONE gap: `setvbuf` (0x800058c0, 173 insts, 63 distinct words MISSING).** But
  `setvbuf` runs in `main` *before* `interp_run` entry — i.e. **outside `Loaded` scope**
  (the plan places `Loaded` at interp_run entry). Its *effect* (stdout `__SNBF`,
  `_bf._base=&_nbuf`, `_bf._size=1`) must be a **pinned precondition** on the stdout FILE
  object, not decoded on the print path. See §3.4 + §6(b): either add setvbuf to the DT
  and prove a one-shot startup lemma, or (recommended) fold the unbuffered-stdout FILE
  fields into `Loaded`/`GoodState` as an assumption. All 63 missing words are ordinary
  RV64I (addi/sd/ld/lh/sh/sw/andi/ori/beq/bnez/j/mv/li); none exotic.

- **Biggest risks.** (a) `_vfprintf_r` is **3395 insts** and here the output IS constrained
  (`%lld` must equal `intToString`) — the "route around" trick from the setjmp brief is
  ILLEGAL; must use the **format-slice** approach from the snprintf brief (§4, §5.2). (b) The
  VAL_INT path uses the **real-FILE** `_vfprintf_r`, whose `%s`/literal flush goes through
  `__sfvwrite_r`→`__swrite`→HTIF (per-byte), unlike the sink's single `memmove` — so the
  decimal digits are first materialized in a stack scratch by the loop, then the ONE
  `__sprint_r`/`__sfvwrite_r` flush emits them byte-by-byte to HTIF. (c) `__swbuf_r`'s
  store-then-flush ordering for the fputc separator/newline (§6a). Details in §6.

---

## 1. Address maps

Instruction classes use the M2 battery vocabulary: **ALU** (OP/OP-IMM/LUI/AUIPC incl.
`mv`,`li`,`slli`,`addiw`,`sext.w`,`neg`,`snez`), **branch** (BRANCH: beq/bne/bltu/bgeu/
blez/bgez/beqz/bnez), **jump** (JAL/JALR incl. `j`,`jal`,`jr`,`ret`,`tail`), **load**
(LOAD: ld/lw/lwu/lh/lhu/lbu), **store** (STORE: sd/sw/sh/sb). "DT" = present in the
DecodeTable (checked against `reachable_words.txt ∪ exit_path_words.txt`, 8250 words).

### 1.1 `value_print` — `0x800028fc … 0x800029c4` (51 insts, DT: all present)

```
--- dispatch head (relative jump table) ---
800028fc: 00052703  lw   a4,0(a0)         LOAD   a4 = v.kind
80002900: 00500793  li   a5,5             ALU
80002904: 0ae7e463  bltu a5,a4,800029ac   BRANCH kind>5 → ret (no-op; kinds are 0..5)
80002908: 00056783  lwu  a5,0(a0)         LOAD   a5 = v.kind (zero-ext)
8000290c: 00017717  auipc a4,0x17         ALU    jump-table base hi
80002910: 60470713  addi a4,a4,1540       ALU    a4 = 0x80019f10  (table base)
80002914: 00279793  slli a5,a5,0x2        ALU    a5 = kind*4
80002918: 00e787b3  add  a5,a5,a4         ALU    a5 = &table[kind]
8000291c: 0007a783  lw   a5,0(a5)         LOAD   a5 = (int32) offset
80002920: 00e787b3  add  a5,a5,a4         ALU    a5 = base + offset  (absolute target)
80002924: 00078067  jr   a5              JUMP   dispatch
--- VAL_FN (4) : 0x80002928 ---
80002928: 00853783  ld   a5,8(a0)         LOAD   a5 = v.as.fn
8000292c: 0007b783  ld   a5,0(a5)         LOAD   a5 = fn->fn_expr
80002930: 0087b603  ld   a2,8(a5)         LOAD   a2 = fn_expr->as.fn.name (C-off 8)
80002934: 06060e63  beqz a2,800029b0      BRANCH name==NULL → fwrite("<fn>")
80002938: 00058513  mv   a0,a1            ALU    a0 = out
8000293c: 00017597  auipc a1,0x17         ALU
80002940: 98c58593  addi a1,a1,-1652      ALU    a1 = 0x800192c8 = "<fn %s>"
80002944: 07d0306f  j    800061c0         JUMP   fprintf(out,"<fn %s>",name)
--- VAL_NATIVE (5) : 0x80002948 ---
80002948: 00853603  ld   a2,8(a0)         LOAD   a2 = v.as.native.name (payload at off 8)
8000294c: 00058513  mv   a0,a1            ALU    a0 = out
80002950: 00017597  auipc a1,0x17         ALU
80002954: 98858593  addi a1,a1,-1656      ALU    a1 = 0x800192d8 = "<native fn %s>"
80002958: 0690306f  j    800061c0         JUMP   fprintf(out,"<native fn %s>",name)
--- VAL_NULL (0) : 0x8000295c ---
8000295c: 00058693  mv   a3,a1            ALU    a3 = out   (fwrite arg4)
80002960: 00400613  li   a2,4             ALU    a2 = nmemb = 4
80002964: 00100593  li   a1,1             ALU    a1 = size = 1
80002968: 00016517  auipc a0,0x16         ALU
8000296c: 6b050513  addi a0,a0,1712       ALU    a0 = 0x80019018 = "null"
80002970: 0f10206f  j    80005260         JUMP   fwrite("null",1,4,out)   ← not fputs!
--- VAL_BOOL (1) : 0x80002974 ---
80002974: 00852783  lw   a5,8(a0)         LOAD   a5 = v.as.b
80002978: 00016517  auipc a0,0x16         ALU
8000297c: 69850513  addi a0,a0,1688       ALU    a0 = 0x80019010 = "false"  (default)
80002980: 00078663  beqz a5,8000298c      BRANCH b==0 → keep "false"
80002984: 00016517  auipc a0,0x16         ALU
80002988: 68450513  addi a0,a0,1668       ALU    a0 = 0x80019008 = "true"
8000298c: 3750306f  j    80006500         JUMP   fputs(a0, out)   [a1 already = out]
--- VAL_INT (2) : 0x80002990 ---   ★ THE %lld PATH
80002990: 00853603  ld   a2,8(a0)         LOAD   a2 = v.as.i  (64-bit payload)
80002994: 00058513  mv   a0,a1            ALU    a0 = out
80002998: 00017597  auipc a1,0x17         ALU
8000299c: 92858593  addi a1,a1,-1752      ALU    a1 = 0x800192c0 = "%lld"
800029a0: 0210306f  j    800061c0         JUMP   fprintf(out,"%lld",v.as.i)
--- VAL_STR (3) : 0x800029a4 ---
800029a4: 00853503  ld   a0,8(a0)         LOAD   a0 = v.as.s  (char*)
800029a8: 3590306f  j    80006500         JUMP   fputs(v.as.s, out)   [a1 = out]
--- bounds-fail (kind>5) : 0x800029ac ---
800029ac: 00008067  ret                   JUMP   (defensive; unreachable for valid Value)
--- VAL_FN no-name : 0x800029b0 ---
800029b0: 00058693  mv   a3,a1            ALU    a3 = out
800029b4: 00400613  li   a2,4             ALU    nmemb = 4
800029b8: 00100593  li   a1,1             ALU    size = 1
800029bc: 00017517  auipc a0,0x17         ALU
800029c0: 91450513  addi a0,a0,-1772      ALU    a0 = 0x800192d0 = "<fn>"
800029c4: 09d0206f  j    80005260         JUMP   fwrite("<fn>",1,4,out)
```

**Jump table at `0x80019f10`** (`.rodata`, verified with objdump):
```
80019f10:  4c 8a fe ff   64 8a fe ff   80 8a fe ff   94 8a fe ff
80019f20:  18 8a fe ff   38 8a fe ff   [18 90 01 80 ...]
```
Signed int32 offsets, target = `0x80019f10 + (int32)entry`:
| kind | entry | target | arm |
|---|---|---|---|
| 0 VAL_NULL   | 0xfffe8a4c | 0x8000295c | fwrite "null" |
| 1 VAL_BOOL   | 0xfffe8a64 | 0x80002974 | fputs true/false |
| 2 VAL_INT    | 0xfffe8a80 | 0x80002990 | fprintf "%lld" |
| 3 VAL_STR    | 0xfffe8a94 | 0x800029a4 | fputs s |
| 4 VAL_FN     | 0xfffe8a18 | 0x80002928 | fprintf "<fn %s>" / fwrite "<fn>" |
| 5 VAL_NATIVE | 0xfffe8a38 | 0x80002948 | fprintf "<native fn %s>" |

**rodata strings** (verified): `0x80019008="true"`, `0x80019010="false"`,
`0x80019018="null"`, `0x800192c0="%lld"`, `0x800192c8="<fn %s>"`, `0x800192d0="<fn>"`,
`0x800192d8="<native fn %s>"`.

**For `native_print`/`native_println` reachability**, the interpreter's while language
prints only whatever `Value`s the program computes. The kinds that appear in a
deterministic non-error run are typically **VAL_NULL, VAL_BOOL, VAL_INT, VAL_STR**
(the four "data" kinds); **VAL_FN / VAL_NATIVE** are printable if the program passes a
function value to `print`. The load-bearing constrained cases for `term_sim`'s output
equality are the ones the spec's `print` semantics can produce; the spec's `Value` deep
embedding (`Vsa/While/Semantics.lean`) determines which arms are live per program.

### 1.2 `native_print` — `0x80002ed4 … 0x80002f78` (42 insts, DT: all present)

Native-fn ABI: `a0 = Interp* in`, `a1 = self/native-fn ptr`, `a2 = argc`, `a3 = argv`
(a `Value[]`, 24-byte stride: `kind`@0, `as`@8..23). Returns a `Value` (null) in `a0`.

```
80002ed4: fb010113  addi sp,sp,-80        ALU    prologue (24-byte Value scratch at 0(sp))
80002ed8: 03413023  sd   s4,32(sp)        STORE
80002edc: 04113423  sd   ra,72(sp)        STORE
80002ee0: 00050a13  mv   s4,a0            ALU    s4 = in
80002ee4: 06c05e63  blez a2,80002f60      BRANCH argc<=0 → skip loop, return null
   … save s0-s3 …
80002ef8: 00068413  mv   s0,a3            ALU    s0 = argv cursor
80002efc: 00060993  mv   s3,a2            ALU    s3 = argc
80002f00: 00000493  li   s1,0             ALU    s1 = index = 0
80002f04: 46018913  addi s2,gp,1120       ALU    s2 = &_impure_ptr
80002f08: 0140006f  j    80002f1c         JUMP   enter loop AT the value_print step (skip sep)
--- back-edge: print separator space then advance ---
80002f0c: 00093783  ld   a5,0(s2)         LOAD   a5 = _impure_ptr
80002f10: 01840413  addi s0,s0,24         ALU    argv++  (24-byte Value stride)
80002f14: 0107b583  ld   a1,16(a5)        LOAD   a1 = _impure_ptr->_stdout (off 16)
80002f18: 3c8030ef  jal  800062e0         JUMP   fputc(a0=32=' ', stdout)   [a0 set below]
--- value_print step ---
80002f1c: 00093783  ld   a5,0(s2)         LOAD   a5 = _impure_ptr
80002f20: 00043683  ld   a3,0(s0)         LOAD   Value word 0 (kind + pad)
80002f24: 00843703  ld   a4,8(s0)         LOAD   Value word 1 (as low)
80002f28: 0107b583  ld   a1,16(a5)        LOAD   a1 = stdout
80002f2c: 01043783  ld   a5,16(s0)        LOAD   Value word 2 (as high)
80002f30: 00010513  mv   a0,sp            ALU    a0 = &scratch Value (on stack)
80002f34: 00d13023  sd   a3,0(sp)         STORE  copy Value onto stack (by-value arg)
80002f38: 00e13423  sd   a4,8(sp)         STORE
80002f3c: 00f13823  sd   a5,16(sp)        STORE
80002f40: 0014849b  addiw s1,s1,1         ALU    index++
80002f44: 9b9ff0ef  jal  800028fc         JUMP   value_print(&val, stdout)
80002f48: 02000513  li   a0,32            ALU    a0 = ' '  (separator for NEXT iter)
80002f4c: fc9990e3  bne  s3,s1,80002f0c   BRANCH more args → back-edge (prints sep)
--- epilogue: return value_null() ---
80002f60: 000a0513  mv   a0,s4            ALU    a0 = in
80002f64: 889ff0ef  jal  800027ec         JUMP   value_null()   (returns null Value in a0)
80002f78: 00008067  ret                   JUMP
```

**Output shape:** `value_print(v0)`, then for each i≥1: `fputc(' ')` `value_print(vi)`.
So **space-separated, no leading/trailing space**. Empty arg list ⇒ no output. Return =
`value_null()`.

### 1.3 `native_println` — `0x80002f7c … 0x80002fbc` (17 insts, DT: all present)

```
80002f7c: fd010113  addi sp,sp,-48        ALU    prologue
80002f80: 02813023  sd   s0,32(sp)        STORE
80002f84: 00050413  mv   s0,a0            ALU    s0 = a0 (in / return-Value slot)
80002f88: 00010513  mv   a0,sp            ALU    a0 = &scratch  (ABI to native_print)
80002f8c: 02113423  sd   ra,40(sp)        STORE
80002f90: f45ff0ef  jal  80002ed4         JUMP   native_print(...)  (prints the args)
80002f94: 4601b783  ld   a5,1120(gp)      LOAD   a5 = _impure_ptr
80002f98: 00a00513  li   a0,10            ALU    a0 = '\n'  (byte 10)   ★ the newline
80002f9c: 0107b583  ld   a1,16(a5)        LOAD   a1 = stdout
80002fa0: 340030ef  jal  800062e0         JUMP   fputc('\n', stdout)    ★ trailing newline
80002fa4: 00040513  mv   a0,s0            ALU    a0 = in
80002fa8: 845ff0ef  jal  800027ec         JUMP   value_null()
80002fbc: 00008067  ret                   JUMP
```

**println = print + exactly one `fputc('\n'=10, stdout)`.** That single byte-10 HTIF
console store is the whole delta.

### 1.4 The four sink primitives (entry wrappers)

- **fprintf** (`0x800061c0`, 20 insts, DT ok): packs varargs to `32(sp)…`, loads
  `_impure_ptr`, `jal _vfprintf_r` (`0x8000a884`), `ret`. Same wrapper as the setjmp brief.
- **fputs** (`0x80006500`, 5 insts, DT ok): `mv a5,a0; a0=_impure_ptr; a2=out; a1=str;
  j _fputs_r`. `_fputs_r` (`0x800063b8`, 82 insts, DT ok): `strlen(str)`, builds a
  1-element `__suio` iovec on the stack (`_p→len, _nbytes→len, iovcnt→1`), then
  `jal __sfvwrite_r` (`0x80006448`).
- **fwrite** (`0x80005260`, 7 insts, DT ok) → `_fwrite_r` (`0x80005078`, 122 insts, DT ok):
  `__muldi3` (`0x800050ac`) computes `size*nmemb`, builds a 1-element iovec, `jal
  __sfvwrite_r` (`0x80005170`). (Uses the **VERIFIED `__muldi3`** — for value_print's
  fwrite calls `size=1, nmemb=4`, product 4.)
- **fputc** (`0x800062e0`, 54 insts, DT ok) → `_putc_r` (`0x8000e6a4`, 67 insts, DT ok).
  `_putc_r` decrements `FILE._w` (off 12); for unbuffered stdout `_w=0` so `_w-1 = -1 < 0`
  and (char ≠ '\n' handling aside) it falls to `blt a5,a0,0x8000e734` (`a0 = _lbfsize` off
  40 = 0) → `jal __swbuf_r` (`0x8000e738`). So each fputc on unbuffered stdout goes through
  `__swbuf_r`.

### 1.5 `__swbuf_r` — `0x8000f0c8 … ` (85 insts, DT ok): the unbuffered single-byte flush

For an unbuffered (`__SNBF`) writable stream with `_bf._base = &_nbuf` (nonzero,
`_bf._size = 1`), `__swbuf_r`:
1. reloads `_w = _lbfsize` (`0x8000f0ec`), tests `__SWR` (`andi a4,a5,8`) and `_bf._base≠0`
   (`0x8000f100`) — both true for our stdout,
2. stores the byte into the buffer cell (`sb s0,0(a4)` @`0x8000f14c`, where `a4 = _p`),
   advances `_p`, decrements `_w`,
3. since `_p - _bf._base` now equals `_bf._size` (=1), branches to `_fflush_r`
   (`0x8000f1d0: jal 0x8000edcc <_fflush_r>`).

`_fflush_r` (`0x8000edcc`, 50) → `__sflush_r` (`0x8000eb70`, 151). `__sflush_r`'s
real-FILE branch loads `_write` cookie (`ld a5,64(s0)` @`0x8000ecf4`) and `jalr a5`
(`0x8000ed08`) = `__swrite`, writing the 1 pending byte. **Net: fputc → 1 HTIF console
store, synchronously, same call.** (fputs/fwrite/fprintf-literal instead batch bytes into
one iovec and take the `__sfvwrite_r` direct-write branch, §1.6 — also synchronous, one
HTIF store per byte.)

### 1.6 `__sfvwrite_r` unbuffered dispatch — `0x8000de8c` (311 insts, DT ok)

Identical to the setjmp brief §"__sfvwrite_r write dispatch". Tests `__SNBF`
(`andi a5,a3,8` @`0x8000deac`) and `_bf._base≠0` (`0x8000dec0`) → the **direct-write**
branch: loads `_write` cookie `ld a5,64(s0)` (`0x8000df10`), seek-offset `_offset`
`ld a1,48(s0)`, and `jalr a5` (`0x8000df1c`) = `__swrite`. The `__SLBF` (line-buffered,
`andi a5,a3,2` @`0x8000ded8`) and the fully-buffered branches (with the `_malloc_r` at
`0x8000e02c`) are **dead** for `__SNBF` stdout — must be proved unreachable via the
pinned `_flags` (§6a). Same argument as the setjmp brief risk (a), but for stdout.

### 1.7 The write chain (BYTE-IDENTICAL to setjmp brief §1.5)

```
__swrite 0x8000efd4 (34):  lh a5,16(a1); andi a3,a5,256 (__SAPP) → 0 → not append
                           → j 0x8000f020 → _write_r  (the _lseek_r branch is dead)
_write_r 0x800104fc (23):  → jal 0x8000003c <_write>
_write   0x8000003c (12):  per-byte HTIF console store loop:
    8000004c: lbu  a5,0(a1)             a5 = *p
    80000050: addi a1,a1,1              p++
    80000054: or   a5,a5,a4             a5 = 0x0101<<48 | byte
    8000005c: sd   a5,-856(a6)          *tohost = a5   (tohost = 0x8001ad00)
    80000060: bne  a1,a3,8000004c       loop until p == buf+len
```
Each iteration = one 8-byte store `tohost = 0x0101_0000_0000_00XX` (device 1, cmd 1,
byte XX). This is exactly M2's **`htif_store_putchar`** (`Vsa/Sim/Htif.lean:164`), which
pushes `String.singleton (Char.ofNat byte)` onto `sailOutput` ⇒ appends one char to
`Machine.output`. `tohost = 0x8001ad00 = Vsa.Sim.tohostAddr`.

---

## 2. The stdout FILE object + the buffering / OutRepr argument (authoritative)

### 2.1 Buffering verdict (from the binary)

`main` @`0x8000459c/0x800045a0/0x800045a4/0x800045a8/0x800045ac`:
```
80004594: ld  a5,0(s0)      a5 = _impure_ptr        (s0 = gp+1120 = &_impure_ptr)
80004598: li  a3,0          size = 0
8000459c: li  a2,2          mode = 2 = _IONBF       ← unbuffered
800045a0: ld  a0,16(a5)     a0 = _impure_ptr->_stdout (FILE*, off 16)
800045a4: li  a1,0          buf  = NULL
800045ac: jal setvbuf       setvbuf(stdout, NULL, _IONBF, 0)
```
C source (`c/src/main.c:155`): `setvbuf(stdout, NULL, _IONBF, 0);`. Toolchain
`stdio.h`: `_IONBF == 2`. **Binary and source agree.**

`setvbuf`'s `_IONBF` arm (`0x80005ad8`):
```
80005ae0: addi a2,s0,119        a2 = &FILE._nbuf (1-byte internal cell)
80005ae8: ori  a3,a5,2          a3 = _flags | __SNBF (0x2)
80005aec: sw   zero,12(s0)      _w = 0
80005af4: sh   a3,16(s0)        _flags |= __SNBF
80005af8: sd   a2,0(s0)         _p        = &_nbuf
80005afc: sd   a2,24(s0)        _bf._base = &_nbuf
80005b00: sw   a1,32(s0)        _bf._size = 1        (a1 = 1)
```
**No malloc** on this arm. Post-setvbuf stdout FILE state (the pins the print proof
needs):
| field | off | value |
|---|---|---|
| `_flags` | 16 | `__SWR | __SNBF | …` (bit `0x8` and bit `0x2` both set) |
| `_w`     | 12 | 0 |
| `_p`     | 0  | `&FILE._nbuf` (= FILE+119) |
| `_bf._base` | 24 | `&FILE._nbuf` |
| `_bf._size` | 32 | 1 |
| `_write` cookie | 64 | `__swrite` (`0x8000efd4`) — set by `__sinit` |
| `_seek`  cookie | 48 | `__sseek` — set by `__sinit` (dead for our path) |

(`_impure_ptr->_stdout` and its `_write`/`_seek`/`_read`/`_close` cookies are populated by
`__sinit`/`_REENT_INIT`; the setjmp brief's target-resolution argument for `FILE->_write
== __swrite` applies verbatim here.)

### 2.2 The OutRepr consequence (the design question — RESOLVED)

`OutRepr σ st := Machine.output σ = st.out` (`Vsa/RuntimeRepr.lean:145`), with
`Machine.output σ = String.join σ.sailOutput.toList` (`Vsa/Machine.lean:36`) growing by
**one character per HTIF console store** (M2 `htif_store_putchar`).

The spec's `print`/`println` semantics **append the printed characters to `out` per print
call** (per-statement/per-native-call granularity). The question the task poses: *if the
machine defers output to a flush boundary, OutRepr cannot hold per-instruction, and it
would need generalizing to "machine output + pending buffer contents = spec out".*

**Because stdout is `__SNBF`, there is NO pending buffer.** Every byte a print produces is
flushed to the HTIF console **within the same fputc/fputs/fwrite/fprintf call** that
produced it:
- fputs/fwrite/fprintf-literal → `__sfvwrite_r` direct-write branch → `__swrite` →
  `_write` per-byte store loop, all synchronous (§1.6, §1.7).
- fputc → `__swbuf_r` stores 1 byte to `_nbuf`, immediately `_fflush_r` → `__swrite` →
  `_write` (§1.5).

The `_bf._size = 1` cell (`_nbuf`) holds **at most one byte in transit**, and never
across a print boundary: it is drained by the flush before the enclosing primitive
returns. So at every point where the spec appends to `st.out` (a completed print call),
the machine has already executed the corresponding HTIF stores, and
`Machine.output σ = st.out` holds **with the plain, ungeneralized `OutRepr`**.

**Verdict: no OutRepr generalization is required for this binary.** The plan's `OutRepr`
(`output only ever grows by exactly the spec characters`) is sound as-is on the `__SNBF`
path.

**But make the unbufferedness a LOAD-BEARING, PINNED assumption, not an accident.** Add
the stdout-FILE `__SNBF` flag (and `_write == __swrite`, `_bf._size = 1`) to `Loaded`/
`GoodState` as a stdout-FILE-shape predicate. Two payoffs: (i) it discharges the
`__sfvwrite_r`/`__swbuf_r`/`_putc_r` dead buffered branches by `decide` on `_flags`;
(ii) if the binary is ever rebuilt without the `setvbuf(_IONBF)` call, the pinned flag
becomes false and the proof fails loudly rather than silently mis-modeling buffered
output. **This is the single most important structural note in this brief.**

(Contrast: if stdout were `_IOFBF`/`_IOLBF`, `__swhatbuf_r` would `malloc` a heap buffer
via `__smakebuf`, output would accumulate there and flush only on buffer-full / `'\n'`
(LBF) / `exit`'s `__stdio_exit_handler` (`_cleanup_r` → `_fflush_r` on every stream). THEN
the OutRepr generalization the task describes would be mandatory: the invariant would read
`Machine.output σ ++ (pending bytes in stdout._bf[_base.._p)) = st.out`, threading the
FILE's `_p`/`_base` window through Layer-2. We are spared this by `_IONBF`.)

---

## 3. Call chain with instruction counts + which branches execute vs are dead

### 3.1 Per-kind live chains (counts from the disassembly)

| Value kind | value_print arm | primitive | engine | flush | terminal |
|---|---|---|---|---|---|
| NULL | fwrite("null",1,4) | fwrite 7 → _fwrite_r 122 (+__muldi3 9) | — | __sfvwrite_r 311 | __swrite 34 → _write_r 23 → _write 12 (4 stores) |
| BOOL | fputs(true/false) | fputs 5 → _fputs_r 82 (+strlen) | — | __sfvwrite_r 311 | …→ _write (4 or 5 stores) |
| INT  | fprintf("%lld") | fprintf 20 → _vfprintf_r 3395 | decimal loop (+udivdi3 18, umoddi3 13 per digit) | __sfvwrite_r 311 | …→ _write (1..20 stores) |
| STR  | fputs(s) | fputs 5 → _fputs_r 82 (+strlen) | — | __sfvwrite_r 311 | …→ _write (len stores) |
| FN(named) | fprintf("<fn %s>") | fprintf 20 → _vfprintf_r 3395 | %s copy | __sfvwrite_r 311 | …→ _write |
| FN(none) | fwrite("<fn>",1,4) | fwrite 7 → _fwrite_r 122 (+__muldi3 9) | — | __sfvwrite_r 311 | …→ _write (4 stores) |
| NATIVE | fprintf("<native fn %s>") | fprintf 20 → _vfprintf_r 3395 | %s copy | __sfvwrite_r 311 | …→ _write |
| sep/newline | native_print/println fputc | fputc 54 → _putc_r 67 → __swbuf_r 85 | — | _fflush_r 50 → __sflush_r 151 | __swrite 34 → _write_r 23 → _write 12 (1 store) |

### 3.2 Branches that execute vs provably dead

**Live** (must simulate): value_print dispatch + one arm; the chosen primitive's happy
path; `__sfvwrite_r`'s `__SNBF` direct-write branch (`0x8000debc→0x8000df10` region);
`__swrite`'s non-append branch (`j _write_r`); `_write`'s store loop; for fputc, `_putc_r`
fall-to-`__swbuf_r` + `__swbuf_r`'s store-then-`_fflush_r` + `__sflush_r`'s real-FILE
write. For VAL_INT: `_vfprintf_r`'s `%lld` slice (format parse of 4 chars, sign test +
`neg`, the decimal loop §4, one `__sprint_r`/`__sfvwrite_r` flush).

**Provably dead** (discharge by `decide` on pinned `_flags`/format/locale):
- `__sfvwrite_r` `__SLBF` branch (`andi a5,a3,2`) and fully-buffered branch with
  `_malloc_r` (`0x8000e02c`) — dead: `_flags` is `__SNBF`, not `__SLBF`/`__SFBF`.
- `_putc_r` fast in-buffer store (`0x8000e6f8`) — dead: `_w = 0` for `__SNBF`, forces the
  `__swbuf_r` call.
- `__swbuf_r` `__swsetup_r` re-init (`0x8000f188`) — dead: stdout already `__SWR` with a
  base; and the "flush failed" arms.
- `__sflush_r` `__SSTR` mem branch (`0x8000ecb4`, string sink), the `_seek`/append
  `jalr a6` (`0x8000ebd8`/`0x8000ec1c`, `__SAPP`/`__SOPT` — stdout is neither) — dead.
- `_fwrite_r`/`_fputs_r` lock-acquire/`__sinit` re-entry arms — dead once stdio is
  initialized (it is, `__sinit` ran during `main`'s setvbuf).
- `_vfprintf_r` (VAL_INT): **all** float (`_dtoa_r`, `__eqdf2/__ledf2/…`,
  `__muldi3/__divdi3/__moddi3` on the float path), wide-char (`_wcsrtombs_r`), grouping,
  width/precision-pad, and `_malloc_r` branches — dead for fixed format `"%lld"` + C
  locale. **Same dead-branch table as the snprintf brief §4**, applied to the real-FILE
  `_vfprintf_r` copy instead of `_svfprintf_r`.

### 3.3 Decode coverage vs `reachable_words.txt ∪ exit_path_words.txt` (8250 words)

Checked programmatically (see the coverage script summary in §0): **every function on the
per-print output path is 0/N missing.** The single gap is **`setvbuf` (63 distinct words
missing)** — see §3.4. (I re-verified `__swrite`/`_write_r`/`_write`, previously flagged in
the setjmp brief: now fully covered by `exit_path_words.txt`.)

### 3.4 The `setvbuf` gap (startup, outside `Loaded` scope)

`setvbuf` (`0x800058c0`, 173 insts) runs in `main` before `interp_run`. `disasm_reachable.py`
roots at `interp_run` and follows direct `jal`; `setvbuf` is reached only from `main`
(above interp_run), so its 63 distinct words never entered the closure (same cause as the
setjmp brief's missing `main`). **All 63 are ordinary RV64I** (addi/sd/ld/lh/sh/sw/andi/
ori/beq/bne/bnez/beqz/j/mv/li/negw/slliw/sext.w — sample:
`00042623 sw zero,12(s0)`, `0027e693 ori a3,a5,2`, `00c43023 sd a2,0(s0)`,
`00d41823 sh a3,16(s0)`, `00fa0a63 beq s4,a5,…`). **Two resolutions:**
1. **(recommended) Pin the unbuffered stdout FILE shape in `Loaded` (§2.2)** and do NOT
   decode setvbuf. The print proof consumes the FILE fields as a hypothesis; `setvbuf`
   never appears in the output-path DecodeTable. Cleanest and matches the plan's `Loaded`
   scoping.
2. Add setvbuf's 63 words to the DT and prove a one-shot `setvbuf_ionbf_spec` startup
   lemma establishing the FILE shape from `main`'s call — only needed if the proof wants
   to *derive* rather than *assume* unbufferedness.

---

## 4. The `intToString` correspondence (VAL_INT `%lld`) + the `%s`/fputs case

### 4.1 `%lld` on the REAL FILE — same digit core as the snprintf brief

VAL_INT reaches `fprintf(out,"%lld",v)` → `_vfprintf_r` (`0x8000a884`), NOT the string-sink
`_svfprintf_r` (`0x80007654`) of the snprintf brief. But the **decimal engine is a
structurally identical copy**. The loop in `_vfprintf_r` (`0x8000ca60 … 0x8000cab8`):
```
8000ca60: mv   a0,s6           a0 = running n
8000ca64: li   a1,10
8000ca68: jal  800046ac <__hidden___udivdi3>   a0 = n / 10        ★ VERIFIED div
8000ca6c: mv   s7,s6           s7 = old n (exit test)
8000ca74: mv   s11,s9          advance descending cursor
8000ca78: mv   s6,a0           n = n/10
8000ca7c: bgeu a5,s7,8000cab8  old n <= 9 → done
8000ca80: li   a1,10
8000ca84: mv   a0,s6           a0 = n
8000ca88: jal  800046f4 <__umoddi3>            a0 = n % 10        ★ VERIFIED mod
8000ca8c: addiw a0,a0,48       a0 = '0' + (n%10)
8000ca90: sb   a0,-1(s11)      *(--cursor) = digit char  (BACKWARD emit)
8000ca94: addi s9,s11,-1       next slot
8000ca98: addiw s0,s0,1        digit count++
8000ca9c: beqz s4,8000ca60     grouping flag == 0 (always for %lld) → next quotient step
```
This is **byte-for-byte the same shape** as the snprintf brief §1.4: emit `n%10` then
`n/=10`, do-while until pre-value ≤ 9, digits written low-first into a **descending**
scratch (so cursor→top is MSB-first), `'0'+d` via `addiw …,48`, `__hidden___udivdi3` +
`__umoddi3` per digit. The sign handling (leading `'-'`, `neg` to unsigned magnitude,
INT64_MIN via wrapping-neg-as-unsigned = 2^63) is the same as the snprintf brief §3.3.
**The `intToString` byte-for-byte verdict (incl. 0, -1, INT64_MIN) transfers wholesale**;
the correspondence to `natDigits`/`natToString`/`intToString`
(`Vsa/While/Semantics.lean:155-168`) is identical, and the same `decimalLoop_spec`
induction (snprintf brief §5.3) applies here — just re-anchored to `0x8000ca60` and the
`_vfprintf_r` register live-set (running n in `s6` here vs `s0` there; cursor `s9/s11`;
count `s0`). Consumes the **VERIFIED** div cluster (`__hidden___udivdi3`, `__umoddi3`).

**Key difference from the snprintf brief — the flush is per-byte to HTIF, not one memmove.**
The sink brief's digits went to `buf` via a single `memmove` (`__ssputs_r` fast path).
Here the digits materialized in `_vfprintf_r`'s stack scratch are flushed through
`__sprint_r`/`__sfvwrite_r` → `__swrite` → `_write` = **one HTIF console store per digit
byte**. So the constrained obligation is: (decimal loop produces bytes = `intToString v`)
∧ (those bytes reach `sailOutput` in order via the write chain). The first conjunct is the
snprintf brief's §5.3; the second is this brief's write-chain spec (§5.3 below).

### 4.2 The `%s`/fputs case (VAL_STR, VAL_BOOL, VAL_NULL, FN/native names)

- **VAL_STR** `fputs(v.as.s, out)`: bytes emitted = the C string at `v.as.s` up to (not
  incl.) NUL. By the Layer-2 `CStr`/`ValueRepr` invariant, `v.as.s` points to the spec
  string's UTF-8 bytes (all the interpreter's strings are ASCII/byte strings), so the
  emitted byte list = **the spec string's bytes** exactly. `_fputs_r` measures with the
  VERIFIED `strlen`, builds a 1-iovec, and `__sfvwrite_r` copies those `len` bytes to the
  write chain → `len` HTIF stores.
- **VAL_BOOL** → `fputs("true"|"false")`, **VAL_NULL** → `fwrite("null",1,4)`,
  **FN(no-name)** → `fwrite("<fn>",1,4)`: fixed rodata literals; emitted bytes = the pinned
  rodata strings (`0x80019008/0x80019010/0x80019018/0x800192d0`). These are constant
  byte-pins (M1 init-footprint style). The spec's `print` of a bool/null must produce
  exactly these ASCII bytes — **confirm the spec's `Value.toString`/print semantics uses
  `"true"`/`"false"`/`"null"` verbatim** (it does, per the deep embedding; this is the
  correspondence obligation for these arms).
- **FN(named) / NATIVE** → `fprintf("<fn %s>"/"<native fn %s>", name)`: `_vfprintf_r`'s
  `%s` path (literal prefix + `%s` copy + literal suffix), all flushed per-byte. Live only
  if the program prints a function value.

---

## 5. Proposed decomposition into provable units

Idiom: `M3-pilot-design.md` — `Triple`, `Ust`/`St` predicate with blanket ghost-frame,
`StepObs`, `tick < 2`, `minstret` ∃-bound. `P`/`Q` name the exact memory regions read/
written. The **stdout FILE shape** (`__SNBF`, `_write=__swrite`, `_bf._size=1`, `_p=_base=
&_nbuf`) is a shared precondition abbrev `StdoutUnbuffered m0 file`, pinned in every P and
sourced from `Loaded` (§2.2, §3.4).

### 5.1 `value_print_spec` (per-kind, or one spec ∃-quantified over the emitted bytes)

Parameterize by the `Value` (kind + payload), `out` (= stdout addr), and the pinned FILE
shape. `Q`: `Machine.output` grew by exactly `printBytes v` (the kind-determined byte
list), memory outside the write chain scratch preserved, `PC = ret`.
```
def printBytes : Value → List UInt8
  | .null      => "null".toUTF8
  | .bool true => "true".toUTF8 | .bool false => "false".toUTF8
  | .int i     => (intToString i).toUTF8
  | .str s     => s.toUTF8
  | .fn f      => ("<fn " ++ …).toUTF8  -- if reachable
  | .native n  => ("<native fn " ++ …).toUTF8

theorem value_print_spec :
  Triple (value_print_pre v out m0 g)          -- StdoutUnbuffered m0 out, PC=0x800028fc, a0=&v, a1=out
         (fun c => GoodState c.σ ∧ PC c = ret ∧
                   Machine.output c.σ = Machine.output σ0 ++ String.fromUTF8 (printBytes v) ∧
                   FrameOutsideWriteScratch c.σ.mem m0 ∧ c.tick < 2 …)
```
Composes the arm's primitive spec (§5.2) with the shared write-chain spec (§5.3). The
VAL_INT arm additionally consumes `decimalLoop_spec` (§4.1 / snprintf §5.3).

### 5.2 Primitive specs (fputs/fwrite/fprintf-literal/fputc)

Each reduces to "emit byte list L to unbuffered stdout":
- `fputs_spec` / `fwrite_spec`: measure/compute `L` (strlen/`__muldi3`), one
  `__sfvwrite_r` direct-write ⇒ `Machine.output` grows by `L`. Consumes VERIFIED
  `strlen`/`__muldi3`.
- `fputc_spec`: single byte via `_putc_r`→`__swbuf_r`→`_fflush_r`→`__sflush_r` ⇒ 1 char.
  Used for the separator space and println's `'\n'`.
- `vfprintf_lld_spec` (real FILE): the **format-slice** spec (like snprintf §5.2 but sink
  = real unbuffered FILE, flush = write chain not memmove). `Q`: `Machine.output` grows by
  `(intToString v).toUTF8`. `decide`-prune float/wide/grouping/pad dead branches (§3.2).

### 5.3 `write_chain_spec` (the shared terminal — the load-bearing output lemma)

`Triple` over `__sfvwrite_r`(direct-write) → `__swrite` → `_write_r` → `_write`, plus the
`__swbuf_r`/`_fflush_r`/`__sflush_r` variant for the fputc single byte. `Q`: for an input
iovec/byte-buffer `[p, p+len)` holding bytes `bs`, `Machine.output` grows by
`String.fromUTF8 bs` and memory is otherwise unchanged. **Consumes M2's
`htif_store_putchar`** once per byte, folded over the `_write` loop by induction on `len`
(measure = remaining bytes; each iteration one `htif_store_putchar` append). This is the
one place the character-exact output equality actually lands. Reuses the setjmp brief's
identical `_write`/`__swrite`/`_write_r` analysis.

### 5.4 `native_print_spec` / `native_println_spec` (the consumers)

- `native_print_spec`: induction over the arg list (measure = argc − index). Invariant:
  `Machine.output` = base ++ `interleave " " (map printBytes args[0..i])`. Each iteration
  composes `fputc_spec` (separator, i≥1) + `value_print_spec`. Returns `value_null`.
- `native_println_spec`: `native_print_spec` then one `fputc_spec('\n')` ⇒ output grows by
  `(interleaved prints) ++ "\n"`. Returns `value_null`.

These are the specs Layer 4 (`term_sim`) consumes when a `print`/`println` big-step node is
encountered: they re-establish `OutRepr` by appending exactly the spec `out` delta.

### 5.5 Which landed / named specs get consumed

| spec | status | consumed at |
|---|---|---|
| `htif_store_putchar` (`Vsa/Sim/Htif.lean:164`) | LANDED (M2) | `_write` loop, once per output byte — §5.3 |
| `__muldi3` | VERIFIED | `_fwrite_r` size*nmemb (VAL_NULL/FN(no-name)) |
| `__hidden___udivdi3` / `__umoddi3` (div cluster) | VERIFIED | `_vfprintf_r` decimal loop, once each per digit — §4.1 |
| `strlen` | VERIFIED | `_fputs_r` (VAL_STR/BOOL); `_vfprintf_r` prologue |
| `memcpy`/`memmove` | VERIFIED | `__sfvwrite_r`/`_vfprintf_r` internal copies (if any live) |
| snprintf-track `decimalLoop_spec` (snprintf §5.3) | proposed | re-anchored to `_vfprintf_r` `0x8000ca60` — §4.1 |
| `intToString`/`natDigits` correspondence (snprintf §3) | proposed | VAL_INT byte-equality |
| `OutRepr` (`Vsa/RuntimeRepr.lean:145`) | LANDED (def) | re-established by §5.1/§5.4 (ungeneralized — §2.2) |

---

## 6. Risks / blockers

**(a) Unbufferedness must be PINNED, and the dead buffered branches proved dead (the
central risk).** The whole "OutRepr holds per-print" argument (§2.2) rests on
`stdout._flags & __SNBF`. This flag is set by `setvbuf` in `main`, *outside* `Loaded`
scope. **Mitigation:** carry `StdoutUnbuffered m0 out` (the FILE-shape pins of §2.1) as a
`Loaded`/`GoodState` conjunct; discharge every `__sfvwrite_r`/`_putc_r`/`__swbuf_r`/
`__sflush_r` buffered/line-buffered/`_malloc_r` branch by `decide` on the pinned `_flags`.
If the pin is ever false the proof fails loudly (desired). This also kills the `_malloc_r`
sites (`__sfvwrite_r 0x8000e02c`; `_vfprintf_r`'s `_dtoa_r` scratch) — must be proved
unreachable, exactly the setjmp brief risk (a), for stdout.

**(b) `setvbuf` DecodeTable gap (63 words).** See §3.4. Recommended fix: pin the FILE
shape in `Loaded` and never decode setvbuf. Alternative: add its 63 (ordinary RV64I) words
+ a startup spec. **Blocker only if resolution (2) is chosen and the words are not added.**

**(c) `_vfprintf_r` is 3395 insts and output IS constrained (VAL_INT).** The setjmp
brief's "route around output" is **illegal here** — `%lld` must equal `intToString`
byte-for-byte. Must use the **format-slice** (snprintf brief §6a): pin `fmt="%lld"` + the
unbuffered-FILE flags, `decide`-prune float/wide/grouping/pad, collapse to the parse +
sign + decimal loop + one flush. Residual character-exact obligation = the decimal loop
(§4.1) + the write chain (§5.3). This is the same 3k-inst-body-as-slice discipline the
snprintf brief established, re-applied to the real-FILE copy.

**(d) fputc store-then-flush ordering (`__swbuf_r`).** For the separator space and
println's newline, `__swbuf_r` writes the byte into `_nbuf` *then* calls `_fflush_r` — so
the byte sits in `_nbuf` for ~a dozen instructions before the HTIF store. The spec append
happens at the (single) HTIF store, and `_nbuf` is drained before fputc returns, so
`OutRepr` still holds at every print-call boundary — but the proof must not assert
`OutRepr` mid-`__swbuf_r` (between the `_nbuf` store and the flush). Encode the fputc
byte-emission as an atomic `fputc_spec` whose `Q` (not any intermediate) re-establishes
output growth. **Not a soundness threat; a granularity note.**

**(e) Indirect `jalr a5` to the write cookie.** `__sfvwrite_r` (`0x8000df1c`) and
`__sflush_r` (`0x8000ed08`) reach `__swrite` via `jalr` on `FILE._write` (off 64). Needs
(i) the `jalr` word in the DT [present], and (ii) a target-resolution lemma `FILE._write ==
0x8000efd4` from the pinned FILE (set by `__sinit`). Same as setjmp brief risk (b);
resolve identically. The FILE-shape pin (a) supplies the `_write` cookie value.

**(f) VAL_FN / VAL_NATIVE reachability.** These arms are live only if a program prints a
function value. If the spec's `print` semantics for functions is unconstrained (like the
diagnostic text), they can be routed around; if constrained (must emit `"<fn NAME>"`
etc.), they need the `%s` slice of `_vfprintf_r` + the name-pointer chain
(`fn->fn_expr->as.fn.name`). Determine from the spec's `Value` print semantics which is
required; for a data-only test program these arms are dead.

**(g) 24-byte Value stride + by-value copy.** `native_print` copies each 24-byte `Value`
from `argv[i]` onto its own stack before calling `value_print` (`sd` ×3 at
`0x80002f34/38/3c`). The `ValueRepr` invariant must cover the stack copy (same bytes as
the argv slot) so `value_print_spec` reads a well-formed Value. Standard frame reasoning;
the 24-byte layout (kind@0, as@8) matches the snprintf brief's `Value` (there stringify
saw kind@0/as@8 in a 16-byte view — here native_print copies 24 bytes = the full tagged
union incl. the `native.name` slot at as+8). **Confirm the Value struct size (24 here vs
16 in stringify's read): the 24-byte stride is authoritative for the print path.**

---

## Appendix — quick address index

| symbol | addr | insts | DT | role |
|---|---|---|---|---|
| `value_print` | 0x800028fc | 51 | ok | jump-table dispatch on v.kind → fwrite/fputs/fprintf |
| `native_print` | 0x80002ed4 | 42 | ok | loop: sep-space + value_print per arg; ret null |
| `native_println` | 0x80002f7c | 17 | ok | native_print + fputc('\n'); ret null |
| `value_null` | 0x800027ec | 3 | ok | returns null Value (native-fn return) |
| `fputc` | 0x800062e0 | 54 | ok | → _putc_r |
| `_putc_r` | 0x8000e6a4 | 67 | ok | unbuffered → __swbuf_r |
| `__swbuf_r` | 0x8000f0c8 | 85 | ok | store _nbuf + _fflush_r (1 byte) |
| `fputs` | 0x80006500 | 5 | ok | → _fputs_r |
| `_fputs_r` | 0x800063b8 | 82 | ok | strlen + 1-iovec → __sfvwrite_r |
| `fwrite` | 0x80005260 | 7 | ok | → _fwrite_r |
| `_fwrite_r` | 0x80005078 | 122 | ok | __muldi3 size*nmemb + iovec → __sfvwrite_r |
| `fprintf` | 0x800061c0 | 20 | ok | → _vfprintf_r |
| `_vfprintf_r` | 0x8000a884 | 3395 | ok | real-FILE format engine; %lld slice = parse+sign+decimal loop+flush |
| `_svfprintf_r` | 0x80007654 | 3212 | ok | (string-sink twin — snprintf brief; NOT this path) |
| `__hidden___udivdi3` | 0x800046ac | 18 | ok | **VERIFIED** n/10 (decimal loop @0x8000ca68) |
| `__umoddi3` | 0x800046f4 | 13 | ok | **VERIFIED** n%10 (decimal loop @0x8000ca88) |
| `__muldi3` | 0x80004640 | 9 | ok | **VERIFIED** _fwrite_r size*nmemb |
| `__sfvwrite_r` | 0x8000de8c | 311 | ok | unbuffered → jalr _write (off 64) = __swrite |
| `__sflush_r` | 0x8000eb70 | 151 | ok | fputc flush: real-FILE _write cookie |
| `_fflush_r` | 0x8000edcc | 50 | ok | → __sflush_r |
| `__swrite` | 0x8000efd4 | 34 | ok | non-append → j _write_r |
| `_write_r` | 0x800104fc | 23 | ok | → jal _write |
| `_write` | 0x8000003c | 12 | ok | **per-byte HTIF console store** (htif_store_putchar) |
| `setvbuf` | 0x800058c0 | 173 | **63 miss** | main→ _IONBF: sets stdout __SNBF (startup, outside Loaded) |
| `main` | 0x80004588 | 46 | (miss, setjmp brief) | setvbuf(stdout,NULL,_IONBF,0) @0x800045ac |

HTIF mailbox `tohost = 0x8001ad00` (= `Vsa.Sim.tohostAddr`). Per-byte console store in
`_write`; characterized by M2 `htif_store_putchar` (`Vsa/Sim/Htif.lean:164`).
value_print jump table: `0x80019f10` (rel-int32, 6 entries). Decimal loop (VAL_INT):
`0x8000ca60 … 0x8000cab8` (div `0x8000ca68`, mod `0x8000ca88`, backward emit `0x8000ca90`).
`_IONBF = 2` (toolchain `stdio.h:122`); `main`'s `li a2,2` @`0x8000459c`.
