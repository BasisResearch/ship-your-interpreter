# M3 — the integer-to-string path: `stringify` → `snprintf(buf,64,"%lld",v)` → `_svfprintf_r` decimal core → `intToString v`

Standing brief for the Layer-3 integer-formatting proof agents. Analysis only
(no `.lean` written). Every address, offset, and encoding below is quoted from
`experiments/disasm.txt` (objdump of `c/while-riscv-htif.elf`); where `c/*.c`
and the binary disagree, **the binary wins**. (Here the plan's task text says
`stringify` lives in `c/src/value.c`; **the binary and the C both put it in
`c/src/interp.c:84`** — `value.c` has only `value_print`, which uses
`fprintf(out,"%lld",…)` and is *not* on this path. The binary wins: the 105-inst
`stringify` at `0x80002fc0` is the interp.c one.)

Spec idiom follows `experiments/M3-pilot-design.md`: `Triple` composition,
per-function `Ust`/`St` config predicate carrying the **blanket ghost-frame
conjunct** (`hframe : ∀ R, NotWritten R → get? R = g R`), `StepObs`
observational steps, noise absorbed existentially (`minstret` ∃-bound,
`tick < 2`, `mcycle/mtime/mip` never mentioned). The div-by-10 cluster reuses
the **already-verified** `__umoddi3`/`__hidden___udivdi3`/`__muldi3` specs.

WHY this brief matters to the spec: the plan's Layer-3 requires that the
`snprintf`-for-`%lld` behavior **equals** `intToString` (`Vsa/While/Semantics.lean`,
digit recursion). This is the entire reason `intToString`/`natDigits` are defined
by **digit recursion** (§3): the binary's decimal core is a divide-by-10 /
mod-10 emit-backward loop, and `natDigits` mirrors it digit-for-digit so the
correspondence is structural, not an appeal to an opaque `Nat.repr`.

---

## 0. Executive summary

- **Call chain (with insn counts).**
  ```
  stringify            0x80002fc0  (105)   VAL_INT case: snprintf(buf,64,"%lld",v.as.i)
    snprintf           0x80005c44  (46)    builds a string-sink FILE on its stack, → _svfprintf_r
      _svfprintf_r     0x80007654  (3212)  the format engine (string sink)
        __hidden___udivdi3 0x800046ac (18) n/10  (shift-subtract unsigned divide — VERIFIED cluster)
        __umoddi3      0x800046f4  (9)      n%10  (wraps __hidden___udivdi3 — VERIFIED)
        __ssprint_r    0x8000e908  (60)     flushes the sink's iov → __ssputs_r
          __ssputs_r   0x8001438c  (101)    copies bytes into the caller buffer via memmove (fast path)
            memmove    0x800069c4  (~117)   byte copy into buf
        strlen         0x80006cf0  (43)     (prologue: measures decimal_point; benign)
        memset         0x80006aec  (~46)    (prologue: zero 8-byte state array; benign)
        _localeconv_r  0x80010258  (2)      returns &C-locale (grouping="" ⇒ %'d path dead)
  ```
  Then back in `stringify`: `strlen(buf)` → `malloc(len+1)` → `memcpy` → return
  the heap copy.

- **Div-by-10 mechanism (answers Q1).** No M extension, so the decimal loop
  calls **both** `__hidden___udivdi3` (quotient `n/10`, `0x80008304`) and
  `__umoddi3` (remainder `n%10`, `0x80008324`) — **NOT** a multiply-shift
  reciprocal (`__muldi3` *is* linked and called once inside `_svfprintf_r` at
  `0x8000a520`, but that call is on the **float `_dtoa_r` path**, not the integer
  loop). Both div helpers are the **already-verified division cluster**
  (`__umoddi3` → `__hidden___udivdi3` shift-subtract, `Vsa.Sim` div specs). The
  loop emits digits **backward** into a stack buffer, low digit first
  (`sb a0,-1(s9); addi s10,s9,-1`), exactly like `natDigits`' `… ++ [last]`.

- **String-sink, not FILE (answers Q2).** `snprintf` does **not** touch the
  fwrite/`__sfvwrite_r`/`__swrite`/`_write`/HTIF path used by the setjmp
  diagnostic brief. It fabricates a **string-sink `FILE`** on its own stack with
  `_flags = 0x0208 = __SSTR|__SWR` (`lui a6,0xffff0; addi a6,a6,520 →
  0xffff0208`; the low half `0x0208` is the flags), `_bf._base = buf`, `_w =
  size-1` (`subw a4,a1,snez → n-1`). `_svfprintf_r` accumulates an iovec and
  flushes via **`__ssprint_r → __ssputs_r`**, and `__ssputs_r` takes its
  **`memmove` fast path** (`bgeu a3,s1` false ⇒ chunk fits ⇒
  `jal memmove; ret`) because the sink is **not** `__SMBF`/dynamic
  (`0x0208 & 0x480 = 0` — the grow-branch test `andi …,1152` at `0x80014400` is
  not taken, so **no `_malloc_r`/`_realloc_r`** inside the sink). This is the
  clean contrast to the setjmp brief's FILE path: the byte destination is a
  **memory buffer**, and the transfer is one `memmove`, not per-byte HTIF stores.

- **`intToString` byte-for-byte verdict incl. INT64_MIN (answers Q3).**
  **They agree byte-for-byte on all `Int` inputs.** The C signed path (`0x800080dc
  ld a3,0(a4)`; `bgez a3` skip; else `li a5,45; sb a5,167(sp)` store `'-'`; `neg
  a4,a4`) writes a leading `'-'` iff the value is negative, then formats the
  **unsigned magnitude** `a4`. For `v = INT64_MIN = -9223372036854775808`,
  `neg` is two's-complement and wraps to the same bit pattern, but read as
  **unsigned** it is `2^63 = 9223372036854775808` — the correct magnitude — so
  the loop (unsigned div/mod) prints `9223372036854775808` and the C output is
  `-9223372036854775808`. **`intToString` agrees**: `intToString (.negSucc m) =
  "-" ++ natToString (m+1)`, and for INT64_MIN the `Int` payload is
  `.negSucc 9223372036854775807`, so `natToString (9223372036854775807 + 1) =
  natToString 9223372036854775808 = "9223372036854775808"`, giving
  `"-9223372036854775808"`. **No overflow on either side** — C avoids it by never
  computing a *signed* negation result (it uses the wrapped `neg` as an *unsigned*
  magnitude), and Lean avoids it because `.negSucc m` already carries `m+1` as a
  `Nat`. Concrete traces in §3.3.

- **Decode-gap list (answers the decode-coverage check): NONE.** Every distinct
  32-bit word on the whole path is already in `reachable_words.txt ∪
  exit_path_words.txt`. Checked per function: `stringify` (0/84 missing),
  `snprintf` (0/46), `_svfprintf_r` (0/1621), `__hidden___udivdi3` (0/18),
  `__umoddi3` (0/9), `__ssprint_r` (0/47), `__ssputs_r` (0/91), `strlen` (0/43),
  `memcpy` (0/64), `memmove` (0/117), `malloc` (0/3), `_malloc_r` (0/425),
  `fwrite` (0/…; the malloc-fail branch), `_localeconv_r` (0/2). **This path is
  fully decode-covered** — the sharp contrast with the setjmp exit brief (42
  missing) is because `disasm_reachable.py` roots at `interp_run` and follows
  direct `jal`; `stringify`/`snprintf`/`_svfprintf_r` are all reached by direct
  `jal` from within the interp subtree, and the string sink uses `__ssprint_r`
  via **direct `jal`** (`0x80008af8`), not an indirect write cookie.

- **Biggest risk.** `_svfprintf_r` is **3212 instructions**. As with the setjmp
  brief's `_vfprintf_r`, whole-function forward simulation is infeasible; but here
  the output IS constrained (must equal `intToString v` byte-for-byte), so the
  "route around output" trick does **not** apply. The mitigation is to prove a
  **format-sliced spec**: pin the format string to exactly `"%lld"` and the FILE
  to the `__SSTR|__SWR` string sink, and show that this slice of `_svfprintf_r`
  is the small dispatch + the decimal loop + one `__ssprint_r` flush — a few
  hundred reachable instructions — with **every float/wide/grouping/pad branch
  proved dead** (§4). The decimal loop itself is the load-bearing induction
  (§5.3), consuming the verified div cluster.

---

## 1. Address maps

Instruction classes use the M2 battery vocabulary: **ALU** (OP/OP-IMM/LUI/AUIPC
incl. `mv`,`li`,`neg`,`snez`,`sext.w`,`addiw`,`slli`,`srli`), **branch**
(BRANCH: beq/bne/bltu/bgeu/blez/bgez/beqz/bnez), **jump** (JAL/JALR incl.
`j`,`jal`,`ret`,`jr`,`tail`), **load** (LOAD: ld/lw/lh/lhu/lbu), **store**
(STORE: sd/sw/sh/sb). "DT" = present in the 8,187-word DecodeTable (checked
against `reachable_words.txt ∪ exit_path_words.txt`).

### 1.1 `stringify` — `0x80002fc0 … 0x80003160` (105 insts, DT: all present)

Per-site classification of the dispatch head + the VAL_INT arm + the shared tail.
`a0 = &Value` (a `Value*`, tagged union: `kind` at off 0, payload `as` at off 8).

```
--- dispatch on v.kind (0(a0)) ---
80002fc0: 00052783  lw   a5,0(a0)          LOAD   a5 = v.kind
80002fc4: f9010113  addi sp,sp,-112        ALU    prologue (buf[64] lives at sp+16)
80002fc8: 06113423  sd   ra,104(sp)        STORE
80002fcc: 06813023  sd   s0,96(sp)         STORE
80002fd0: 04913c23  sd   s1,88(sp)         STORE
80002fd4: 00300713  li   a4,3              ALU    3 = VAL_STR
80002fd8: 10e78463  beq  a5,a4,0x800030e0  BRANCH VAL_STR → strlen/malloc/memcpy of v.as.s
80002fdc: 00200713  li   a4,2              ALU    2 = VAL_INT
80002fe0: 0ee78063  beq  a5,a4,0x800030c0  BRANCH VAL_INT → snprintf "%lld"   ★ the path
80002fe4: 02f76863  bltu a4,a5,0x80003014  BRANCH kind>2 (>=4: VAL_FN/VAL_NATIVE)
80002fe8: 0c078063  beqz a5,0x800030a8     BRANCH kind==0 (VAL_NULL) → "null"
                                            (fallthrough kind==1 VAL_BOOL → "true"/"false")
--- VAL_BOOL arm (0x80002fec) uses li/auipc/addi to pick "true"/"false" + strcpy ---
--- shared tail: measure + heap-copy the formatted buf ---
80003044: 00048513  mv   a0,s1             ALU    a0 = &buf   (s1 = sp+16)
80003048: 4a9030ef  jal  0x80006cf0 <strlen>   JUMP  len = strlen(buf)
8000304c: 00150613  addi a2,a0,1           ALU    a2 = len+1
80003050: 00060513  mv   a0,a2             ALU    a0 = len+1  (malloc size)
80003054: 00c13423  sd   a2,8(sp)          STORE  spill len+1
80003058: 738010ef  jal  0x80004790 <malloc>    JUMP  s = malloc(len+1)
8000305c: 00813603  ld   a2,8(sp)          LOAD   a2 = len+1 (memcpy size)
80003060: 00050413  mv   s0,a0             ALU    s0 = s
80003064: 0c050e63  beqz a0,0x80003140     BRANCH malloc==NULL → fwrite("out of memory")+exit(1)
80003068: 00048593  mv   a1,s1             ALU    a1 = &buf (src)
8000306c: 35d030ef  jal  0x80006bc8 <memcpy>    JUMP  memcpy(s, buf, len+1)
80003070: 06813083  ld   ra,104(sp)        LOAD   epilogue
80003074: 00040513  mv   a0,s0             ALU    return s
...
80003084: 00008067  ret                    JUMP
--- VAL_INT arm (0x800030c0) — ★ THE %lld PATH ---
800030c0: 00853683  ld   a3,8(a0)          LOAD   a3 = v.as.i   (64-bit payload)
800030c4: 01010493  addi s1,sp,16          ALU    s1 = &buf[64]
800030c8: 00048513  mv   a0,s1             ALU    a0 = buf       (snprintf dst)
800030cc: 00016617  auipc a2,0x16          ALU    fmt hi
800030d0: 1f460613  addi a2,a2,500 # 0x800192c0    a2 = "%lld"   (see §3.1 verify)
800030d4: 04000593  li   a1,64             ALU    a1 = 64        (sizeof buf)
800030d8: 36d020ef  jal  0x80005c44 <snprintf>  JUMP snprintf(buf,64,"%lld",a3)
800030dc: f69ff06f  j    0x80003044        JUMP   → shared tail (strlen/malloc/memcpy)
--- malloc-fail branch (0x80003140) ---
80003140: 4601b783  ld   a5,1120(gp) # _impure_ptr    LOAD
80003144: 00e00613  li   a2,14            ALU   len("out of memory\n")=14
80003148: 00100593  li   a1,1             ALU   nmemb=1
8000314c: 0187b683  ld   a3,24(a5)        LOAD  a3 = _impure_ptr->_stderr
80003150: 00016517  auipc a0,0x16         ALU   msg hi
80003154: ef050513  addi a0,a0,-272 # 0x80019040  a0 = "out of memory\n"
80003158: 108020ef  jal  0x80005260 <fwrite>   JUMP fwrite(msg,1,14,stderr)
8000315c: 00100513  li   a0,1             ALU   exit code 1
80003160: 604010ef  jal  0x80004764 <exit>     JUMP exit(1)  — no return
```

**Answers Q4 (stringify's OTHER branches + malloc usage):**
- **VAL_NULL / VAL_BOOL / VAL_FN(no-name) / VAL_NATIVE** do **not** call
  `snprintf`. They store a small literal directly and `strcpy` it into `buf`
  (VAL_NULL `0x800030a8`: `lui a5,0x6c6c7; addi a5,…,1390 → "null"` packed as a
  word, `sw a5,16(sp); sb zero,4(s1)`; VAL_BOOL: `auipc/addi` a pointer to
  `"true"`/`"false"` then `strcpy` at `0x8000300c`). **Only VAL_INT** (and the
  named-function `VAL_FN` case, `0x8000302c`, which uses `snprintf "<fn %s>"`)
  route through `snprintf`. The `%lld` obligation is the VAL_INT arm alone.
- **VAL_STR** (`0x800030e0`) does **no** snprintf and no `buf`: it
  `strlen(v.as.s)+1`, `malloc`s, and `memcpy`s the source string directly — a
  pass-through copy.
- **malloc usage (MallocContract consumer).** Every non-error arm converges on the
  shared tail `malloc(strlen(buf)+1)` at `0x80003058` (and VAL_STR's own
  `malloc(len+1)` at `0x800030f8`). `stringify` is therefore a **MallocContract
  consumer** exactly as `runtime_error`'s snprintf callees are: it needs the
  `malloc_spec` giving a fresh, disjoint, `len+1`-byte region (or NULL, handled by
  the `beqz a0,0x80003140` fail branch → `exit(1)`). The result buffer is the
  function's return value; its content is `intToString v ++ [NUL]` after the
  `memcpy`.

### 1.2 `snprintf` — `0x80005c44 … 0x80005cfc` (46 insts, DT: all present)

Builds the **string-sink FILE** on its own stack (offsets `8(sp)..40(sp)`) and
calls `_svfprintf_r`. The load-bearing setup:

```
80005c44: ef010113  addi sp,sp,-272       ALU    prologue
80005c48: 80000337  lui  t1,0x80000       ALU    t1 = 0x80000000
80005c60/64: sd a6,256(sp); sd a7,264(sp) STORE  spill varargs a6,a7
80005c54..5c: sd a3/a4/a5,232/240/248(sp) STORE  spill varargs a3,a4,a5 (the "%lld" arg lands here)
80005c68: fff34313  not  t1,t1            ALU    t1 = 0x7fffffff_ffffffff (size sanity bound)
80005c6c: 4601b483  ld   s1,1120(gp) # _impure_ptr  LOAD  reent
80005c70: 08b36c63  bltu t1,a1,0x80005d08 BRANCH size > SSIZE_MAX → EOVERFLOW (dead: a1=64)
80005c74: 00b03733  snez a4,a1            ALU    a4 = (n != 0) ? 1 : 0
80005c78: ffff0837  lui  a6,0xffff0       ALU    a6 hi
80005c7c: 00050793  mv   a5,a0            ALU    a5 = buf (dst)
80005c80: 40e5873b  subw a4,a1,a4         ALU    a4 = n - (n!=0) = n-1   (_w = size-1)
80005c88: 0e810693  addi a3,sp,232        ALU    a3 = &va_list (points at spilled a3..a7)
80005c8c: 20880813  addi a6,a6,520        ALU    a6 = 0xffff0208         (_flags low = 0x0208)
80005c90: 00058413  mv   s0,a1            ALU    s0 = n
80005c94: 00048513  mv   a0,s1            ALU    a0 = reent (_svfprintf_r arg0)
80005c98: 00810593  addi a1,sp,8          ALU    a1 = &FILE (the string sink)
80005c9c: 00f13423  sd   a5,8(sp)         STORE  FILE._p    = buf
80005ca0: 02f13023  sd   a5,32(sp)        STORE  FILE._bf._base = buf
80005ca8: 00e12a23  sw   a4,20(sp)        STORE  FILE._w    = n-1
80005cac: 02e12423  sw   a4,40(sp)        STORE  FILE._bf._size = n-1
80005cb0: 01012c23  sw   a6,24(sp)        STORE  FILE._flags = 0x0208 (__SSTR|__SWR)
80005cb4: 00d13023  sd   a3,0(sp)         STORE  (spill va_list ptr)
80005cb8: 19d010ef  jal  0x80007654 <_svfprintf_r>  JUMP
80005cbc: fff00793  li   a5,-1            ALU
80005cc0: 02f54c63  blt  a0,a5,0x80005cf8 BRANCH ret < -1 → error (dead here)
80005cc4: 00041c63  bnez s0,0x80005cdc    BRANCH n != 0 → NUL-terminate
   ... 0x80005cdc: ld a5,8(sp); sb zero,0(a5)  (write '\0' at FILE._p) ...
80005cd8: 00008067  ret                    JUMP  return #chars-would-have-been-written
```

Key facts the spec pins: `_flags = 0x0208` (§0), `_w = size-1 = 63`,
`_bf._base = _p = buf`, and the NUL terminator is written by **snprintf itself**
(`sb zero,0(a5)` on the `bnez s0` arm), not by `_svfprintf_r`. So the observable
memory write is `buf[0..k) = decimal digits` (by the sink) plus `buf[k] = '\0'`
(by snprintf), where `k = strlen(intToString v)` and `k < 63` always (max 20
chars for INT64_MIN incl. sign, ≪ 63). **No truncation** for any 64-bit value.

### 1.3 `_svfprintf_r` — `0x80007654 … 0x8000a880` (3212 insts, DT: all present)

Too large to reproduce; only the **`"%lld"`-reachable slice** matters. Segments:

**(a) Prologue (always run, benign).** `_localeconv_r` (returns C-locale ptr),
`strlen(decimal_point)` (`= 1`), `memset(sp+200,0,8)` (zero an 8-slot state
array). No output.

**(b) Format parse.** Walks `"%lld"`: `%` enters the conversion state machine;
`l` (`li a5,108; beq` at `0x80008538`) sets the long/`0x10` flag twice (`ll`);
`d` reaches the **signed-decimal** case (§1.4).

**(c) Signed-decimal setup + negation** (`0x800080c4 … 0x800080f8`):
```
800080dc: 00073683  ld   a3,0(a4)         LOAD   a3 = the 64-bit arg (va_list slot)
800080e4: 00068713  mv   a4,a3            ALU    a4 = value
800080e8: f606d4e3  bgez a3,0x80008050    BRANCH value >= 0 → skip sign (a4 stays)
800080ec: 02d00793  li   a5,45            ALU    a5 = '-'
800080f0: 0af103a3  sb   a5,167(sp)       STORE  sign byte = '-'
800080f4: 40e00733  neg  a4,a4            ALU    a4 = -value (unsigned magnitude; INT64_MIN→2^63)
```

**(d) Decimal loop** (`0x800080fc … 0x80008358`) — the digit engine, §1.4.

**(e) Flush** (`0x80008af8` `jal __ssprint_r`) — hands the collected iov to the
string sink; `__ssprint_r` calls `__ssputs_r` which `memmove`s into `buf`.

**(f) Dead segments for `"%lld"` + string sink** (§4): all `_dtoa_r`
(`0x80009a74`,`0x80009fe0`,`0x8000a62c`), `__muldi3`/`__divdi3`/`__moddi3`
(`0x8000a520`,`0x80009678`,`0x8000965c` — float/`%f`/`%g` and the SECOND
`__umoddi3` at `0x8000a170`), `__eqdf2`/`__ledf2`/… (float compares),
`_wcsrtombs_r` (wide), the `_malloc_r` sites (`0x80009094`,`0x80009ec0`,
`0x80009f04` — `_dtoa_r` scratch and `%ls`), the grouping code (guarded by the
`t1 & 1024` flag which is 0 for `%lld` and by C-locale `grouping=""`), and the
padding/precision segments (no width/precision in `"%lld"`).

### 1.4 The decimal conversion loop — `0x800080fc … 0x80008358` (DT: all present)

The heart of the correspondence. `a4` holds the unsigned magnitude; `s9`/`s10`
are a **descending** write pointer into a stack scratch (`s6 = sp+348` top).

```
--- single-digit fast path (magnitude <= 9, incl. 0) ---
80008100: 00900793  li   a5,9             ALU
80008104: 1ce7e263  bltu a5,a4,0x800082c8 BRANCH magnitude>9 → loop; else fall through
80008108: 0307071b  addiw a4,a4,48        ALU    a4 = '0' + digit
8000810c: 14e10da3  sb   a4,347(sp)       STORE  emit the single digit  (buf[347])
   ... proceeds to length/pad/flush with one char ...
--- multi-digit do-while loop entry (magnitude > 9), at 0x800082c8 ---
800082c8: 15c10b13  addi s6,sp,348        ALU    s6 = top of scratch
800082dc: 000b0c93  mv   s9,s6            ALU    s9 = write cursor (starts at top)
800082e8: 00000b93  li   s7,0             ALU    s7 = digit count = 0
800082f4: 00070413  mv   s0,a4            ALU    s0 = running value n
800082f8: 0240006f  j    0x8000831c       JUMP   enter at the mod step
--- quotient step: n = n / 10 ---
800082fc: 00040513  mv   a0,s0            ALU    a0 = n
80008300: 00a00593  li   a1,10            ALU    a1 = 10
80008304: ba8fc0ef  jal  0x800046ac <__hidden___udivdi3>  JUMP  a0 = n / 10   ★ VERIFIED div
80008308: 00040b13  mv   s6,s0            ALU    s6 = old n (for exit test)
8000830c: 00900793  li   a5,9             ALU
80008310: 000d0c93  mv   s9,s10           ALU    advance cursor (s9 = s10 = prev-1)
80008314: 00050413  mv   s0,a0            ALU    n = n / 10
80008318: 0567f063  bgeu a5,s6,0x80008358 BRANCH old n <= 9 → done (last digit already emitted)
--- remainder/emit step: digit = n % 10 ---
8000831c: 00a00593  li   a1,10            ALU    a1 = 10
80008320: 00040513  mv   a0,s0            ALU    a0 = n
80008324: bd0fc0ef  jal  0x800046f4 <__umoddi3>  JUMP  a0 = n % 10   ★ VERIFIED mod
80008328: 0305051b  addiw a0,a0,48        ALU    a0 = '0' + (n%10)
8000832c: feac8fa3  sb   a0,-1(s9)        STORE  *(--cursor) = digit char   (BACKWARD)
80008330: fffc8d13  addi s10,s9,-1        ALU    s10 = s9 - 1 (next slot)
80008334: 001b8b9b  addiw s7,s7,1         ALU    digit count++
80008338: fc0d82e3  beqz s11,0x800082fc   BRANCH grouping flag == 0 (always, %lld) → next quotient step
   ... 0x8000833c: grouping-separator logic (dead: s11=0 for %lld) ...
80008358: (exit)   length = top - cursor ; hand off to pad/flush
```

**Loop shape:** it is a **do-while emitting `n%10`, then `n/=10`, until the
pre-division value `≤ 9`** (whereupon the leading digit was just emitted and the
loop ends). Written low-digit-first into a **descending** buffer, so the final
byte order (cursor→top) is most-significant-first. This is **exactly** the
`natDigits` recursion read in reverse (§3): `natDigits` appends the least-
significant digit **last** (`natDigits (n/10) ++ [digitChar (n%10)]`), and the
loop writes it **first** into a descending buffer — the two produce the identical
MSB-first string.

### 1.5 The div cluster (VERIFIED — consumed, not re-proved)

```
__hidden___udivdi3  0x800046ac (18)  shift-subtract unsigned divide, returns quotient in a0
__umoddi3           0x800046f4 (9):
  800046f4: mv t0,ra ; jal __hidden___udivdi3 ; mv a0,a1 ; jr t0   -- remainder in a1→a0
```
`__umoddi3` saves `ra` in `t0` (the M3-pilot's noted t0-survival case), calls the
shared core, and returns the remainder (`a1`) it left. Both are covered by the
`Vsa.Sim` division-cluster specs. `__muldi3` (`0x80004640`, verified) is **not**
consumed on the integer path (float only).

### 1.6 The string sink flush — `__ssprint_r` (60) + `__ssputs_r` (101)

`__ssprint_r` (`0x8000e908`) walks the iovec array, for each nonempty entry calls
`__ssputs_r`, decrementing the sink's `_w`. `__ssputs_r` (`0x8001438c`):

```
8001438c: fc010113  addi sp,sp,-64        ALU
80014394: 00c5a483  lw   s1,12(a1)        LOAD   s1 = FILE._w  (remaining capacity)
800143a8: 0496f663  bgeu a3,s1,0x800143f4 BRANCH chunk_len >= _w → grow branch (DEAD, §4)
--- fast path: chunk fits ---
800143b0: 00043503  ld   a0,0(s0)         LOAD   a0 = FILE._p (dest cursor)
800143b8: mv a1,a5 ; mv a2,s1             ALU    src=chunk, len
800143c0: e04f20ef  jal  0x800069c4 <memmove>  JUMP  memmove(_p, chunk, len)  ★ VERIFIED memmove
800143d0: subw a4,a4,s1 ; add a5,a5,s1    ALU    _w -= len ; _p += len
800143d8/dc: sw a4,12(s0); sd a5,0(s0)    STORE  write back _w, _p
800143f0: 00008067  ret                    JUMP  return 0
--- grow branch 0x800143f4 (DEAD for snprintf): tests _flags & 0x480, calls _malloc_r/_realloc_r ---
```

For the `__SSTR|__SWR` (non-`__SMBF`) sink of `snprintf` with `_w = 63 ≫
20`, the `bgeu a3,s1` guard is **false**, so the **fast `memmove` path** runs and
the grow/malloc branch is dead. The sink's `_p` advances and `_w` shrinks; the
bytes land in `buf`.

---

## 2. The string-sink FILE layout (authoritative, from the binary)

`snprintf` fabricates the FILE at `sp+8` (via the spills in §1.2). Fields it sets
(offsets are into the `FILE`/`__sFILE` struct as the binary lays it out):

| field | struct off | snprintf store (§1.2) | value | used by |
|---|---|---|---|---|
| `_p`         | 0  | `sd a5,8(sp)`   | `buf` | `__ssputs_r` cursor |
| `_w`         | 12 | `sw a4,20(sp)`  | `size-1 = 63` | `__ssputs_r` capacity |
| `_flags`     | 16 | `sw a6,24(sp)`  | `0x0208 = __SSTR\|__SWR` | branch guards |
| `_bf._base`  | 24 | `sd a5,32(sp)`  | `buf` | (grow branch; dead) |
| `_bf._size`  | 32 | `sw a4,40(sp)`  | `size-1 = 63` | (grow branch; dead) |

- `_flags = 0x0208`: `__SSTR (0x200)` marks a **string sink** (routes flush to
  `__ssprint_r`/`__ssputs_r`, never `__sfvwrite_r`/`__swrite`); `__SWR (0x8)`
  marks it writable. **`__SMBF (0x800)` is CLEAR** ⇒ the buffer is caller-owned,
  not malloc-grown ⇒ `__ssputs_r`'s grow branch is dead (§1.6, §4).
- `_w = size - 1`: reserves one byte for the NUL that **snprintf** (not the sink)
  writes on return (§1.2). Guarantees the sink never overruns `buf[0..size-1)`.
- This is the clean contrast the plan asked for vs the setjmp brief: **no `FILE`
  cookie, no `__swrite`, no `_write`, no per-byte HTIF store**. The byte
  destination is the caller's `buf`, reached by a single `memmove`.

---

## 3. The `intToString` correspondence (byte-for-byte)

`Vsa/While/Semantics.lean:155–168`:
```
def natDigits : Nat → Nat → List Char
  | 0, _ => []
  | fuel + 1, n =>
    if n < 10 then [Nat.digitChar n]
    else natDigits fuel (n / 10) ++ [Nat.digitChar (n % 10)]
def natToString (n : Nat) : String := (natDigits (n + 1) n).foldl .push ""
def intToString : Int → String
  | .ofNat m    => natToString m
  | .negSucc m  => "-" ++ natToString (m + 1)
```

### 3.1 The format string is exactly `"%lld"`

`stringify` VAL_INT arm loads `a2 = 0x800192c0` (`auipc a2,0x16; addi a2,a2,500`).
The C source is `snprintf(buf, sizeof buf, "%lld", v.as.i)` (interp.c:94). The
spec pins `[0x800192c0] = "%lld\0"` as a P hypothesis (a rodata byte-pin, like
the setjmp brief's `"%s\n"` pin at `0x800195e0`). This is the sole format; the
spec's dead-branch discharge (§4) keys off these 4 bytes by `decide`.

### 3.2 Structural mapping loop ↔ recursion

| binary (§1.4) | `natDigits` |
|---|---|
| magnitude ≤ 9 fast path: emit one `'0'+n` | base case `n < 10 ⇒ [digitChar n]` |
| loop: emit `n%10`, then `n := n/10`, repeat while pre-value > 9 | recursive `natDigits (n/10) ++ [digitChar (n%10)]` |
| digits written **descending** (low first, into a top-down buffer) | list built **MSB-first** (`… ++ [lsd]`), so reversal matches | 
| `'0' + d` (`addiw a0,a0,48`) | `Nat.digitChar d` (= `'0'+d` for `d < 10`) |
| leading `'-'` iff `value < 0`, then unsigned magnitude | `intToString (.negSucc m) = "-" ++ natToString (m+1)` |

`Nat.digitChar d = Char.ofNat (48 + d)` for `d ≤ 9`, matching `addiw …,48`
byte-exactly. The `fuel` argument (`n+1`) is a Lean-side termination device with
no binary analogue; the binary loop terminates by the `bgeu a5,s6` exit test
(pre-division value ≤ 9). The equivalence proof (§5.3) shows the loop's emitted
byte list equals `natDigits (n+1) n` by induction on the digit count.

### 3.3 Concrete traces (both sides)

**v = 0** (`Int.ofNat 0`).
- C: `bgez` taken (0 ≥ 0, no sign); magnitude `a4 = 0 ≤ 9` ⇒ fast path emits
  `'0'`; result `"0"`, then snprintf writes `'\0'`. Bytes: `30 00`.
- Lean: `intToString (.ofNat 0) = natToString 0 = (natDigits 1 0).foldl push ""`;
  `natDigits 1 0 = if 0<10 then [digitChar 0] = ['0']` ⇒ `"0"`. **Match.**

**v = -1** (`Int.negSucc 0`).
- C: `bgez` NOT taken ⇒ sign `'-'`; `neg a4` ⇒ magnitude `1 ≤ 9` ⇒ fast path
  `'1'`; result `"-1"`. Bytes: `2d 31 00`.
- Lean: `intToString (.negSucc 0) = "-" ++ natToString (0+1) = "-" ++ natToString
  1 = "-" ++ "1" = "-1"`. **Match.**

**v = -9223372036854775808 = INT64_MIN** (`Int.negSucc 9223372036854775807`).
- C: `ld a3` = `0x8000000000000000`; `bgez` NOT taken ⇒ sign `'-'`;
  `neg a4` ⇒ `a4 = 0x8000000000000000` read as **unsigned = 9223372036854775808 =
  2^63** (no signed overflow — the value is only ever used unsigned by the
  div/mod loop); loop prints `"9223372036854775808"`; result
  `"-9223372036854775808"` (20 bytes + NUL). **INT64_MIN handled without
  UB/overflow** precisely because the negation result is consumed as unsigned.
- Lean: `.negSucc 9223372036854775807` ⇒ `"-" ++ natToString (9223372036854775807
  + 1) = "-" ++ natToString 9223372036854775808 = "-9223372036854775808"`.
  **Match.** (Lean has no overflow: `m+1` is `Nat` arithmetic; the magnitude
  `2^63` is representable.)

**Verdict: byte-for-byte identical on every `Int` in `[INT64_MIN, INT64_MAX]`,
including 0, -1, and INT64_MIN, provided the result fits in `n` (it always does:
≤ 20 bytes + NUL ≪ 64).**

---

## 4. Dead branches for the fixed call shape

For (format = exactly `"%lld"`) ∧ (FILE = `__SSTR|__SWR` string sink, `_w = 63`)
∧ (no floats) ∧ (C locale, `grouping=""`):

| dead region | guard that kills it | how discharged |
|---|---|---|
| `_dtoa_r` / float conversion (`0x80009a74`, `0x80009fe0`, `0x8000a62c`) | conversion char ∈ {e,f,g,a}; `%lld`→`d` | `decide` on the `beq s6,<'F'/'G'/'E'>` dispatch |
| `__muldi3`/`__divdi3`/`__moddi3` (float scaling) + 2nd `__umoddi3` `0x8000a170` | reached only under the float case | dead once float case dead |
| `__eqdf2`/`__ledf2`/`__gedf2`/`__unorddf2`/`__floatsidf`/… | float compares | dead once float case dead |
| `_wcsrtombs_r`/`_wcrtomb_r` (`%ls`/`%lc`) | wide-char conversion char | dead (`%lld`→`d`) |
| grouping / thousands-sep (`0x8000833c…`) | `t1 & 1024` (grouping flag) = 0 **and** C-locale `grouping[0]==0` | `decide` (flag not set by `"%lld"`) + `_localeconv_r` returns `grouping=""` |
| width/precision padding (`memset` pad loops `0x800097d4`,`0x80009884`; blanks/zeroes fill) | no `width`/`.prec` in `"%lld"` | `decide` (parse sets width=prec=0) |
| `__ssputs_r` grow branch + `_malloc_r`/`_realloc_r` (`0x800143f4…`) | `bgeu a3,s1` (chunk ≥ `_w`) **or** `_flags & 0x480` | `decide`: `_flags=0x0208 ⇒ &0x480=0`; and `len ≤ 20 < 63 = _w` |
| `_svfprintf_r` overflow/error returns (`0x80005c70`,`0x80005cc0`) | `size > SSIZE_MAX`; ret `< -1` | `decide` (`size=64`) |
| stringify malloc-fail (`0x80003140` fwrite+exit(1)) | `beqz a0` after `malloc` | handled by `malloc_spec`'s non-NULL success case; the fail case is a separate (provable) `exit(1)` triple |

The **only live** integer-path segments: the format parse of 4 chars, the sign
test + `neg`, the decimal loop (§1.4), one `__ssprint_r`/`__ssputs_r` flush
(memmove), the NUL write. The float dispatch tests are the biggest quantitative
dead weight (they gate ~2/3 of the 3212 instructions); once `conversion-char = d`
is pinned, `decide` prunes them at the dispatch `beq`s.

---

## 5. Proposed Lean spec shapes (statements only)

Idiom: `M3-pilot-design.md` — `Triple`, `Ust`/`St` config predicate with the
blanket ghost-frame `hframe`, `StepObs` steps, `tick < 2`, `minstret` ∃-bound.
`P`/`Q` name exactly the memory regions read/written. Written but not shown:
`NotWritten` abbrevs per function.

### 5.1 `snprintf_lld_spec` (the top-level obligation)

The load-bearing spec: `snprintf(buf, n, "%lld", v)` writes `intToString v ++
[0]` to `buf` when it fits (it always does for `n ≥ 21`).

```
-- buf : BitVec 64  (dest address, = stringify's sp+16)
-- n   : BitVec 64  (size, = 64 in the consumer)
-- fmt : BitVec 64  (= 0x800192c0, the "%lld" rodata)
-- v   : BitVec 64  (the signed 64-bit value, from Value.as.i)
-- m0  : Mem
-- g   : ghost frame
def snprintf_lld_pre (buf n fmt v m0 g) (c) : Prop :=
  GoodState c.σ ∧ CodeLoadedSnprintf c.σ ∧ CodeLoadedSvfprintf c.σ ∧
  CodeLoadedDivCluster c.σ ∧ CodeLoadedSsprint c.σ ∧ CodeLoadedMemmove c.σ ∧
  c.σ.mem = m0 ∧ PC c = 0x80005c44 ∧
  x10 c = buf ∧ x11 c = n ∧ x12 c = fmt ∧ x13 c = v ∧      -- a0..a3
  Reads4 m0 fmt "%lld\0" ∧ n.toNat ≥ 21 ∧                  -- fits: max 20 + NUL
  WritableWindow m0 buf n.toNat ∧                          -- buf..buf+n in RAM, disjoint code/tohost
  c.tick < 2 ∧ (∃ k, minstret c = some k) ∧
  (∀ R, NotWrittenSnprintf R → c.σ.regs.get? R = g R)

def snprintf_lld_post (buf n fmt v m0 g) (c) : Prop :=
  GoodState c.σ ∧ PC c = <ret addr> ∧
  -- memory: buf holds intToString v then NUL, rest of buf-window unconstrained, else = m0
  WritesStr c.σ.mem m0 buf (intToStringBytes v) ∧          -- bytes = (intToString v).toUTF8 ++ [0]
  x10 c = (intToString v).length ∧                         -- snprintf returns char count
  c.tick < 2 ∧ (∃ k, minstret c = some k) ∧
  (∀ R, NotWrittenSnprintf R → c.σ.regs.get? R = g R)

theorem snprintf_lld_spec : Triple (snprintf_lld_pre …) (snprintf_lld_post …)
```

`intToStringBytes v` is the bridge lemma target: `= (intToString v).toUTF8 ++
[0#8]` — all ASCII, so `toUTF8` is `List.map Char.toUInt8`. The proof composes
§5.2–5.4.

### 5.2 `svfprintf_lld_spec` (the sliced format-engine spec)

The 3212-inst body restricted to the `"%lld"` + string-sink slice. Pins the FILE
fields (§2) and the format bytes; asserts the sink buffer receives
`intToString v`.

```
-- file : BitVec 64 (address of the sink FILE, = snprintf's sp+8)
-- Requires the sink's _flags=0x0208, _w≥21, _p=_bf._base=buf   (pinned in P)
def svfprintf_lld_pre (reent file buf v m0 g) (c) : Prop :=
  GoodState c.σ ∧ … ∧ PC c = 0x80007654 ∧
  x11 c = file ∧                                            -- a1 = FILE*
  Reads2 m0 (file+16) 0x0208 ∧ Reads4 m0 (file+12) w ∧ w ≥ 21 ∧
  Reads8 m0 (file+0) buf ∧ Reads8 m0 (file+24) buf ∧
  VaListHolds m0 (va_of c) v ∧                              -- the %lld arg = v
  Reads_fmt m0 "%lld\0" ∧ …
def svfprintf_lld_post (…) (c) : Prop :=
  GoodState c.σ ∧ PC c = <ret> ∧
  WritesStr c.σ.mem m0 buf ((intToString v).toUTF8) ∧      -- sink writes digits (NO NUL — snprintf adds it)
  x10 c = (intToString v).length ∧ …
```

Proof strategy: (i) `decide`-prune the float/wide/grouping/pad dead branches
(§4) using the pinned fmt + flags; (ii) reduce to the sign-test + decimal loop +
one flush; (iii) invoke §5.3 (loop) and §5.4 (flush).

### 5.3 `decimalLoop_spec` (the induction — biggest risk, the load-bearing lemma)

A `Triple` over the loop `0x800082c8 … 0x80008358` (plus the fast-path
`0x80008108`). Consumes the **verified** `__umoddi3`/`__hidden___udivdi3` specs
per iteration.

```
-- entry: a4 = magnitude m (unsigned Nat < 2^64), scratch cursor s9 = sp+348
-- invariant LoopI: bytes already written [cursor, top) = natDigitsSuffix m_orig k
--                  ∧ running n = m_orig / 10^k  ∧ cursor = top - k
-- measure LoopMu = n.toNat   (strictly decreasing: n/10 < n for n > 9, shr-style)
-- guard  LoopB  = "n > 9"
theorem decimalLoop_spec :
  Triple (loop_pre m buf_scratch …)
         (fun c => digitsWritten c = natDigits (m+1) m ∧ …)   -- byte list = natDigits
```

The arithmetic core (analogous to the pilot's `invmul_bv`): one identity
`natDigits (m+1) m = natDigits (m/10 + 1) (m/10) ++ [digitChar (m%10)]` for
`m ≥ 10`, plus the `digitChar d = '0'+d` (d ≤ 9) fact, plus the measure decrease
`m > 9 ⇒ (m/10).toNat < m.toNat`. **This is where the byte-for-byte equality is
actually proved.** Per-iteration the loop calls `__umoddi3` then
`__hidden___udivdi3`; each is discharged by the div-cluster spec at its `jal`
site (with the ghost frame recovering the loop's live registers across the call,
per the pilot's t0-survival amendment). **Biggest risk:** threading the loop's
callee-saved live set (`s0,s6,s7,s9,s10,s11`, the cursor + count + running value)
across **two** `jal`s per iteration into the div core — the div spec must return
every untouched register (blanket ghost frame), and the loop invariant must
re-establish them each back-edge.

### 5.4 `ssprint_flush_spec` (the sink → buffer copy)

`__ssprint_r`/`__ssputs_r` fast path: `Triple` showing the collected iov bytes
are `memmove`d into `buf`, `_p`/`_w` updated, **grow branch dead**. Consumes the
verified `memmove_spec` (or `memcpy_spec`).

```
theorem ssputs_fast_spec :
  Triple (ssputs_pre file src len m0 g)            -- _flags=0x0208, len < _w
         (fun c => WritesBytes c.σ.mem m0 (p0) (bytesOf src len) ∧   -- memmove'd
                   Reads8 c.σ.mem (file+0) (p0+len) ∧                -- _p advanced
                   Reads4 c.σ.mem (file+12) (w0-len) ∧ …)            -- _w shrunk
```

### 5.5 `stringify_int_spec` (the consumer)

Composes `snprintf_lld_spec` + `strlen_spec` + `malloc_spec` + `memcpy_spec` to
show `stringify (Value.int v)` returns a fresh heap buffer holding
`intToString v ++ [0]`.

```
def stringify_int_post (valptr v m0 g) (c) : Prop :=
  GoodState c.σ ∧ PC c = <ret> ∧
  (∃ s, x10 c = s ∧ FreshRegion m0 s ((intToString v).length + 1) ∧
        WritesStr c.σ.mem m0 s (intToStringBytes v)) ∧            -- OR malloc failed → exit(1)
  …
```

`malloc` is a `MallocContract` consumer: on success a fresh disjoint
`len+1`-byte region; on NULL the `beqz a0,0x80003140` branch → `fwrite` +
`exit(1)` (a separate, small, provable divergent triple ⇒ `Halts c out 1`).

### 5.6 Which existing verified specs get consumed

| verified spec | consumed at | count saved |
|---|---|---|
| `__umoddi3` / `__hidden___udivdi3` (div cluster) | decimal loop, once each per digit (§1.4) | 27/digit |
| `__muldi3` | **not consumed** (float only) | — |
| `memmove` (or `memcpy`) | `__ssputs_r` fast path (§1.6) | ~117 |
| `memcpy` | `stringify` tail heap-copy (§1.1) | 64 |
| `strlen` | `stringify` `strlen(buf)`; `_svfprintf_r` prologue `strlen(".")` | 43 |
| `malloc_spec` (MallocContract) | `stringify` result buffer (§1.1) | — |

---

## 6. Risks / blockers

**(a) `_svfprintf_r` is 3212 instructions; the output IS constrained.** Unlike
the setjmp brief's `_vfprintf_r` (where "route around output" was legal because
the diagnostic text is unconstrained), here `stringify` must produce **exactly**
`intToString v`, so the decimal loop must be simulated character-exact. Mitigation
is the **format-slice** (§5.2): pin `fmt="%lld"` + string-sink flags and
`decide`-prune every float/wide/grouping/pad branch (§4), collapsing the live
slice to a few hundred instructions. The residual character-exact obligation is
the §5.3 decimal loop only.

**(b) The decimal loop threads live registers across TWO `jal`s per iteration
(THE BIGGEST RISK).** Each digit calls `__umoddi3` then `__hidden___udivdi3`; the
loop's live set (`s0`=running n, `s6`/`s7`=exit-test/count, `s9`/`s10`=cursor,
`s11`=grouping flag) must survive both. Requires the div-cluster specs to carry
the **blanket ghost frame** (return every untouched register — exactly the
pilot's post-hoc amendment that fixed `__umoddi3`'s t0), and the loop invariant to
re-establish the live set on each back-edge. `s0` (the running value) is the one
the div core *does* clobber via a0 — must be reloaded from `__hidden___udivdi3`'s
result, tracked in the invariant.

**(c) `neg` on INT64_MIN — resolved, not a risk.** The C path's `neg a4,a4` on
`0x8000000000000000` yields `0x8000000000000000`, consumed as **unsigned** `2^63`
by the div loop. No signed overflow/UB is exercised (the value is never used as a
signed quantity after `neg`). `intToString` agrees (`.negSucc` carries `m+1` as
`Nat`). The spec must model `neg` as `BitVec.neg` (wrapping) and the loop input as
`(neg a4).toNat`, then prove `(neg a4).toNat = |v|` for `v < 0` including
INT64_MIN. **Resolved by §3.3; encode as a `BitVec.toNat_neg` lemma.**

**(d) Format-string and rodata byte-pins.** `snprintf_lld_pre` must pin
`[0x800192c0] = "%lld\0"` (5 bytes) and the C-locale `grouping`/`decimal_point`
statics that `_localeconv_r` returns (`gp+904` region). These are static-data
byte-pins in the M1 init-footprint style; the grouping pin (`grouping[0]==0`) is
needed to kill the thousands-separator branch (§4). **Action: add the `"%lld"`
rodata pin and the C-locale `grouping=""`/`decimal_point="."` pins to
`CodeLoadedSvfprintf`/a data-loaded predicate.**

**(e) String-sink FILE field pins.** `svfprintf_lld_pre` pins 5 FILE fields
(§2). These are on `snprintf`'s **stack**, written by `snprintf` immediately
before the `jal` — so the composition `snprintf_lld_spec` establishes them as the
post-of-the-setup / pre-of-`svfprintf`. No aliasing risk: the FILE is at `sp+8`,
`buf` is the caller's separate region; `DisjointWindows` by `decide` once
addresses are concrete. **The `_w = 63 ≫ 20` bound is what makes the grow branch
dead** — must be carried as `_w ≥ 21` (the max digit count for a signed 64-bit
value is 20).

**(f) `_localeconv_r` returns a static pointer — trivial (2 insts).** `addi
a0,gp,904; ret`. No reentrancy, no allocation. Its result (the C locale) is a
data pin (risk (d)). **Not a risk.**

**(g) DecodeTable: NO gap.** Unlike the setjmp exit path (42 missing words), the
entire snprintf/`%lld` path is fully covered (§0, verified per-function: 0
missing across all 14 functions incl. `_svfprintf_r`'s 1621 distinct words). The
path is reached from `interp_run` via direct `jal`s (`stringify`←`eval_binary`,
`snprintf`, `_svfprintf_r`, `__ssprint_r`), so `disasm_reachable.py`'s
direct-`jal` closure already included it. **No blocker here.**

---

## Appendix — quick address index

| symbol | addr | insts | DT | role |
|---|---|---|---|---|
| `stringify` | 0x80002fc0 | 105 | ok | VAL_INT → snprintf "%lld"; other arms strcpy/copy; tail malloc+memcpy |
| `snprintf` | 0x80005c44 | 46 | ok | builds `__SSTR\|__SWR` string sink → _svfprintf_r; writes NUL |
| `_snprintf_r` | 0x80005b74 | 52 | ok | reentrant variant (not on stringify's path; stringify uses `snprintf`) |
| `_svfprintf_r` | 0x80007654 | 3212 | ok | string-sink format engine; slice = parse+sign+decimal loop+flush |
| `__hidden___udivdi3` | 0x800046ac | 18 | ok | **VERIFIED** shift-subtract n/10 |
| `__umoddi3` | 0x800046f4 | 9 | ok | **VERIFIED** n%10 (wraps udivdi3; saves ra in t0) |
| `__muldi3` | 0x80004640 | — | ok | **VERIFIED** but NOT consumed (float path only) |
| `__ssprint_r` | 0x8000e908 | 60 | ok | flush iovec → __ssputs_r |
| `__ssputs_r` | 0x8001438c | 101 | ok | fast path memmove into buf; grow/malloc branch DEAD |
| `memmove` | 0x800069c4 | ~117 | ok | **VERIFIED** class; sink copy |
| `memcpy` | 0x80006bc8 | 64 | ok | **VERIFIED**; stringify heap copy |
| `strlen` | 0x80006cf0 | 43 | ok | **VERIFIED**; stringify + svfprintf prologue |
| `malloc` | 0x80004790 | 3 | ok | → _malloc_r; MallocContract |
| `_malloc_r` | 0x800047a8 | 425 | ok | allocator (stringify result buf); DEAD inside svfprintf slice |
| `fwrite` | 0x80005260 | — | ok | stringify malloc-fail branch only |
| `_localeconv_r` | 0x80010258 | 2 | ok | returns &C-locale (grouping="" ⇒ %'d dead) |

Digit-conversion loop: `0x800082c8 … 0x80008358` (div `0x80008304`, mod
`0x80008324`, backward emit `0x8000832c`). Fast path (mag ≤ 9): `0x80008108`.
Sign/negate: `0x800080ec … 0x800080f4`. All within the DecodeTable.
