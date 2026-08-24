# While — a small imperative language, interpreted in C

A self-contained tree-walking interpreter (lexer → parser → AST →
evaluator) for a C-syntax "While" language. It builds as a normal host
binary and also cross-compiles to a bare-metal RISC-V kernel image that
runs under `qemu-system-riscv64` using semihosting for all I/O (stdio,
host file access, command line).

## The language

C-style syntax: `//` and `/* */` comments, `;`-terminated statements,
`{}` blocks. Values are 64-bit ints, bools, strings, `null`, and
first-class functions (closures).

```c
// declarations and arithmetic
var x = (1 + 2) * 3 % 4;

// control flow: if/else, while, for, break, continue
for (var i = 1; i <= 15; i = i + 1) {
    if (i % 15 == 0) { println("FizzBuzz"); }
    else if (i % 3 == 0) { println("Fizz"); }
    else if (i % 5 == 0) { println("Buzz"); }
    else { println(i); }
}

// recursion
fn fib(n) {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
}

// first-class functions and closures
fn make_counter() {
    var count = 0;
    return fn () { count = count + 1; return count; };
}
var tick = make_counter();
tick();
println(tick()); // 2

// strings concatenate with +, and + coerces the other side
println("fib(20) = " + fib(20));
```

Built-ins: `println(...)`, `print(...)`, `assert(cond, msg?)`.

Operators (C precedence): `||  &&  == !=  < <= > >=  + -  * / %  ! -`
with short-circuiting `&&`/`||`. Truthiness: `null`, `false`, and `0`
are falsy; everything else is truthy.

## Building and running

```sh
make            # host binary ./while
./while         # REPL (multi-line input works; ctrl-D exits)
./while prog.wl # run a script
make test       # test suite against the host binary
```

### RISC-V under QEMU

```sh
make riscv                            # cross-compile while-riscv.elf
make run-riscv                        # REPL under qemu-system-riscv64
make run-riscv SCRIPT=tests/for.wl    # run a (host) script file
make test-riscv                       # full test suite under QEMU
```

The RISC-V build is bare metal (`-machine virt -bios none`): `crt0.S`
sets up the stack and clears `.bss`, `link.ld` places the image at
0x80000000, and `semihost.c` implements newlib's syscalls (`_read`,
`_write`, `_open`, `_sbrk`, ...) on top of the RISC-V semihosting
protocol, which QEMU serves with `-semihosting-config enable=on`. That
is what lets the interpreter open script files that live on the host and
run its REPL over QEMU's stdin/stdout.

Toolchain: [xPack riscv-none-elf-gcc](https://github.com/xpack-dev-tools/riscv-none-elf-gcc-xpack)
(bundles newlib), expected under `~/toolchains/xpack-riscv-none-elf-gcc-*`
or overridable with `make riscv RISCV_CC=path/to/gcc`. Homebrew's
`riscv64-elf-gcc` does not ship a C library. QEMU: `brew install qemu`.

## Layout

```
src/lexer.[ch]    tokens
src/parser.[ch]   recursive-descent parser -> AST (ast.h)
src/value.[ch]    runtime values
src/env.[ch]      lexical environments (closures keep them alive)
src/interp.[ch]   tree-walking evaluator + builtins
src/main.c        REPL / script driver
src/crt0.S        bare-metal startup (RISC-V build only)
src/semihost.c    newlib syscalls over semihosting (RISC-V build only)
src/link.ld       linker script for the QEMU virt machine
tests/            *.wl scripts + *.expected output / *.err diagnostics
```

Design notes: AST and closure environments are heap-allocated and never
freed (no GC) — fine for scripts and REPL sessions, by design. Call
depth is capped at 1000 to turn runaway recursion into a runtime error
instead of a C stack overflow.
