# While language interpreter
#
#   make            build host binary ./while
#   make riscv      cross-compile ./while-riscv.elf (riscv64-elf-gcc)
#   make riscv-htif [HTIF_SCRIPT=path]  cross-compile ./while-riscv-htif.elf
#                   (HTIF hosts: Spike / sail-riscv Lean emulator; runs the
#                   embedded script, no REPL)
#   make run        host REPL
#   make run-riscv [SCRIPT=path]   run under qemu-system-riscv64
#   make test       run test suite against the host binary
#   make test-riscv run test suite under QEMU
#   make clean

CC       ?= cc
CFLAGS   ?= -std=c11 -O2 -g -Wall -Wextra

SRC      := src/lexer.c src/parser.c src/value.c src/env.c src/interp.c src/main.c
HDR      := src/lexer.h src/parser.h src/ast.h src/value.h src/env.h src/interp.h

# Cross toolchain: needs newlib, so prefer the xPack riscv-none-elf-gcc
# (Homebrew's riscv64-elf-gcc ships without a C library). Override with
# `make riscv RISCV_CC=...` if yours lives elsewhere.
XPACK_GCC    := $(firstword $(wildcard $(HOME)/toolchains/xpack-riscv-none-elf-gcc-*/bin/riscv-none-elf-gcc))
RISCV_CC     ?= $(if $(XPACK_GCC),$(XPACK_GCC),riscv-none-elf-gcc)
RISCV_CFLAGS ?= -std=gnu11 -O2 -Wall -Wextra -march=rv64imac_zicsr -mabi=lp64 \
                -mcmodel=medany -DWHILE_BAREMETAL
# HTIF build: plain rv64i because the Lean emulator's model was generated
# without the M extension -- mul/div come from libgcc's soft routines.
RISCV_HTIF_CFLAGS ?= -std=gnu11 -O2 -Wall -Wextra -march=rv64i -mabi=lp64 \
                     -mcmodel=medany -DWHILE_HTIF
HTIF_SCRIPT  ?= tests/while.wl
QEMU         ?= qemu-system-riscv64
# -serial none -monitor none: leave QEMU's stdin to the semihosting
# console, otherwise the UART mux swallows REPL input
QEMU_FLAGS   ?= -machine virt -cpu rv64 -m 256M -nographic -serial none \
                -monitor none -bios none

COMMA := ,
SEMIHOST_ARGS = enable=on$(COMMA)target=native$(COMMA)arg=while$(if $(SCRIPT),$(COMMA)arg=$(SCRIPT))

all: while

while: $(SRC) $(HDR)
	$(CC) $(CFLAGS) -o $@ $(SRC)

riscv: while-riscv.elf

while-riscv.elf: $(SRC) $(HDR) src/crt0.S src/semihost.c src/link.ld
	$(RISCV_CC) $(RISCV_CFLAGS) -nostartfiles -T src/link.ld \
	    -o $@ src/crt0.S src/semihost.c $(SRC)

riscv-htif: while-riscv-htif.elf

while-riscv-htif.elf: $(SRC) $(HDR) src/crt0.S src/htif.c src/script.S src/link.ld $(HTIF_SCRIPT)
	$(RISCV_CC) $(RISCV_HTIF_CFLAGS) -DSCRIPT_PATH='"$(HTIF_SCRIPT)"' \
	    -nostartfiles -T src/link.ld \
	    -o $@ src/crt0.S src/htif.c src/script.S $(SRC)

run: while
	./while

run-riscv: while-riscv.elf
	$(QEMU) $(QEMU_FLAGS) -semihosting-config $(SEMIHOST_ARGS) -kernel $<

test: while
	./tests/run_tests.sh host

test-riscv: while-riscv.elf
	./tests/run_tests.sh riscv

clean:
	rm -f while while-riscv.elf while-riscv-htif.elf
	rm -rf while.dSYM

.PHONY: all riscv riscv-htif run run-riscv test test-riscv clean
