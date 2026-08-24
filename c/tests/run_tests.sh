#!/bin/sh
# Run the While-language test suite.
#   run_tests.sh host    -- against ./while (default)
#   run_tests.sh riscv   -- against while-riscv.elf under qemu-system-riscv64
set -u
mode=${1:-host}
cd "$(dirname "$0")/.." || exit 1

QEMU=${QEMU:-qemu-system-riscv64}

QEMU_FLAGS="-machine virt -cpu rv64 -m 256M -nographic -serial none -monitor none -bios none"

if [ "$mode" = riscv ]; then
    BIN=while-riscv.elf
    run_prog() {
        # shellcheck disable=SC2086
        "$QEMU" $QEMU_FLAGS \
            -semihosting-config "enable=on,target=native,arg=while,arg=$1" \
            -kernel while-riscv.elf
    }
    run_repl() {
        # shellcheck disable=SC2086
        "$QEMU" $QEMU_FLAGS -semihosting-config "enable=on,target=native" \
            -kernel while-riscv.elf
    }
else
    BIN=./while
    run_prog() { ./while "$1"; }
    run_repl() { ./while; }
fi

if [ ! -e "$BIN" ]; then
    echo "error: $BIN not built (run 'make' or 'make riscv' first)" >&2
    exit 1
fi

pass=0
fail=0
tmpout=$(mktemp)
tmperr=$(mktemp)
trap 'rm -f "$tmpout" "$tmperr"' EXIT

report_fail() {
    fail=$((fail + 1))
    echo "FAIL $1: $2"
}

for t in tests/*.wl; do
    name=$(basename "$t" .wl)
    run_prog "$t" >"$tmpout" 2>"$tmperr"
    status=$?
    if [ -f "tests/$name.err" ]; then
        # error test: stderr must contain the expected diagnostic
        want=$(cat "tests/$name.err")
        if grep -qF "$want" "$tmperr"; then
            pass=$((pass + 1))
            echo "PASS $name"
        else
            report_fail "$name" "expected stderr containing \"$want\""
            sed 's/^/    stderr: /' "$tmperr"
        fi
    elif [ -f "tests/$name.expected" ]; then
        if [ "$status" -ne 0 ]; then
            report_fail "$name" "exit status $status"
            sed 's/^/    stderr: /' "$tmperr"
        elif cmp -s "$tmpout" "tests/$name.expected"; then
            pass=$((pass + 1))
            echo "PASS $name"
        else
            report_fail "$name" "output mismatch"
            diff "tests/$name.expected" "$tmpout" | sed 's/^/    /'
        fi
    else
        echo "SKIP $name (no .expected or .err file)"
    fi
done

# REPL smoke tests (piped stdin; on riscv this goes through the QEMU
# semihosting console)
banner="While language v1.0 -- C-style syntax, type ctrl-D to exit"

printf '1 + 2;\nvar x = 3;\nx * x;\n' | run_repl >"$tmpout" 2>&1
printf '%s\n> 3\n> > 9\n> \n' "$banner" >"$tmperr"
if cmp -s "$tmpout" "$tmperr"; then
    pass=$((pass + 1))
    echo "PASS repl_basic"
else
    report_fail repl_basic "output mismatch"
    diff "$tmperr" "$tmpout" | sed 's/^/    /'
fi

printf 'fn add(a, b) {\nreturn a + b;\n}\nadd(2, 3);\n' | run_repl >"$tmpout" 2>&1
printf '%s\n> .. .. > 5\n> \n' "$banner" >"$tmperr"
if cmp -s "$tmpout" "$tmperr"; then
    pass=$((pass + 1))
    echo "PASS repl_multiline"
else
    report_fail repl_multiline "output mismatch"
    diff "$tmperr" "$tmpout" | sed 's/^/    /'
fi

echo "----------------------------------------"
echo "$pass passed, $fail failed ($mode)"
[ "$fail" -eq 0 ]
