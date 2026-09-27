#!/usr/bin/env bash
# Tests for the `whilecheck` executable (parser, inference, verified checker).
# Usage: scripts/test_whilecheck.sh   (after `lake build whilecheck`)
set -u
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/whilecheck
fail=0

"$BIN" --selftest c/tests >/dev/null || { echo "FAIL: parser selftest"; fail=1; }

expect() {  # expect accept|reject FILE
  if "$BIN" "$2" >/dev/null; then got=accept; else got=reject; fi
  [ "$got" = "$1" ] || { echo "FAIL: $2: expected $1, got $got"; fail=1; }
}
for t in arithmetic err_divzero for functions scope strings while; do
  expect accept "c/tests/$t.wl"
done
for t in err_parse err_undefined recursion; do
  expect reject "c/tests/$t.wl"
done

tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
case_() { printf '%s\n' "$3" > "$tmp/$2.wl"; expect "$1" "$tmp/$2.wl"; }
case_ accept strcat 'fn g(s, n) { var r = ""; for (var k = 0; k < n; k = k + 1) { r = r + s; } return r; } println(g("a", 3));'
case_ accept higher 'fn apply(f, v) { return f(v); } println(apply(fn (q) { return q < "m"; }, "abc"));'
case_ accept natives 'var p = println; p(1, "x", true); assert(1 == 1, "msg");'
case_ accept noreturn 'fn f(x) { println(x); } f(1);'
case_ accept lateTypes 'fn k(a, b) { var c = a + b; return c < "m"; } var w = k(1, "s");'
case_ accept nativeParam 'fn apply(f) { return f(1); } var r = apply(println);'
case_ reject recursionFwd 'fn f(n) { return g(n); } fn g(n) { return n; }'
case_ reject strminus 'println("a" - 1);'
case_ reject retype 'var x = 1; x = "s";'
case_ reject fallthrough 'fn f(x) { if (x > 0) { return 1; } }'
case_ reject toplevelret 'return 1;'
case_ reject breakout 'break;'
case_ reject arity 'fn f(a) { return a; } f(1, 2);'
case_ reject assertarity 'assert();'
case_ reject callint 'var x = 1; x();'

# many ambiguous `+` before an error: rejected without exponential search
{ for i in $(seq 1 200); do echo "fn f$i(a$i, b$i) { return a$i + b$i; }"; done
  echo 'println("a" - 1);'; } > "$tmp/many.wl"
if timeout 20 "$BIN" "$tmp/many.wl" >/dev/null; then echo "FAIL: many.wl accepted"; fail=1
elif [ $? = 124 ]; then echo "FAIL: many.wl timed out"; fail=1; fi

[ $fail = 0 ] && echo "whilecheck tests: OK"
exit $fail
