// EX_FN, EX_CALL, closures, recursion, ST_RETURN with and without value
fn add(a, b) { return a + b; }
println(add(2, 3));
fn mk(n) { return fn (x) { return x + n; }; }
var f = mk(5);
println(f(4));
fn fact(n) { if (n <= 1) { return 1; } return n * fact(n - 1); }
println(fact(6));
fn v() { return; }
v();
println(add);
assert(true);
