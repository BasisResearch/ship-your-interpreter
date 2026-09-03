// EX_NULL, ST_VAR with no init, null equality
var a;
println(a == null);
var b = null;
println(b != null, b == a);
if (b == null) { println("isnull"); } else { println("no"); }
fn f() { return; }
println(f() == null);
