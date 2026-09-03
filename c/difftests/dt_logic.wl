// EX_LOGICAL both short-circuit directions, EX_UNARY
var t = true;
var f = false;
println(t && t, t && f, f && t, f && f);
println(t || t, t || f, f || t, f || f);
println(!t, !f, !!t);
var n = 3;
println(-n, - -n);
if (t && !f) { println("and"); }
while (f) { println("never"); }
