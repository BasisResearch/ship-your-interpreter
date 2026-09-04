// EX_UNARY with T_MINUS (hNeg, unop token 12) and EX_LOGICAL with a FALSE
// left operand (hOrFalse), driven to an exit and nothing else.  phase1 showed
// the unary and logical arms entered 15 and 13 times across the corpus while
// phase3b found no instance of hNeg or hOrFalse, so these two operators are
// isolated here.
var n = 7;
var m = -n;
println(m);
println(-m);
println(- -n);
var z = 0;
println(-z);
var f = false;
var t = true;
println(f || t);
println(f || f);
println(f || (n > 3));
if (f || t) { println("orfalse-taken"); }
