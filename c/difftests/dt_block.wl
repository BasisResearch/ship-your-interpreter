// ST_BLOCK nesting, scope shadowing, ST_IF all three shapes
var x = 1;
{ var x = 2; { var x = 3; println(x); } println(x); }
println(x);
if (x == 1) { println("a"); }
if (x == 9) { println("b"); } else { println("c"); }
if (x > 0) { if (x < 5) { println("d"); } }
var i = 0;
while (i < 3) { i = i + 1; if (i == 2) { continue; } println(i); }
