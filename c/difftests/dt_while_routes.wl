// Witness every recursive while status route used by the SMT differential oracle.
var i = 0;
while (true) { i = i + 1; break; }
while (i < 2) { i = i + 1; }
fn return_from_while() { while (true) { return 7; } }
println(return_from_while());
