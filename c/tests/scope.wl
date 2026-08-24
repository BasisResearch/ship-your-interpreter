// local variables, shadowing, block scope
var x = 1;
{
    var x = 2;
    println(x);
    x = 3;
    println(x);
}
println(x);

var y = 10;
{
    y = 20;
}
println(y);

var g = 5;
fn shadow(g) { return g * 2; }
println(shadow(7), g);

var count = 0;
while (count < 3) {
    var local = count * 10;
    count = count + 1;
}
println(count);

// assert builtin works
assert(1 + 1 == 2, "math is broken");
println("asserts ok");
