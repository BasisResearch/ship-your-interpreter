// every integer binary operator arm, both operand orders
var a = 17;
var b = 5;
println(a + b, a - b, a * b, a / b, a % b);
println(a < b, a <= b, a > b, a >= b, a == b, a != b);
println(0 - a, -a, !false, !true);
println(a / (0 - b), a % (0 - b), (0 - a) / b, (0 - a) % b);
