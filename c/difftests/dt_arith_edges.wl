// Compiler-runtime helper edge cases reachable through the While interpreter.
var z = 0;
var o = 1;
var n = z - o;
var min = z - 9223372036854775807 - o;
println(z * z, o * o, n * n, min * 2);
println(7 / o, 7 / n, (z - 7) / 3, 7 / (z - 3), (z - 7) / (z - 3), min / n);
println(7 % o, 7 % n, (z - 7) % 3, 7 % (z - 3), (z - 7) % (z - 3), min % n);
