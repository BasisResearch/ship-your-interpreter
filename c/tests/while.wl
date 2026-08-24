// while loops, break, continue, nesting
var i = 0;
var sum = 0;
while (i < 10) {
    i = i + 1;
    sum = sum + i;
}
println(sum);

var n = 0;
var total = 0;
while (true) {
    n = n + 1;
    if (n > 100) { break; }
    if (n % 2 == 0) { continue; }
    total = total + n;
}
println(total);

var acc = 0;
var a = 1;
while (a <= 3) {
    var b = 1;
    while (b <= 3) {
        acc = acc + a * b;
        b = b + 1;
    }
    a = a + 1;
}
println(acc);
