// for loops: fizzbuzz, accumulation, continue, degenerate forms
for (var i = 1; i <= 15; i = i + 1) {
    if (i % 15 == 0) { println("FizzBuzz"); }
    else if (i % 3 == 0) { println("Fizz"); }
    else if (i % 5 == 0) { println("Buzz"); }
    else { println(i); }
}

var sum = 0;
for (var i = 1; i <= 100; i = i + 1) { sum = sum + i; }
println(sum);

var s = 0;
for (var i = 1; i <= 10; i = i + 1) {
    if (i % 3 == 0) { continue; }
    s = s + i;
}
println(s);

var j = 0;
for (; j < 3;) { j = j + 1; }
println(j);

var line = "";
for (var i = 0; i < 5; i = i + 1) { line = line + i; }
println(line);
