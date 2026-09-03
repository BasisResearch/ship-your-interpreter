// ST_FOR, ST_BREAK, ST_CONTINUE, degenerate for
var s = 0;
for (var i = 1; i <= 6; i = i + 1) { s = s + i; }
println(s);
var t = 0;
for (var i = 0; i < 8; i = i + 1) {
  if (i % 3 == 0) { continue; }
  if (i > 6) { break; }
  t = t + i;
}
println(t);
var j = 0;
for (; j < 3;) { j = j + 1; }
println(j);
