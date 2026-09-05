println(null == null, null != 1);
println(true == true, true != false);
println(7 == 7, 7 != 8);
println("a" == "a", "a" != "b");
fn f() { return null; }
fn g() { return null; }
f();
println(f == f, f != g);
println(print == print, print != println);
println("x" + null, "x" + true, "x" + 7, "x" + "s", "x" + f, "x" + print);
