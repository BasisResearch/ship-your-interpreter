// first-class functions: closures, higher-order functions, anonymous fns
fn make_adder(n) {
    return fn (x) { return x + n; };
}
var add5 = make_adder(5);
println(add5(10));

fn apply_twice(f, x) { return f(f(x)); }
println(apply_twice(add5, 1));
println(apply_twice(fn (x) { return x * x; }, 3));

fn make_counter() {
    var count = 0;
    return fn () {
        count = count + 1;
        return count;
    };
}
var c = make_counter();
c();
c();
println(c());
var c2 = make_counter();
println(c2());

var f = add5;
println(f == add5);
println(make_adder);
println(fn (x) { return x; });

fn compose(f, g) { return fn (x) { return f(g(x)); }; }
var inc = fn (x) { return x + 1; };
var dbl = fn (x) { return x * 2; };
println(compose(inc, dbl)(10));
