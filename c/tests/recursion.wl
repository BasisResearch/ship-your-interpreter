// recursion: factorial, fibonacci, mutual recursion, ackermann
fn fact(n) {
    if (n <= 1) { return 1; }
    return n * fact(n - 1);
}
println(fact(10));

fn fib(n) {
    if (n < 2) { return n; }
    return fib(n - 1) + fib(n - 2);
}
println(fib(20));

fn is_even(n) {
    if (n == 0) { return true; }
    return is_odd(n - 1);
}
fn is_odd(n) {
    if (n == 0) { return false; }
    return is_even(n - 1);
}
println(is_even(10), is_odd(10));

fn ack(m, n) {
    if (m == 0) { return n + 1; }
    if (n == 0) { return ack(m - 1, 1); }
    return ack(m - 1, ack(m, n - 1));
}
println(ack(2, 3));
