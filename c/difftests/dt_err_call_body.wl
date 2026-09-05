// DIFFTEST-ERROR: hVarUndef,hExpr,hSeqHead,hBody,hCallC,hSeqTail
fn f() { missing; }
f();
