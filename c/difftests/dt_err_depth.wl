// DIFFTEST-ERROR: hDepth,hCallC,hBody,hRet,hSeqHead,hSeqTail
fn f() { return f(); }
f();
