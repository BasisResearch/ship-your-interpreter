// DIFFTEST-ERROR: hVarUndef,hRet,hSeqHead,hBody,hCallC,hSeqTail
fn f() { return missing; }
f();
