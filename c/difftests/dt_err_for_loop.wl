// DIFFTEST-ERROR: hVarUndef,hExpr,hFlBody,hFlLoop,hForLoop,hSeqTail
var i = 0;
for (; i < 2; i = i + 1) { if (i == 1) { missing; } }
