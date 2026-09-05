// DIFFTEST-ERROR: hVarUndef,hOrR,hWhileCond,hWhileLoop,hSeqTail
var i = 0;
while ((i = i + 1) < 2 || missing) {}
