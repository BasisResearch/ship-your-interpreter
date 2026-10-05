import Vsa.Compiler.Gen

namespace Vsa.Compiler

def nez : List Ins := [.slt s3 a0 0, .slt a0 0 a0, .add a0 a0 s3]

def flip : List Ins := [.sub a0 0 a0, .addi a0 a0 1]

def ctMul : List Ins :=
  [.addi s3 0 0, .addi s4 0 64,
   .add s3 s3 s3, .slt s5 a1 0, .sub s5 0 s5, .and s5 s5 a0, .add s3 s3 s5, .add a1 a1 a1,
   .addi s4 s4 (-1), .br .ne s4 0 (BitVec.ofInt 13 (-4 * (7 : Nat))), mv a0 s3]

end Vsa.Compiler
