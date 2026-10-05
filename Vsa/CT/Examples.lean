import Vsa.CT.Transfer
import Vsa.While.Derive
import Vsa.Compiler.CompileSize

set_option maxRecDepth 4000000

namespace Vsa.CT.Examples

open Vsa.While Vsa.CT Vsa.Compiler

private def v (x : String) : Expr := .var x
private def i (n : Int) : Expr := .int n
private def set (x : String) (e : Expr) : Stmt := .expr (.assign x e)
private def add (a b : Expr) : Expr := .binary .add a b
private def sub (a b : Expr) : Expr := .binary .sub a b
private def mul (a b : Expr) : Expr := .binary .mul a b

def selSec (x : String) : Bool := x == "b" || x == "x" || x == "y" || x == "r"

def selBody : Program :=
  [.varDecl "r" (some (add (v "y") (mul (v "b") (sub (v "x") (v "y"))))),
   .expr (.call (v "println") [v "r"])]

def selIns (b x y : Int) : List (String × Int) := [("b", b), ("x", x), ("y", y)]

theorem sel_ct : ctSeq selSec selBody = true := by decide

def eqSec (x : String) : Bool := x == "a0" || x == "a1" || x == "a2" || x == "a3" || x == "acc"

def eqBody : Program :=
  [.varDecl "acc" (some (i 0))] ++
    (["0", "1", "2", "3"].map fun j =>
      set "acc" (add (v "acc") (mul (sub (v ("a" ++ j)) (v ("c" ++ j))) (sub (v ("a" ++ j)) (v ("c" ++ j)))))) ++
    [.expr (.call (v "println") [v "acc"])]

def eqIns (a : List Int) : List (String × Int) :=
  (List.zip ["a0", "a1", "a2", "a3"] a) ++ (List.zip ["c0", "c1", "c2", "c3"] [1, 2, 3, 5])

theorem eq_ct : ctSeq eqSec eqBody = true := by decide


def cswap (b : String) : List Stmt :=
  [set "d" (mul (v b) (sub (v "r0") (v "r1"))),
   set "r0" (sub (v "r0") (v "d")),
   set "r1" (add (v "r1") (v "d"))]

def ladStep (b : String) : List Stmt :=
  cswap b ++ [set "r1" (mul (v "r0") (v "r1")), set "r0" (mul (v "r0") (v "r0"))] ++ cswap b

def ladBits : List String := ["k7", "k6", "k5", "k4", "k3", "k2", "k1", "k0"]

def ladSec (x : String) : Bool := (["r0", "r1", "d"] ++ ladBits).contains x

def ladBody : Program :=
  [.varDecl "r0" (some (i 1)), .varDecl "r1" (some (v "x")), .varDecl "d" (some (i 0))] ++
    ladBits.flatMap ladStep ++ [.expr (.call (v "println") [v "r0"])]

def ladIns (k : List Int) : List (String × Int) := ("x", 3) :: List.zip ladBits k

theorem lad_ct : ctSeq ladSec ladBody = true := by decide

theorem sel_sup : Supported (prog selSec (selIns 0 0 0) selBody) := by
  simp [Supported, prog, inDecl, selIns, selSec, selBody, SupSeq, SupS, IntE, BoolE, CondE, v, add, sub,
    mul, NScope.declare, NScope.Mem, IsNative, InRange, ArithOp, CmpOp, SupArgs, maxArgs, encLit, encAux,
    chunkI]

theorem sel_fit : 0x80004800 + 4 * (compile (prog selSec (selIns 0 0 0) selBody)).length ≤ 0x8001ad00 := by
  have := compile_length_le (prog selSec (selIns 0 0 0) selBody)
  have hs : seqSize (prog selSec (selIns 0 0 0) selBody) ≤ 2000 := by decide
  omega

theorem eq_sup : Supported (prog eqSec (eqIns [0, 0, 0, 0]) eqBody) := by
  simp [Supported, prog, inDecl, eqIns, eqSec, eqBody, SupSeq, SupS, IntE, BoolE, CondE, v, i, set, add,
    sub, mul, NScope.declare, NScope.Mem, IsNative, InRange, ArithOp, CmpOp, SupArgs, maxArgs, encLit, encAux,
    chunkI]

theorem eq_fit : 0x80004800 + 4 * (compile (prog eqSec (eqIns [0, 0, 0, 0]) eqBody)).length ≤
    0x8001ad00 := by
  have := compile_length_le (prog eqSec (eqIns [0, 0, 0, 0]) eqBody)
  have hs : seqSize (prog eqSec (eqIns [0, 0, 0, 0]) eqBody) ≤ 4000 := by decide
  omega

theorem lad_sup : Supported (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladBody) := by
  simp [Supported, prog, inDecl, ladIns, ladSec, ladBody, ladBits, ladStep, cswap, SupSeq, SupS, IntE, BoolE,
    CondE, v, i, set, add, sub, mul, NScope.declare, NScope.Mem, IsNative, InRange, ArithOp, CmpOp, SupArgs,
    maxArgs, encLit, encAux, chunkI]

theorem lad_fit : 0x80004800 + 4 * (compile (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladBody)).length ≤
    0x8001ad00 := by
  have := compile_length_le (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladBody)
  have hs : seqSize (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladBody) ≤ 20000 := by decide
  omega

theorem sel_low (b x y b' x' y' : Int) : LowIns selSec (selIns b x y) (selIns b' x' y') :=
  .cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide))
    (.cons (fun h => absurd h (by decide)) .nil))

theorem sel_machine (b x y b' x' y' : Int) {c1 c2 : Vsa.Machine.Config}
    (hb1 : Boot (prog selSec (selIns b x y) selBody) c1) (hb2 : Boot (prog selSec (selIns b' x' y') selBody) c2)
    {o1 : String} (hh1 : Vsa.Machine.Halts c1 o1 0) :
    ∃ o2 ℓ1 ℓ2, BigStepL (prog selSec (selIns b x y) selBody) o1 ℓ1 ∧
      BigStepL (prog selSec (selIns b' x' y') selBody) o2 ℓ2 ∧ Vsa.Machine.Halts c2 o2 0 ∧
      skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → o1 = o2 ∧ ∃ T : List (BitVec 64),
        (∃ c' σf, Vsa.Machine.RunT c1 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o1) ∧
        (∃ c' σf, Vsa.Machine.RunT c2 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o2)) :=
  ct_machine' sel_ct (by simp [selIns, isNat]) (sel_low b x y b' x' y')
    (sup_transfer _ _ (sel_low 0 0 0 b x y) _ _ sel_sup)
    (by rw [← len_transfer _ _ (sel_low 0 0 0 b x y)]; exact sel_fit) hb1 hb2 hh1

theorem sel_valid : BigStep (prog selSec (selIns 1 5 9) selBody) "5\n" := by bigstep_derive

theorem sel_halts {c : Vsa.Machine.Config} (hb : Boot (prog selSec (selIns 1 5 9) selBody) c) :
    Vsa.Machine.Halts c "5\n" 0 :=
  ((compile_correct _ (sup_transfer _ _ (sel_low 0 0 0 1 5 9) _ _ sel_sup)
    (by rw [← len_transfer _ _ (sel_low 0 0 0 1 5 9)]; exact sel_fit) c hb.good hb.tick hb.pc hb.pw hb.out
    hb.code hb.lib).1 _).mp sel_valid

theorem eq_valid : BigStep (prog eqSec (eqIns [1, 2, 3, 4]) eqBody) "1\n" := by bigstep_derive

theorem lad_valid : BigStep (prog ladSec (ladIns [1, 0, 1, 1, 0, 1, 0, 1]) ladBody)
    "2351117403390039091\n" := by bigstep_derive

theorem eq_low (a0 a1 a2 a3 b0 b1 b2 b3 : Int) :
    LowIns eqSec (eqIns [a0, a1, a2, a3]) (eqIns [b0, b1, b2, b3]) :=
  .cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide))
    (.cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide))
    (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) (.cons (fun _ => rfl) .nil)))))))

theorem eq_machine (a0 a1 a2 a3 b0 b1 b2 b3 : Int) {c1 c2 : Vsa.Machine.Config}
    (hb1 : Boot (prog eqSec (eqIns [a0, a1, a2, a3]) eqBody) c1)
    (hb2 : Boot (prog eqSec (eqIns [b0, b1, b2, b3]) eqBody) c2)
    {o1 : String} (hh1 : Vsa.Machine.Halts c1 o1 0) :
    ∃ o2 ℓ1 ℓ2, BigStepL (prog eqSec (eqIns [a0, a1, a2, a3]) eqBody) o1 ℓ1 ∧
      BigStepL (prog eqSec (eqIns [b0, b1, b2, b3]) eqBody) o2 ℓ2 ∧ Vsa.Machine.Halts c2 o2 0 ∧
      skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → o1 = o2 ∧ ∃ T : List (BitVec 64),
        (∃ c' σf, Vsa.Machine.RunT c1 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o1) ∧
        (∃ c' σf, Vsa.Machine.RunT c2 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o2)) :=
  ct_machine' eq_ct (by simp [eqIns, isNat]) (eq_low a0 a1 a2 a3 b0 b1 b2 b3)
    (sup_transfer _ _ (eq_low 0 0 0 0 a0 a1 a2 a3) _ _ eq_sup)
    (by rw [← len_transfer _ _ (eq_low 0 0 0 0 a0 a1 a2 a3)]; exact eq_fit) hb1 hb2 hh1

theorem eq_halts {c : Vsa.Machine.Config} (hb : Boot (prog eqSec (eqIns [1, 2, 3, 4]) eqBody) c) :
    Vsa.Machine.Halts c "1\n" 0 :=
  ((compile_correct _ (sup_transfer _ _ (eq_low 0 0 0 0 1 2 3 4) _ _ eq_sup)
    (by rw [← len_transfer _ _ (eq_low 0 0 0 0 1 2 3 4)]; exact eq_fit) c hb.good hb.tick hb.pc hb.pw
    hb.out hb.code hb.lib).1 _).mp eq_valid

theorem lad_low (k k' : List Int) (hk : k.length = 8) (hk' : k'.length = 8) :
    LowIns ladSec (ladIns k) (ladIns k') := by
  match k, k', hk, hk' with
  | [a7, a6, a5, a4, a3, a2, a1, a0], [b7, b6, b5, b4, b3, b2, b1, b0], _, _ =>
    exact .cons (fun _ => rfl) (.cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide))
      (.cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide))
      (.cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide))
      (.cons (fun h => absurd h (by decide)) (.cons (fun h => absurd h (by decide)) .nil))))))))

theorem lad_machine (k k' : List Int) (hk : k.length = 8) (hk' : k'.length = 8) {c1 c2 : Vsa.Machine.Config}
    (hb1 : Boot (prog ladSec (ladIns k) ladBody) c1) (hb2 : Boot (prog ladSec (ladIns k') ladBody) c2)
    {o1 : String} (hh1 : Vsa.Machine.Halts c1 o1 0) :
    ∃ o2 ℓ1 ℓ2, BigStepL (prog ladSec (ladIns k) ladBody) o1 ℓ1 ∧
      BigStepL (prog ladSec (ladIns k') ladBody) o2 ℓ2 ∧ Vsa.Machine.Halts c2 o2 0 ∧
      skelSs ℓ1 = skelSs ℓ2 ∧
      (outsSs ℓ1 = outsSs ℓ2 → o1 = o2 ∧ ∃ T : List (BitVec 64),
        (∃ c' σf, Vsa.Machine.RunT c1 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o1) ∧
        (∃ c' σf, Vsa.Machine.RunT c2 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o2)) := by
  have hnat : ∀ p ∈ ladIns k, isNat p.1 = false := by
    match k, hk with
    | [_, _, _, _, _, _, _, _], _ => simp [ladIns, ladBits, isNat]
  exact ct_machine' lad_ct hnat (lad_low k k' hk hk')
    (sup_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] k rfl hk) _ _ lad_sup)
    (by rw [← len_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] k rfl hk)]; exact lad_fit) hb1 hb2 hh1

theorem lad_halts {c : Vsa.Machine.Config} (hb : Boot (prog ladSec (ladIns [1, 0, 1, 1, 0, 1, 0, 1]) ladBody) c) :
    Vsa.Machine.Halts c "2351117403390039091\n" 0 :=
  ((compile_correct _ (sup_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] _ rfl rfl) _ _ lad_sup)
    (by rw [← len_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] [1, 0, 1, 1, 0, 1, 0, 1] rfl rfl)];
        exact lad_fit) c hb.good hb.tick hb.pc hb.pw hb.out hb.code hb.lib).1 _).mp lad_valid

def ladPubBody : Program :=
  [.varDecl "r0" (some (i 1)), .varDecl "r1" (some (v "x")), .varDecl "d" (some (i 0))] ++
    ladBits.flatMap ladStep ++ [.expr (.call (v "println") [i 1])]

theorem ladPub_ct : ctSeqPub ladSec ladPubBody = true := by decide

theorem ladPub_sup : Supported (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladPubBody) := by
  simp [Supported, prog, inDecl, ladIns, ladSec, ladPubBody, ladBits, ladStep, cswap, SupSeq, SupS, IntE,
    BoolE, CondE, v, i, set, add, sub, mul, NScope.declare, NScope.Mem, IsNative, InRange, ArithOp, SupArgs,
    maxArgs, encLit, encAux, chunkI]

theorem ladPub_fit :
    0x80004800 + 4 * (compile (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladPubBody)).length ≤
      0x8001ad00 := by
  have := compile_length_le (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladPubBody)
  have hs : seqSize (prog ladSec (ladIns [0, 0, 0, 0, 0, 0, 0, 0]) ladPubBody) ≤ 20000 := by decide
  omega

theorem ladPub_machine (k k' : List Int) (hk : k.length = 8) (hk' : k'.length = 8)
    {c1 c2 : Vsa.Machine.Config} (hb1 : Boot (prog ladSec (ladIns k) ladPubBody) c1)
    (hb2 : Boot (prog ladSec (ladIns k') ladPubBody) c2) {o : String} (hh1 : Vsa.Machine.Halts c1 o 0) :
    Vsa.Machine.Halts c2 o 0 ∧ ∃ T : List (BitVec 64),
      (∃ c' σf, Vsa.Machine.RunT c1 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o) ∧
      (∃ c' σf, Vsa.Machine.RunT c2 T c' ∧ Vsa.Machine.Halted c' 0 σf ∧ Vsa.Machine.output σf = o) := by
  have hnat : ∀ p ∈ ladIns k, isNat p.1 = false := by
    match k, hk with
    | [_, _, _, _, _, _, _, _], _ => simp [ladIns, ladBits, isNat]
  exact ct_machine_pub' ladPub_ct hnat (lad_low k k' hk hk')
    (sup_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] k rfl hk) _ _ ladPub_sup)
    (by rw [← len_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] k rfl hk)]; exact ladPub_fit) hb1 hb2 hh1

theorem ladPub_valid : BigStep (prog ladSec (ladIns [1, 0, 1, 1, 0, 1, 0, 1]) ladPubBody) "1\n" := by
  bigstep_derive

theorem ladPub_halts {c : Vsa.Machine.Config}
    (hb : Boot (prog ladSec (ladIns [1, 0, 1, 1, 0, 1, 0, 1]) ladPubBody) c) :
    Vsa.Machine.Halts c "1\n" 0 :=
  ((compile_correct _ (sup_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] _ rfl rfl) _ _ ladPub_sup)
    (by rw [← len_transfer _ _ (lad_low [0, 0, 0, 0, 0, 0, 0, 0] [1, 0, 1, 1, 0, 1, 0, 1] rfl rfl)];
        exact ladPub_fit) c hb.good hb.tick hb.pc hb.pw hb.out hb.code hb.lib).1 _).mp ladPub_valid

end Vsa.CT.Examples
