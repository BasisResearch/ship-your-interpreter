import Vsa.CT.Agree

namespace Vsa.CT

open Vsa.While

inductive Ty where
  | int | bool
  deriving DecidableEq, Repr

def isNat (x : String) : Bool := x == "print" || x == "println" || x == "assert"

def arithB : BinOp → Bool
  | .add | .sub | .mul | .div | .mod => true
  | _ => false

def divB : BinOp → Bool
  | .div | .mod => true
  | _ => false

def ctE (sec : String → Bool) : Expr → Option (Ty × Bool)
  | .int _ => some (.int, false)
  | .bool _ => some (.bool, false)
  | .var x => if isNat x then none else some (.int, sec x)
  | .assign x e =>
    match ctE sec e with
    | some (.int, l) => if isNat x || (l && !sec x) then none else some (.int, l)
    | _ => none
  | .binary op l r =>
    match ctE sec l, ctE sec r with
    | some (.int, a), some (.int, b) =>
      if divB op then (if a || b then none else some (.int, false))
      else if arithB op then some (.int, a || b) else some (.bool, a || b)
    | _, _ => none
  | .unary .neg e =>
    match ctE sec e with
    | some (.int, l) => some (.int, l)
    | _ => none
  | .unary .not e =>
    match ctE sec e with
    | some (_, l) => some (.bool, l)
    | none => none
  | _ => none

def pubC (sec : String → Bool) (c : Expr) : Bool :=
  match ctE sec c with
  | some (_, false) => true
  | _ => false

def intArg (sec : String → Bool) (e : Expr) : Bool :=
  match ctE sec e with
  | some (.int, _) => true
  | _ => false

mutual

def ctS (sec : String → Bool) : Stmt → Bool
  | .expr (.call (.var f) args) =>
    (f == "print" || f == "println") && !sec f && decide (args.length ≤ maxArgs) &&
      args.all (intArg sec)
  | .expr e => (ctE sec e).isSome
  | .varDecl x (some e) =>
    !isNat x && match ctE sec e with
      | some (.int, l) => !l || sec x
      | _ => false
  | .block ss => ctSeq sec ss
  | .ifStmt c t none => pubC sec c && ctS sec t
  | .ifStmt c t (some e) => pubC sec c && ctS sec t && ctS sec e
  | .whileStmt c b => pubC sec c && ctS sec b
  | .brk => true
  | .cont => true
  | _ => false

def ctSeq (sec : String → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => ctS sec s && ctSeq sec ss

end

def pubArg (sec : String → Bool) (e : Expr) : Bool :=
  match ctE sec e with
  | some (_, false) => true
  | _ => false

mutual

def ppS (sec : String → Bool) : Stmt → Bool
  | .expr (.call (.var _) args) => args.all (pubArg sec)
  | .block ss => ppSeq sec ss
  | .ifStmt _ t none => ppS sec t
  | .ifStmt _ t (some e) => ppS sec t && ppS sec e
  | .whileStmt _ b => ppS sec b
  | _ => true

def ppSeq (sec : String → Bool) : List Stmt → Bool
  | [] => true
  | s :: ss => ppS sec s && ppSeq sec ss

end

def ctSeqPub (sec : String → Bool) (body : Program) : Bool := ctSeq sec body && ppSeq sec body

mutual

def EL.skel : EL → EL
  | .leaf => .leaf
  | .asg l => .asg l.skel
  | .bin l r d => .bin l.skel r.skel d
  | .orT l => .orT l.skel
  | .orF l r => .orF l.skel r.skel
  | .andF l => .andF l.skel
  | .andT l r => .andT l.skel r.skel
  | .un l => .un l.skel
  | .call f args c => .call f.skel (skelEs args) c.skel
  | .fn => .fn

def skelEs : List EL → List EL
  | [] => []
  | l :: ls => l.skel :: skelEs ls

def CL.skel : CL → CL
  | .clo b => .clo (skelSs b)
  | .print _ => .print []
  | .println _ => .println []
  | .assert => .assert

def SL.skel : SL → SL
  | .expr l => .expr l.skel
  | .varInit l => .varInit l.skel
  | .varNull => .varNull
  | .block ss => .block (skelSs ss)
  | .ifT c s => .ifT c.skel s.skel
  | .ifF c s => .ifF c.skel s.skel
  | .ifN c => .ifN c.skel
  | .whileF c => .whileF c.skel
  | .whileBrk c b => .whileBrk c.skel b.skel
  | .whileRet c b => .whileRet c.skel b.skel
  | .whileLoop c b r => .whileLoop c.skel b.skel r.skel
  | .forS i lp => .forS (skelOS i) lp.skel
  | .ret l => .ret l.skel
  | .retNull => .retNull
  | .brk => .brk
  | .cont => .cont

def skelSs : List SL → List SL
  | [] => []
  | s :: ss => s.skel :: skelSs ss

def skelOS : Option SL → Option SL
  | none => none
  | some s => some s.skel

def skelOE : Option EL → Option EL
  | none => none
  | some l => some l.skel

def FL.skel : FL → FL
  | .condF c => .condF c.skel
  | .bodyBrk c b => .bodyBrk (skelOE c) b.skel
  | .bodyRet c b => .bodyRet (skelOE c) b.skel
  | .loop c b s r => .loop (skelOE c) b.skel (skelOE s) r.skel

end

mutual

def EL.outs : EL → List (List Value)
  | .leaf => []
  | .asg l => l.outs
  | .bin l r _ => l.outs ++ r.outs
  | .orT l => l.outs
  | .orF l r => l.outs ++ r.outs
  | .andF l => l.outs
  | .andT l r => l.outs ++ r.outs
  | .un l => l.outs
  | .call f args c => f.outs ++ outsEs args ++ c.outs
  | .fn => []

def outsEs : List EL → List (List Value)
  | [] => []
  | l :: ls => l.outs ++ outsEs ls

def CL.outs : CL → List (List Value)
  | .clo b => outsSs b
  | .print vs => [vs]
  | .println vs => [vs]
  | .assert => []

def SL.outs : SL → List (List Value)
  | .expr l => l.outs
  | .varInit l => l.outs
  | .varNull => []
  | .block ss => outsSs ss
  | .ifT c s => c.outs ++ s.outs
  | .ifF c s => c.outs ++ s.outs
  | .ifN c => c.outs
  | .whileF c => c.outs
  | .whileBrk c b => c.outs ++ b.outs
  | .whileRet c b => c.outs ++ b.outs
  | .whileLoop c b r => c.outs ++ b.outs ++ r.outs
  | .forS i lp => outsOS i ++ lp.outs
  | .ret l => l.outs
  | .retNull => []
  | .brk => []
  | .cont => []

def outsSs : List SL → List (List Value)
  | [] => []
  | s :: ss => s.outs ++ outsSs ss

def outsOS : Option SL → List (List Value)
  | none => []
  | some s => s.outs

def outsOE : Option EL → List (List Value)
  | none => []
  | some l => l.outs

def FL.outs : FL → List (List Value)
  | .condF c => c.outs
  | .bodyBrk c b => outsOE c ++ b.outs
  | .bodyRet c b => outsOE c ++ b.outs
  | .loop c b s r => outsOE c ++ b.outs ++ outsOE s ++ r.outs

end

end Vsa.CT
