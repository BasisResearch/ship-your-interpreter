import Vsa.Compiler.VRepr

namespace Vsa.Compiler

open Vsa.While

def addName (l : List String) (x : String) : List String := if x ∈ l then l else l ++ [x]

def addNames (l : List String) (xs : List String) : List String := xs.foldl addName l

def declsS : Stmt → List String
  | .varDecl x _ => [x]
  | .ifStmt _ t none => declsS t
  | .ifStmt _ t (some e) => declsS t ++ declsS e
  | .whileStmt _ b => declsS b
  | _ => []

def frameNames (pre : List String) (ss : List Stmt) : List String :=
  addNames [] (pre ++ ss.flatMap declsS)

def forNames (init : Option Stmt) (b : Stmt) : List String :=
  addNames [] ((match init with | some s => declsS s | none => []) ++ declsS b)

def globalNames (p : Program) : List String := frameNames ["print", "println", "assert"] p

def slotOf : List String → String → Option Nat
  | [], _ => none
  | y :: l, x => if y = x then some 0 else (slotOf l x).map (· + 1)

mutual
def strsE : Expr → List String
  | .str s => [s]
  | .assign _ e => strsE e
  | .binary _ l r => strsE l ++ strsE r
  | .logical _ l r => strsE l ++ strsE r
  | .unary _ e => strsE e
  | .call f args => strsE f ++ strsArgs args
  | .fn name _ body => [dispName name, catName name] ++ strsSeq body
  | _ => []

def strsArgs : List Expr → List String
  | [] => []
  | e :: es => strsE e ++ strsArgs es

def strsS : Stmt → List String
  | .expr e => strsE e
  | .varDecl _ (some e) => strsE e
  | .block ss => strsSeq ss
  | .ifStmt c t none => strsE c ++ strsS t
  | .ifStmt c t (some e) => strsE c ++ strsS t ++ strsS e
  | .whileStmt c b => strsE c ++ strsS b
  | .forStmt i c st b =>
    (match i with | some s => strsS s | none => []) ++ (match c with | some e => strsE e | none => []) ++
      (match st with | some e => strsE e | none => []) ++ strsS b
  | .ret (some e) => strsE e
  | _ => []

def strsSeq : List Stmt → List String
  | [] => []
  | s :: ss => strsS s ++ strsSeq ss
end

def strTab (p : Program) : List String := addNames fixedStrs (strsSeq p)

def strAddr (T : List String) (s : String) : Nat := objBase + strOff T (T.idxOf s)

mutual

def tE : Expr → Nat
  | .assign _ e => tE e
  | .binary _ l r => max (tE l) (tE r + 1)
  | .logical _ l r => max (tE l) (tE r)
  | .unary _ e => tE e
  | .call f args => max (tE f) (max (tArgs 1 args) (args.length + 1))
  | _ => 0

def tArgs (j : Nat) : List Expr → Nat
  | [] => 0
  | e :: es => max (j + tE e) (tArgs (j + 1) es)
end

mutual
def tS : Stmt → Nat
  | .expr e => tE e
  | .varDecl _ (some e) => tE e
  | .block ss => tSeq ss
  | .ifStmt c t none => max (tE c) (tS t)
  | .ifStmt c t (some e) => max (tE c) (max (tS t) (tS e))
  | .whileStmt c b => max (tE c) (tS b)
  | .forStmt i c st b =>
    max (match i with | some s => tS s | none => 0)
      (max (match c with | some e => tE e | none => 0)
        (max (match st with | some e => tE e | none => 0) (tS b)))
  | .ret (some e) => tE e
  | _ => 0

def tSeq : List Stmt → Nat
  | [] => 0
  | s :: ss => max (tS s) (tSeq ss)
end

def frameSize (ss : List Stmt) : Nat := 16 + 16 * tSeq ss

def storeTmp (k : Nat) : List Ins :=
  [addiN t6 spR (16 + 16 * k), .sd a0 t6, addi t6 t6 8, .sd a1 t6]

def loadTmp (k : Nat) : List Ins :=
  [addiN t6 spR (16 + 16 * k), .ld a0 t6, addi t6 t6 8, .ld a1 t6]

def errUnlessEq (r1 r2 pos : Nat) : List Ins := [Br .eq r1 r2 pos (pos + 2), J (pos + 1) errPos]

def jmpIfZero (pos tgt : Nat) : List Ins := [Br .ne a0 0 pos (pos + 2), J (pos + 1) tgt]

def jmpIfNonzero (pos tgt : Nat) : List Ins := [Br .eq a0 0 pos (pos + 2), J (pos + 1) tgt]

def opCode (pos : Nat) : BinOp → List Ins
  | .add => [Call pos addPos]
  | .sub => [Call pos subPos]
  | .mul => [Call pos mulPos]
  | .div => [Call pos divPos]
  | .mod => [Call pos modPos]
  | .lt => [mvi a4 0, Call (pos + 1) cmpPos]
  | .le => [mvi a4 1, Call (pos + 1) cmpPos]
  | .gt => [mvi a4 2, Call (pos + 1) cmpPos]
  | .ge => [mvi a4 3, Call (pos + 1) cmpPos]
  | .eq => [Call pos eqPos]
  | .ne => [Call pos eqPos, mvi t0 1, .sub a1 t0 a1]

def readHere (x : String) (l : List String) (pos fin : Nat) : List Ins :=
  match slotOf l x with
  | some i => [addiN t1 t0 (8 + 16 * i), .ld a0 t1, mvi t3 6, Br .eq a0 t3 (pos + 3) (pos + 7),
      addi t1 t1 8, .ld a1 t1, J (pos + 6) fin]
  | none => []

def writeHere (x : String) (l : List String) (pos fin : Nat) : List Ins :=
  match slotOf l x with
  | some i => [addiN t1 t0 (8 + 16 * i), .ld t2 t1, mvi t3 6, Br .eq t2 t3 (pos + 3) (pos + 8),
      .sd a0 t1, addi t1 t1 8, .sd a1 t1, J (pos + 7) fin]
  | none => []

def walkCode (here : List String → Nat → List Ins) (pos : Nat) : List (List String) → List Ins
  | [] => [J pos errPos]
  | [l] => here l pos ++ [J (pos + (here l pos).length) errPos]
  | l :: l' :: g =>
    here l pos ++ [.ld t0 t0] ++ walkCode here (pos + (here l pos).length + 1) (l' :: g)

def walkLen (hl : List String → Nat) : List (List String) → Nat
  | [] => 1
  | [l] => hl l + 1
  | l :: l' :: g => hl l + 1 + walkLen hl (l' :: g)

def hereLen (w : Nat) (x : String) (l : List String) : Nat := if (slotOf l x).isSome then w else 0

def varCode (x : String) (pos : Nat) (Γ : List (List String)) : List Ins :=
  let fin := pos + 1 + walkLen (hereLen 7 x) Γ
  [mv t0 envR] ++ walkCode (fun l p => readHere x l p fin) (pos + 1) Γ

def setCode (x : String) (pos : Nat) (Γ : List (List String)) : List Ins :=
  let fin := pos + 1 + walkLen (hereLen 8 x) Γ
  [mv t0 envR] ++ walkCode (fun l p => writeHere x l p fin) (pos + 1) Γ

structure GCtx where
  Γ : List (List String)
  blk : Nat
  brk : Option (Nat × Nat)
  cont : Option (Nat × Nat)
  ret : Option (Nat × Nat)

def GCtx.loop (C : GCtx) (b c : Nat) : GCtx := { C with brk := some (b, C.blk), cont := some (c, C.blk) }

def GCtx.enter (C : GCtx) (L : List String) : GCtx := { C with Γ := L :: C.Γ, blk := C.blk + 1 }

def GCtx.swallow (C : GCtx) (t : Nat) : GCtx :=
  { C with brk := some (t, C.blk), cont := some (t, C.blk), ret := some (t, C.blk) }

def exitTo (blk pos : Nat) : Option (Nat × Nat) → List Ins
  | none => [J pos errPos]
  | some (tgt, d) => List.replicate (blk - d) (.ld envR envR) ++ [J (pos + (blk - d)) tgt]

def enterFrame (l : List String) (pos : Nat) : List Ins :=
  [addiN a5 0 l.length, mv a6 envR, Call (pos + 2) nfPos, mv envR a4]

def storeSlot (i : Nat) : List Ins :=
  [addiN t6 envR (8 + 16 * i), .sd a0 t6, addi t6 t6 8, .sd a1 t6]

def printLoopG (pos : Nat) : Nat → Nat → List Ins
  | _, 0 => []
  | t, n + 1 =>
    let c := loadTmp t ++ [Call (pos + 4) dpPos] ++ (if n = 0 then [] else putc ' ')
    c ++ printLoopG (pos + c.length) (t + 1) n

def callCode (k m pos : Nat) : List Ins :=
  let pp := pos + 15
  let assertC : List Ins :=
    if m = 1 ∨ m = 2 then
      loadTmp (k + 1) ++ [Call (pp + 4) trPos] ++ jmpIfZero (pp + 5) errPos ++ [mvi a0 0, mvi a1 0]
    else [J pp errPos]
  let pr := pp + assertC.length + 1
  let prC := printLoopG pr (k + 1) m ++ [mvi a0 0, mvi a1 0]
  let pl := pr + prC.length + 1
  let plC := printLoopG pl (k + 1) m ++ putc '\n' ++ [mvi a0 0, mvi a1 0]
  let cl := pl + plC.length + 1
  let fin := cl + 8
  [addiN t6 spR (16 + 16 * k), .ld t0 t6, addi t6 t6 8, .ld t1 t6,
   mvi t2 4, Br .ne t0 t2 (pos + 5) (pos + 7), J (pos + 6) cl,
   mvi t2 5] ++ errUnlessEq t0 t2 (pos + 8) ++
  [Br .ne t1 0 (pos + 10) (pos + 12), J (pos + 11) pr,
   mvi t2 1, Br .ne t1 t2 (pos + 13) (pos + 15), J (pos + 14) pl] ++
  assertC ++ [J (pr - 1) fin] ++
  prC ++ [J (pl - 1) fin] ++
  plC ++ [J (cl - 1) fin] ++
  [mv a2 t1, addiN a3 spR (16 + 16 * (k + 1)), mvi a4 m, addi t3 a2 8, .ld t3 t3,
   Call (cl + 5) (cl + 7), J (cl + 6) fin, .jalr t3]

def paramCopy (L : List String) (j : Nat) (x : String) : List Ins :=
  [addiN t5 a3 (16 * j), .ld t4 t5, addiN t6 a4 (8 + 16 * (slotOf L x).getD 0), .sd t4 t6,
   addi t5 t5 8, .ld t4 t5, addi t6 t6 8, .sd t4 t6]

def paramCopies (L : List String) : Nat → List String → List Ins
  | _, [] => []
  | j, x :: xs => paramCopy L j x ++ paramCopies L (j + 1) xs

def fnPre (L : List String) (params : List String) (fs pos : Nat) : List Ins :=
  [mvi t0 params.length] ++ errUnlessEq a4 t0 (pos + 1) ++
    [mvi t0 1000, Br .lt depR t0 (pos + 4) (pos + 6), J (pos + 5) errPos,
     addi depR depR 1, addi spR spR (-(fs : Int)), .sd ra spR, addi t6 spR 8, .sd envR t6,
     .ld a6 a2, mvi a5 L.length, Call (pos + 13) nfPos] ++ paramCopies L 0 params ++ [mv envR a4]

def fnPost (fs : Nat) : List Ins :=
  [mvi a0 0, mvi a1 0, .ld ra spR, addi t6 spR 8, .ld envR t6, addiN spR spR fs, addi depR depR (-1), ret]

def fnCtx (Γ : List (List String)) (epi : Nat) : GCtx := ⟨Γ, 0, none, none, some (epi, 0)⟩

mutual

def gexpr (T : List String) (Γ : List (List String)) (k pos : Nat) : Expr → List Ins
  | .int n => [mvi a0 2] ++ li a1 (BitVec.ofInt 64 n)
  | .bool b => [mvi a0 1, mvi a1 (if b then 1 else 0)]
  | .null => [mvi a0 0, mvi a1 0]
  | .str s => [mvi a0 3] ++ liN a1 (strAddr T s)
  | .var x => varCode x pos Γ
  | .assign x e =>
    let ce := gexpr T Γ k pos e
    ce ++ setCode x (pos + ce.length) Γ
  | .binary op l r =>
    let cl := gexpr T Γ k pos l
    let p1 := pos + cl.length + 4
    let cr := gexpr T Γ (k + 1) p1 r
    cl ++ storeTmp k ++ cr ++ [mv a2 a0, mv a3 a1] ++ loadTmp k ++ opCode (p1 + cr.length + 6) op
  | .logical op l r =>
    let cl := gexpr T Γ k pos l
    let p1 := pos + cl.length
    let cr := gexpr T Γ k (p1 + 3) r
    let q := p1 + 3 + cr.length
    let short : List Ins := match op with
      | .or => jmpIfNonzero (p1 + 1) (q + 4)
      | .and => jmpIfZero (p1 + 1) (q + 4)
    cl ++ [Call p1 trPos] ++ short ++ cr ++ [Call q trPos, mv a1 a0, mvi a0 1, J (q + 3) (q + 6)] ++
      [mvi a0 1, mvi a1 (match op with | .or => 1 | .and => 0)]
  | .unary .neg e =>
    let ce := gexpr T Γ k pos e
    ce ++ [mvi t0 2] ++ errUnlessEq a0 t0 (pos + ce.length + 1) ++ [.sub a1 0 a1]
  | .unary .not e =>
    let ce := gexpr T Γ k pos e
    ce ++ [Call (pos + ce.length) trPos, mvi t0 1, .sub a1 t0 a0, mvi a0 1]
  | .call f args =>
    let cf := gexpr T Γ k pos f
    let p1 := pos + cf.length
    if maxArgs < args.length then cf ++ [J p1 errPos]
    else
      let ca := gargs T Γ (k + 1) (p1 + 4) args
      cf ++ storeTmp k ++ ca ++ callCode k args.length (p1 + 4 + ca.length)
  | .fn name params body =>
    let L := frameNames params body
    let pre : List Ins := [addi t0 hpO 32] ++ liN t1 objEnd ++
      [Br .ge t1 t0 (pos + 12) (pos + 14), J (pos + 13) errPos, .sd envR hpO] ++
      liN t2 (codeBase + 4 * (pos + 58)) ++ [addi t3 hpO 8, .sd t2 t3] ++
      liN t2 (strAddr T (dispName name)) ++ [addi t3 hpO 16, .sd t2 t3] ++
      liN t2 (strAddr T (catName name)) ++ [addi t3 hpO 24, .sd t2 t3] ++
      [mvi a0 4, mv a1 hpO, mv hpO t0]
    let fs := frameSize body
    let fp := fnPre L params fs (pos + 58)
    let pb := pos + 58 + fp.length
    let lb := (gseq T (fnCtx (L :: Γ) 0) pb body).length
    let F := fp ++ gseq T (fnCtx (L :: Γ) (pb + lb + 2)) pb body ++ fnPost fs
    pre ++ [J (pos + 57) (pos + 58 + F.length)] ++ F

def gargs (T : List String) (Γ : List (List String)) (k pos : Nat) : List Expr → List Ins
  | [] => []
  | e :: es =>
    let c := gexpr T Γ k pos e ++ storeTmp k
    c ++ gargs T Γ (k + 1) (pos + c.length) es

def gstmt (T : List String) (C : GCtx) (pos : Nat) : Stmt → List Ins
  | .expr e => gexpr T C.Γ 0 pos e
  | .varDecl x i =>
    let ce : List Ins := match i with
      | some e => gexpr T C.Γ 0 pos e
      | none => [mvi a0 0, mvi a1 0]
    ce ++ storeSlot ((slotOf (C.Γ.headD []) x).getD 0)
  | .block ss =>
    let L := frameNames [] ss
    enterFrame L pos ++ gseq T (C.enter L) (pos + 4) ss ++ [.ld envR envR]
  | .ifStmt c t e =>
    let cc := gexpr T C.Γ 0 pos c
    let p1 := pos + cc.length
    let pt := p1 + 3
    let ct := gstmt T C pt t
    let pe := pt + ct.length + 1
    let ce : List Ins := match e with
      | some e => gstmt T C pe e
      | none => []
    cc ++ [Call p1 trPos] ++ jmpIfZero (p1 + 1) pe ++ ct ++ [J (pt + ct.length) (pe + ce.length)] ++ ce
  | .whileStmt c b =>
    let cc := gexpr T C.Γ 0 pos c
    let p1 := pos + cc.length
    let pb := p1 + 3
    let lb := (gstmt T (C.loop 0 0) pb b).length
    let ex := pb + lb + 1
    cc ++ [Call p1 trPos] ++ jmpIfZero (p1 + 1) ex ++ gstmt T (C.loop ex pos) pb b ++ [J (pb + lb) pos]
  | .forStmt init cnd step b =>
    let L := forNames init b
    let C1 := C.enter L
    let pi := pos + 4
    let li : Nat := match init with
      | some s => (gstmt T (C1.swallow 0) pi s).length
      | none => 0
    let hd := pi + li
    let ci : List Ins := match init with
      | some s => gstmt T (C1.swallow hd) pi s
      | none => []
    let lc : Nat := match cnd with
      | some c => (gexpr T C1.Γ 0 hd c).length + 3
      | none => 0
    let pb := hd + lc
    let lb := (gstmt T (C1.loop 0 0) pb b).length
    let ps := pb + lb
    let cs : List Ins := match step with
      | some e => gexpr T C1.Γ 0 ps e
      | none => []
    let ex := ps + cs.length + 1
    let cc : List Ins := match cnd with
      | some c =>
        let g := gexpr T C1.Γ 0 hd c
        g ++ [Call (hd + g.length) trPos] ++ jmpIfZero (hd + g.length + 1) ex
      | none => []
    enterFrame L pos ++ ci ++ cc ++
      gstmt T (C1.loop ex ps) pb b ++ cs ++
      [J (ps + cs.length) hd, .ld envR envR]
  | .ret e =>
    let ce : List Ins := match e with
      | some e => gexpr T C.Γ 0 pos e
      | none => [mvi a0 0, mvi a1 0]
    ce ++ exitTo C.blk (pos + ce.length) C.ret
  | .brk => exitTo C.blk pos C.brk
  | .cont => exitTo C.blk pos C.cont

def gseq (T : List String) (C : GCtx) (pos : Nat) : List Stmt → List Ins
  | [] => []
  | s :: ss =>
    let c := gstmt T C pos s
    c ++ gseq T C (pos + c.length) ss

end

def strObjCode (s : String) (a : Nat) : List Ins :=
  liN t0 a ++ liN t1 s.length ++ [.sd t1 t0] ++
    s.toList.flatMap fun c => [addi t0 t0 8, mvi t1 c.toNat, .sd t1 t0]

def strTabCode (T : List String) : List Ins :=
  (List.range T.length).flatMap fun i => strObjCode (T.getD i "") (objBase + strOff T i)

def natCode (i : Nat) : List Ins := [mvi a0 5, mvi a1 i] ++ storeSlot i

def nativeCode : List Ins := natCode 0 ++ natCode 1 ++ natCode 2

def mainPos : Nat := rtEnd

def setupCode (p : Program) : List Ins :=
  let T := strTab p
  let G := globalNames p
  let pre := strTabCode T ++ liN spR (stackHi - frameSize p) ++ [mvi depR 0] ++ liN hpF frameBase ++
    liN hpO (objBase + strOff T T.length)
  pre ++ [mvi a5 G.length, mvi a6 0, Call (mainPos + pre.length + 2) nfPos, mv envR a4] ++ nativeCode

def compileG (p : Program) : List Ins :=
  let T := strTab p
  let sc := setupCode p
  [J 0 mainPos] ++ errCode ++ rtCode ++ sc ++
    gseq T ⟨[globalNames p], 0, none, none, none⟩ (mainPos + sc.length) p ++ exitCode 0

end Vsa.Compiler
