import Vsa.MemRepr
import Vsa.While.Semantics

namespace Vsa.RuntimeRepr

open Vsa.While Vsa.MemRepr

def kindTag : Value → Nat
  | .null => 0
  | .bool _ => 1
  | .int _ => 2
  | .str _ => 3
  | .closure _ => 4
  | .native _ => 5

def nativeName : NativeFn → String
  | .print => "print"
  | .println => "println"
  | .assert => "assert"

structure NativeAddrs where
  print : Nat
  println : Nat
  assert : Nat

def NativeAddrs.addr (N : NativeAddrs) : NativeFn → Nat
  | .print => N.print
  | .println => N.println
  | .assert => N.assert

def ValueRepr (m : Mem) (N : NativeAddrs) (φc : Addr → Nat)
    (a : Nat) : Value → Prop
  | .null => read32 m a = some 0
  | .bool b => read32 m a = some 1 ∧ read32 m (a + 8) = some (cond b 1 0)
  | .int n => read32 m a = some 2 ∧ readI64 m (a + 8) = some n
  | .str s => read32 m a = some 3 ∧
      ∃ p, read64 m (a + 8) = some p ∧ p ≠ 0 ∧ CString m p s
  | .closure ca => read32 m a = some 4 ∧
      read64 m (a + 8) = some (φc ca) ∧ φc ca ≠ 0
  | .native f => read32 m a = some 5 ∧
      (∃ p, read64 m (a + 8) = some p ∧ CString m p (nativeName f)) ∧
      read64 m (a + 16) = some (N.addr f)

def ValueWordsTotal (m : Mem) (a : Nat) : Prop :=
  ∃ d0 d1 d2 : BitVec 64,
    read64 m a = some d0.toNat ∧
    read64 m (a + 8) = some d1.toNat ∧
    read64 m (a + 16) = some d2.toNat

def ClosureRepr (m : Mem) (φf : Addr → Nat) (p : Nat)
    (cd : ClosureData) : Prop :=
  (∃ q, read64 m p = some q ∧ ExprRepr m q (.fn cd.name cd.params cd.body)) ∧
  read64 m (p + 8) = some (φf cd.env) ∧ φf cd.env ≠ 0

def FrameRepr (m : Mem) (N : NativeAddrs) (φf φc : Addr → Nat)
    (e : Nat) (f : Frame) : Prop :=
  read32 m e = some f.vars.length ∧
  (∃ cap, read32 m (e + 4) = some cap ∧ f.vars.length ≤ cap) ∧
  (∃ pn pv, read64 m (e + 8) = some pn ∧ read64 m (e + 16) = some pv ∧
    ∀ i, (h : i < f.vars.length) →
      (∃ q, read64 m (pn + 8 * i) = some q ∧ CString m q (f.vars[i].1)) ∧
      ValueRepr m N φc (pv + 24 * i) (f.vars[i].2)) ∧
  (match f.parent with
   | none => read64 m (e + 24) = some 0
   | some pa => read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0)

structure Arena where
  lo : Nat
  hi : Nat

def Arena.contains (A : Arena) (a size : Nat) : Prop :=
  A.lo ≤ a ∧ a + size ≤ A.hi

structure StoreRepr (m : Mem) (N : NativeAddrs) (A : Arena)
    (φf φc : Addr → Nat) (s : Store) : Prop where
  frames : ∀ fa, (h : fa < s.frames.size) →
    FrameRepr m N φf φc (φf fa) s.frames[fa]
  closures : ∀ ca, (h : ca < s.closures.size) →
    ClosureRepr m φf (φc ca) s.closures[ca]
  φf_inj : ∀ a b, a < s.frames.size → b < s.frames.size →
    φf a = φf b → a = b
  φc_inj : ∀ a b, a < s.closures.size → b < s.closures.size →
    φc a = φc b → a = b
  frames_arena : ∀ fa, fa < s.frames.size →
    A.contains (φf fa) 32 ∧ φf fa % 8 = 0
  closures_arena : ∀ ca, ca < s.closures.size →
    A.contains (φc ca) 16 ∧ φc ca % 8 = 0

def OutRepr (σ : Machine.MState) (st : St) : Prop :=
  Machine.output σ = st.out

end Vsa.RuntimeRepr
