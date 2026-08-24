import Vsa.MemRepr
import Vsa.While.Semantics

/-!
# Layer 2: runtime representation invariants

PLAN-InterpSim.md Layer 2: extends `Vsa/MemRepr.lean` (read-only AST
representation) with the *mutable* runtime — the C `Value`/`Closure`/`Env`
structs against the spec-side `Store` of `Vsa/While/Semantics.lean`.

Layouts are read off the compiled binary (LP64, riscv64), verified against
the generated code (e.g. `env_get`'s `24*i` stride and 3×8-byte copy):

```
Value   (24 bytes): kind:int @0, payload @8 (union), 2nd word @16
                    (only the native member uses bytes 16–23)
Closure (16 bytes): fn_expr:Expr* @0, env:Env* @8
Env     (32 bytes): count:int @0, cap:int @4, names:char** @8,
                    vals:Value* @16, parent:Env* @24
```

Note the plan's descriptive text says "16-byte `Value`"; the actual layout
is 24 bytes because the `native` union member is a 16-byte struct — the
binary is the source of truth here, exactly as `MemRepr` reads `ast.h`'s
layout off the compiled representation.

Spec–machine sharing is mediated by explicit correspondence maps
`φf : spec frame Addr → machine addr` and `φc : spec closure Addr →
machine addr`; two spec frames are the same C environment iff the machine
addresses coincide (`StoreRepr` requires injectivity on the allocated
prefix).

Heap-object *disjointness* obligations (needed for mutation framing:
writing one frame's `vals` slot must not disturb any other represented
object) are deliberately not baked into these relations yet — the exact
footprint witnesses they need will be dictated by the `env_define`/
`env_set` function specs (M3/M4), and will be threaded as layout-witness
records alongside `StoreRepr` at that point. Representation and framing
stay separate concerns, as in the plan ("framing is explicit: every spec
carries …" — a Layer-3 statement, not a Layer-2 one).
-/

namespace Vsa.RuntimeRepr

open Vsa.While Vsa.MemRepr

/-- `ValueKind` tags (`value.h`): `VAL_NULL=0 … VAL_NATIVE=5`. -/
def kindTag : Value → Nat
  | .null => 0
  | .bool _ => 1
  | .int _ => 2
  | .str _ => 3
  | .closure _ => 4
  | .native _ => 5

/-- The C names of the three natives (`interp_init`). -/
def nativeName : NativeFn → String
  | .print => "print"
  | .println => "println"
  | .assert => "assert"

/-- Machine entry addresses of the three native functions; concrete values
come from the symbol table at Layout instantiation (M6). -/
structure NativeAddrs where
  print : Nat
  println : Nat
  assert : Nat

def NativeAddrs.addr (N : NativeAddrs) : NativeFn → Nat
  | .print => N.print
  | .println => N.println
  | .assert => N.assert

/-- A 24-byte C `Value` at address `a` represents spec value `v`.
`φc` maps spec closure addresses to machine `Closure*`s. Payload bytes
beyond a variant's own field are unconstrained (C never reads them). -/
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

/-- A 16-byte C `Closure` at address `p` represents spec closure data `cd`.
`fn_expr` points to the `EX_FN` AST node carrying the same name, params,
and body; `env` is the captured environment through `φf`. -/
def ClosureRepr (m : Mem) (φf : Addr → Nat) (p : Nat)
    (cd : ClosureData) : Prop :=
  (∃ q, read64 m p = some q ∧ ExprRepr m q (.fn cd.name cd.params cd.body)) ∧
  read64 m (p + 8) = some (φf cd.env) ∧ φf cd.env ≠ 0

/-- A 32-byte C `Env` at address `e` represents spec frame `f`: `count` =
number of bindings, arrays hold the names/values positionally (spec
`define` appends exactly like `env_define`), parent link through `φf`
(`NULL` iff the spec parent is `none`). `cap` and the arrays' spare
capacity are existential — the C growth policy is not part of the spec. -/
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

/-- The heap arena (the no-free discipline): every runtime object lives in
`[lo, hi)`. Concrete bounds come from the linker script at M6. -/
structure Arena where
  lo : Nat
  hi : Nat

def Arena.contains (A : Arena) (a size : Nat) : Prop :=
  A.lo ≤ a ∧ a + size ≤ A.hi

/-- **The store is represented**: every allocated spec frame and closure is
laid out in machine memory through the correspondence maps, which are
injective on the allocated prefixes (sharing is meaningful) and 8-aligned
inside the arena. -/
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

/-- **Output correspondence**: the machine's HTIF console output equals the
spec-side accumulated output. -/
def OutRepr (σ : Machine.MState) (st : St) : Prop :=
  Machine.output σ = st.out

end Vsa.RuntimeRepr
