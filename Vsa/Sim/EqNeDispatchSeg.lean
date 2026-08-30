import Vsa.Sim.EvalGeChain
import Vsa.Sim.DeriveCaseRow
import Vsa.Sim.ChainFactsTac
import Vsa.Sim.DeriveCallSeg
import Vsa.Sim.ValueEqualSpec4

/-!
# `EqNeDispatchSeg` — the `eq`/`ne` arm spill-and-call-setup blocks as `#derive_case` leaves

The `eq` (token 19) and `ne` (token 17) arms do NOT run a kind-check ladder like
`div`/`mod`/`ge` — `value_equal` handles every kind itself.  Instead each arm is a
single straight-line block that reloads the two operands' repr words from their
spill slots, points `a0`/`a1` at two freshly-materialised `Value` structs on the
stack (`bufa = sp+0x40`, `bufb = sp+0x20`), spills the words into those structs,
and falls through to `jal value_equal`:

  `eq` arm `0x800036e4 → 0x8000371c`:
     `ld a7,0x78 ; ld a6,0x80 ; ld a2,0x88 ; ld a3,0x90 ; ld a4,0x98 ; ld a5,0xa0`
     `; addi a1,sp,0x20 ; addi a0,sp,0x40`
     `; sd a7,0x40 ; sd a6,0x48 ; sd a2,0x50 ; sd a3,0x20 ; sd a4,0x28 ; sd a5,0x30`
     ▷ (fall through) `jal value_equal @0x8000371c` — box with `value_bool(a0)`;
  `ne` arm `0x80003734 → 0x8000376c`: **the byte-identical block** (same 14
     instruction words, PCs shifted by +0x50) ▷ `jal value_equal @0x8000376c` —
     box with `value_bool(seqz a0)` (the extra `seqz` negation is in the suffix,
     not this seg).

Both rows park at their `jal value_equal` PC with `x10 = bufa = sp+0x40` and
`x11 = bufb = sp+0x20` — the `value_equal(bufa, bufb)` call arguments — and the
six field stores in `out.log`.  On top, `jal value_equal` is a Shape-D `callSeg`
seam threading `value_equal_spec_full` (already complete, `ValueEqualSpec4`) and
`jal value_bool` boxes the result — the same two-seam shape as `div`/`mod`, only
the callee is `value_equal` (a `.bool`, via `binOpSem_eq`/`binOpSem_ne`) rather
than `__divdi3`/`__moddi3` (an `.int`).

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While (NativeFn)
open Vsa.Sim.Code (StrcmpLoaded)

namespace Vsa.Sim

set_option maxHeartbeats 4000000

/- The `eq` arm block `0x800036e4 → 0x8000371c`: one straight-line block, no
branch terminator (control falls through to `jal value_equal`).  Six operand
reloads, the two `addi` buffer-pointer setups, then the six field spills. -/
#derive_case eqDispatch chain
  [(0x800036e4#64, 0x07813883#32),                -- ld   x17,0x78(x2)   (a7)
   (0x800036e8#64, 0x08013803#32),                -- ld   x16,0x80(x2)   (a6)
   (0x800036ec#64, 0x08813603#32),                -- ld   x12,0x88(x2)   (a2)
   (0x800036f0#64, 0x09013683#32),                -- ld   x13,0x90(x2)   (a3)
   (0x800036f4#64, 0x09813703#32),                -- ld   x14,0x98(x2)   (a4)
   (0x800036f8#64, 0x0a013783#32),                -- ld   x15,0xa0(x2)   (a5)
   (0x800036fc#64, 0x02010593#32),                -- addi x11,x2,0x20    (a1 = bufb = sp+0x20)
   (0x80003700#64, 0x04010513#32),                -- addi x10,x2,0x40    (a0 = bufa = sp+0x40)
   (0x80003704#64, 0x05113023#32),                -- sd   x17,0x40(x2)
   (0x80003708#64, 0x05013423#32),                -- sd   x16,0x48(x2)
   (0x8000370c#64, 0x04c13823#32),                -- sd   x12,0x50(x2)
   (0x80003710#64, 0x02d13023#32),                -- sd   x13,0x20(x2)
   (0x80003714#64, 0x02e13423#32),                -- sd   x14,0x28(x2)
   (0x80003718#64, 0x02f13823#32)]                -- sd   x15,0x30(x2)

/- The `ne` arm block `0x80003734 → 0x8000376c`: byte-identical instruction words
to `eqDispatch`, PCs shifted by +0x50. -/
#derive_case neDispatch chain
  [(0x80003734#64, 0x07813883#32),                -- ld   x17,0x78(x2)
   (0x80003738#64, 0x08013803#32),                -- ld   x16,0x80(x2)
   (0x8000373c#64, 0x08813603#32),                -- ld   x12,0x88(x2)
   (0x80003740#64, 0x09013683#32),                -- ld   x13,0x90(x2)
   (0x80003744#64, 0x09813703#32),                -- ld   x14,0x98(x2)
   (0x80003748#64, 0x0a013783#32),                -- ld   x15,0xa0(x2)
   (0x8000374c#64, 0x02010593#32),                -- addi x11,x2,0x20    (a1 = bufb = sp+0x20)
   (0x80003750#64, 0x04010513#32),                -- addi x10,x2,0x40    (a0 = bufa = sp+0x40)
   (0x80003754#64, 0x05113023#32),                -- sd   x17,0x40(x2)
   (0x80003758#64, 0x05013423#32),                -- sd   x16,0x48(x2)
   (0x8000375c#64, 0x04c13823#32),                -- sd   x12,0x50(x2)
   (0x80003760#64, 0x02d13023#32),                -- sd   x13,0x20(x2)
   (0x80003764#64, 0x02e13423#32),                -- sd   x14,0x28(x2)
   (0x80003768#64, 0x02f13823#32)]                -- sd   x15,0x30(x2)

/-- The `eq`/`ne` arm pin list: only `x2 = sp` (the frame base of every load,
store, and `addi`).  Both operand words are reloaded from `lds`, `a0`/`a1` are
computed from `sp`, so nothing else is externally live in the block. -/
def eqDispL (sp : BitVec 64) : GRegs := [(2, sp)]

/-- The `eq` dispatch outcome: parked at `0x8000371c` (ready for `jal
value_equal`), memory updated by the six field stores, and the `value_equal` call
arguments staged — `x10 = bufa = sp+0x40`, `x11 = bufb = sp+0x20` — with `x2=sp`
surviving for the frame. -/
def EqDispatchPost (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks eqDispatch
    (SegEvalState.init (eqDispL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000371c#64 ∧
  gprGet c.σ 10 = some (sp + 0x40#64) ∧
  gprGet c.σ 11 = some (sp + 0x20#64) ∧
  gprGet c.σ 2 = some sp

/-- The `ne` dispatch outcome: parked at `0x8000376c`, otherwise identical to
`EqDispatchPost` (same stores, same staged `bufa`/`bufb`). -/
def NeDispatchPost (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧
  c.σ.mem = writeLog m0 (evalBlocks neDispatch
    (SegEvalState.init (eqDispL sp) lds)).log ∧
  c.σ.regs.get? Register.PC = some 0x8000376c#64 ∧
  gprGet c.σ 10 = some (sp + 0x40#64) ∧
  gprGet c.σ 11 = some (sp + 0x20#64) ∧
  gprGet c.σ 2 = some sp

/-- **The new eq leaf.**  The whole `eq` arm spill-and-setup block
`0x800036e4 → 0x8000371c` as a `Triple`, assembled by `#derive_case` +
`segToTriple`.  `bufa`/`bufb` come off the two `addi`s (`sp + sign_extend imm`,
bridged to `sp+0x40`/`sp+0x20`); `x2=sp` survives the block. -/
theorem eqDispatchRow (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre eqDispatch (eqDispL sp) lds 0x800036e4#64 m0)
      (EqDispatchPost sp lds m0) := by
  apply segToTriple eqDispatch (eqDispL sp) lds 0x800036e4#64 m0
    (EqDispatchPost sp lds m0)
    (by show ChainOK 0x800036e4#64 [2] eqDispatch; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_⟩
  · rw [hpc']
    show some (chainEndPC 0x800036e4#64 (eqDispL sp) lds eqDispatch)
      = some 0x8000371c#64
    rw [chainEndPC_eq_bt eqDispatch 0x800036e4#64 (eqDispL sp) lds (by decide)]
    rfl
  · have e : (sp + sign_extend (m := 64) (0x40#12) : BitVec 64) = sp + 0x40#64 := by
      rw [show (sign_extend (m := 64) (0x40#12) : BitVec 64) = 0x40#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · have e : (sp + sign_extend (m := 64) (0x20#12) : BitVec 64) = sp + 0x20#64 := by
      rw [show (sign_extend (m := 64) (0x20#12) : BitVec 64) = 0x20#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sp) _ hregs (by rfl)

/-- **The new ne leaf.**  The byte-identical `ne` arm block
`0x80003734 → 0x8000376c` as a `Triple`.  Same proof as `eqDispatchRow` up to the
shifted PCs; the `seqz` negation lives in the box suffix, not this seg. -/
theorem neDispatchRow (sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre neDispatch (eqDispL sp) lds 0x80003734#64 m0)
      (NeDispatchPost sp lds m0) := by
  apply segToTriple neDispatch (eqDispL sp) lds 0x80003734#64 m0
    (NeDispatchPost sp lds m0)
    (by show ChainOK 0x80003734#64 [2] neDispatch; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', hmem', ?_, ?_, ?_, ?_⟩
  · rw [hpc']
    show some (chainEndPC 0x80003734#64 (eqDispL sp) lds neDispatch)
      = some 0x8000376c#64
    rw [chainEndPC_eq_bt neDispatch 0x80003734#64 (eqDispL sp) lds (by decide)]
    rfl
  · have e : (sp + sign_extend (m := 64) (0x40#12) : BitVec 64) = sp + 0x40#64 := by
      rw [show (sign_extend (m := 64) (0x40#12) : BitVec 64) = 0x40#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · have e : (sp + sign_extend (m := 64) (0x20#12) : BitVec 64) = sp + 0x20#64 := by
      rw [show (sign_extend (m := 64) (0x20#12) : BitVec 64) = 0x20#64 from by decide]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sp) _ hregs (by rfl)

#print axioms eqDispatchRow
#print axioms neDispatchRow

/-! ## The spec-side `eq`/`ne` bridges

`value_equal` returns `l.equal r` (a `Bool`), which the `value_bool` suffix boxes:
`eq` boxes it directly (`binOpSem .eq = .bool (l.equal r)`), `ne` boxes its
negation via the extra `seqz` (`binOpSem .ne = .bool (!(l.equal r))`).  Both are
total (no divisor-style guard). -/

theorem binOpSem_eq (s : Vsa.While.Store) (l r : Vsa.While.Value) :
    Vsa.While.binOpSem s .eq l r = some (.bool (l.equal r)) := rfl

theorem binOpSem_ne (s : Vsa.While.Store) (l r : Vsa.While.Value) :
    Vsa.While.binOpSem s .ne l r = some (.bool (!(l.equal r))) := rfl

#print axioms binOpSem_eq
#print axioms binOpSem_ne

/-! ## The `value_equal` seam via `callSeg`

The `eq`/`ne` arms' comparison tail is the Shape-D call splice
`spill-setup ≫ jal value_equal ≫ value_bool`.  The callee contract is the REAL
`value_equal_spec_full` (`ValueEqualSpec4`, `x10 = cond (va.equal vb) 1 0`,
covering both the `str`-`str` strcmp branch and all five non-`str` branches).
Unlike `divdi3_spec`/`moddi3_spec` it is stated as a raw `∃ c', Steps ∧ post`
with several universal side-conditions, so we first repackage it as a genuine
`Triple` (`valueEqualTriple`) whose entry predicate is `ve_pre` conjoined with
`x2 = sp` (the frame `value_equal_spec_full` additionally needs), then thread it
with `callSeg` exactly as `divCallSeam`/`modCallSeam` thread their libgcc callee.
The `eq` and `ne` arms share this ONE seam — they differ only in the boxing
suffix `Q` (`value_bool(a0)` vs `value_bool(seqz a0)`). -/

/-- **`value_equal` as a `Triple`.**  Repackages `value_equal_spec_full` into
`callSeg` shape: the entry predicate is `ve_pre` (the `value_equal` contract's own
entry) conjoined with `x2 = sp` (the caller frame the spec also consumes); the
universal side-conditions (`φc`/native injectivity, `strcmp`/mask loaded, `r`
4-aligned, and the `str`-path witnesses used only on the `str`-`str` branch) are
carried as hypotheses. -/
theorem valueEqualTriple
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Vsa.While.Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b)
    (hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0) (hraln4 : r.toNat % 4 = 0)
    (hstrwit : ∀ sa sb, va = .str sa → vb = .str sb →
      ∃ (pa' pb' : Nat) (csa csb : List Char),
        read64 m0 (bufa.toNat + 8) = some pa' ∧ read64 m0 (bufb.toNat + 8) = some pb' ∧
        CStr m0 pa' csa ∧ CStr m0 pb' csb ∧ sa = String.ofList csa ∧ sb = String.ofList csb ∧
        StrcmpRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpRegion (BitVec.ofNat 64 pb') csb.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pb') csb.length ∧
        VEStrRegions sp pa' pb' csa.length csb.length) :
    Triple (fun c => ve_pre g bufa bufb r N φc va vb m0 out0 c ∧
              c.σ.regs.get? Register.x2 = some sp)
      (ve_str_post g r sp va vb m0 out0) := by
  intro c hc
  exact value_equal_spec_full g bufa bufb r sp N φc va vb m0 out0 c hφc hN hc.1 hc.2
    hstrc hmask hraln4 hstrwit

/-- **The `value_equal` seam, realized via `callSeg` with the real
`value_equal_spec_full`.**  Given the caller prefix landing the staged
`eqDispatchRow`/`neDispatchRow` args at the `value_equal` entry
(`Triple P (ve_pre … ∧ x2 = sp)`) and the caller return suffix boxing the boolean
(`Triple (ve_str_post …) Q` — `value_bool(a0)` for `eq`, `value_bool(seqz a0)`
for `ne`), `callSeg` produces the whole comparison call site `Triple P Q` — the
exact Shape-D composition, with `value_equal_spec_full` (not a hand re-derivation)
as the threaded callee.  Shared by both `eq` and `ne`. -/
theorem valueEqualCallSeam {P Q : Config → Prop}
    (g : (R : Register) → Option (RegisterType R)) (bufa bufb r sp : BitVec 64)
    (N : NativeAddrs) (φc : Vsa.While.Addr → Nat) (va vb : Vsa.While.Value)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (out0 : Array String)
    (hφc : ∀ (a b : Vsa.While.Addr), φc a = φc b → a = b)
    (hN : ∀ (f h : NativeFn), N.addr f = N.addr h → f = h)
    (hstrc : StrcmpLoaded m0) (hmask : MaskPinned m0) (hraln4 : r.toNat % 4 = 0)
    (hstrwit : ∀ sa sb, va = .str sa → vb = .str sb →
      ∃ (pa' pb' : Nat) (csa csb : List Char),
        read64 m0 (bufa.toNat + 8) = some pa' ∧ read64 m0 (bufb.toNat + 8) = some pb' ∧
        CStr m0 pa' csa ∧ CStr m0 pb' csb ∧ sa = String.ofList csa ∧ sb = String.ofList csb ∧
        StrcmpRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpRegion (BitVec.ofNat 64 pb') csb.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pa') csa.length ∧
        StrcmpWRegion (BitVec.ofNat 64 pb') csb.length ∧
        VEStrRegions sp pa' pb' csa.length csb.length)
    (pre : Triple P (fun c => ve_pre g bufa bufb r N φc va vb m0 out0 c ∧
              c.σ.regs.get? Register.x2 = some sp))
    (suf : Triple (ve_str_post g r sp va vb m0 out0) Q) :
    Triple P Q :=
  callSeg pre (valueEqualTriple g bufa bufb r sp N φc va vb m0 out0
    hφc hN hstrc hmask hraln4 hstrwit) suf

#print axioms valueEqualTriple
#print axioms valueEqualCallSeam

end Vsa.Sim
