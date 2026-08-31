import Vsa.Sim.CmpArmSeg

/-!
# `StrCmpSignTail` — the operator sign-test tail `0x800036a4 → jal value_bool`,
parameterised over the op token (lt / le / gt / ge)

The comparison arm's shared operator sign-test tail begins at `0x800036a4`
(`experiments/disasm.txt`).  The three operator `beq`s select the per-op sign
block; each block ends at a `jal value_bool @0x800027f8` producing the boolean
payload word in `a1` from the spaceship scalar in `a1`:

```
800036a4  li a5,21 ; beq a2,a5 → 80003af8            (le)
800036ac  li a5,22 ; beq a2,a5 → 80003ae4            (gt)
800036b4  li a5,20 ; beq a2,a5 → 800036c0            (lt) [beq-taken → shared srli]
800036bc  not a1,a1                                   (ge fall-through)
800036c0  srli a1,a1,0x3f ; mv a0,s1 ; jal value_bool (lt/ge shared)
--
80003ae4  sgtz a1,a1 ; mv a0,s1 ; jal value_bool      (gt)
80003af8  slti a1,a1,1 ; mv a0,s1 ; jal value_bool    (le)
```

So the sign-test *diverges* by op token: `lt` (token 20) `beq`-takes at
`0x800036b4` straight to the shared `srli @0x800036c0`; `ge` (token 23) falls
through all three `beq`s, runs `not a1,a1`, then the shared `srli`; `gt` (token
22) `beq`-takes at `0x800036ac` to the `sgtz` block `0x80003ae4`; `le` (token 21)
`beq`-takes at `0x800036a4` to the `slti` block `0x80003af8`.

The `ge` route is already the landed `CmpArmSeg.cmpFixupTail` (`not;srli;mv`).
This file adds the three remaining routes as `#derive_case` segs and factors the
common shape (`SegPre` at `0x800036a4`, pins `[(11, cmpV), (12, tok), (9, sret)]`,
run to the `jal value_bool` entry, produce the sign word in `x11` and `x10 =
sret`).  The seg family IS the parameterisation: one seg per op token, sharing
the pin list, the entry PC, and the `segToTriple` marshalling; `cmpV` (the
spaceship scalar in `a1`) stays symbolic in every seg.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Steps)
open Vsa.Logic

namespace Vsa.Sim

set_option maxHeartbeats 800000

/-! ## The three non-`ge` sign-test routes as `#derive_case` segs

Each is resolved for its op token: the `beq` at the route's entry is TAKEN
(so the pin `x12 = tok` matches the `li a5,tok`).  The route runs from
`0x800036a4` to the `jal value_bool` entry PC of that op's sign block. -/

/- `lt` (token 20): `li a5,21` ▷ `beq` NOT (20≠21) → 0x36ac; `li a5,22` ▷ `beq`
NOT (20≠22) → 0x36b4; `li a5,20` ▷ `beq` TAKEN (20=20) → 0x36c0; then
`srli x11,x11,0x3f ; mv x10,x9` — straight-line to the jal entry 0x36c8. -/
#derive_case sTailLt chain
  [(0x800036a4#64, 0x01500793#32)]                -- li x15,21
    terminator ⟨0x800036a8#64, 0x44f60863#32, 0x63#8, 0x08#8, 0xf6#8, 0x44#8,
      .br bop.BEQ false, 12, 15, 0x0450#13, 0#21, 0#12⟩ ;;
  [(0x800036ac#64, 0x01600793#32)]                -- li x15,22
    terminator ⟨0x800036b0#64, 0x42f60a63#32, 0x63#8, 0x0a#8, 0xf6#8, 0x42#8,
      .br bop.BEQ false, 12, 15, 0x0434#13, 0#21, 0#12⟩ ;;
  [(0x800036b4#64, 0x01400793#32)]                -- li x15,20
    terminator ⟨0x800036b8#64, 0x00f60463#32, 0x63#8, 0x04#8, 0xf6#8, 0x00#8,
      .br bop.BEQ true, 12, 15, 0x0008#13, 0#21, 0#12⟩ ;;   -- TAKEN → 0x36c0
  [(0x800036c0#64, 0x03f5d593#32),                -- srli x11,x11,0x3f
   (0x800036c4#64, 0x00048513#32)]                -- mv   x10,x9

/- `gt` (token 22): `li a5,21` ▷ `beq` NOT (22≠21) → 0x36ac; `li a5,22` ▷ `beq`
TAKEN (22=22) → 0x3ae4; then `sgtz x11,x11 ; mv x10,x9` — straight-line to the
jal entry 0x3ae8. -/
#derive_case sTailGt chain
  [(0x800036a4#64, 0x01500793#32)]                -- li x15,21
    terminator ⟨0x800036a8#64, 0x44f60863#32, 0x63#8, 0x08#8, 0xf6#8, 0x44#8,
      .br bop.BEQ false, 12, 15, 0x0450#13, 0#21, 0#12⟩ ;;
  [(0x800036ac#64, 0x01600793#32)]                -- li x15,22
    terminator ⟨0x800036b0#64, 0x42f60a63#32, 0x63#8, 0x0a#8, 0xf6#8, 0x42#8,
      .br bop.BEQ true, 12, 15, 0x0434#13, 0#21, 0#12⟩ ;;   -- TAKEN → 0x3ae4
  [(0x80003ae4#64, 0x00b025b3#32),                -- sgtz x11,x11  (slt x11,x0,x11)
   (0x80003ae8#64, 0x00048513#32)]                -- mv   x10,x9

/- `le` (token 21): `li a5,21` ▷ `beq` TAKEN (21=21) → 0x3af8; then
`slti x11,x11,1 ; mv x10,x9` — straight-line to the jal entry 0x3afc. -/
#derive_case sTailLe chain
  [(0x800036a4#64, 0x01500793#32)]                -- li x15,21
    terminator ⟨0x800036a8#64, 0x44f60863#32, 0x63#8, 0x08#8, 0xf6#8, 0x44#8,
      .br bop.BEQ true, 12, 15, 0x0450#13, 0#21, 0#12⟩ ;;   -- TAKEN → 0x3af8
  [(0x80003af8#64, 0x0015a593#32),                -- slti x11,x11,1
   (0x80003afc#64, 0x00048513#32)]                -- mv   x10,x9

/-! ## `ChainFacts` legs (one `chain_facts` per route)

Each route's branch guards are the only data-dependent leftovers; pinning
`x12 = tok` closes them by `decide` (via `all_goals rfl` after `chain_facts`). -/

theorem sTailLt_facts (σ : MState)
    (cmpV sret : BitVec 64) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem [(11, cmpV), (12, 20#64), (9, sret)] lds sTailLt := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals rfl

theorem sTailGt_facts (σ : MState)
    (cmpV sret : BitVec 64) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem [(11, cmpV), (12, 22#64), (9, sret)] lds sTailGt := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals rfl

theorem sTailLe_facts (σ : MState)
    (cmpV sret : BitVec 64) (lds : List (List (BitVec 8)))
    (h : Vsa.Sim.Code.Eval_exprLoaded σ.mem) :
    ChainFacts σ.mem σ.mem [(11, cmpV), (12, 21#64), (9, sret)] lds sTailLe := by
  chain_facts h with "Vsa.Sim.Code.eval_expr_at_"
  all_goals rfl

/-! ## The sign-word posts and `segToTriple` rows

Each route runs to its op's `jal value_bool` entry PC (lt/ge: `0x800036c8`;
gt: `0x80003ae8`; le: `0x80003afc`), memory unchanged (no stores), with the
boolean payload word in `x11` and `x10 = sret` (the `mv x10,x9`).  The payload
word is the reflected fixup applied to the spaceship scalar `cmpV`:
  lt: `srli cmpV 0x3f`;  le: `slti cmpV 1`;  gt: `sgtz cmpV`. -/

/-- Post of the `lt` sign-test route: parked at `0x800036c8` (the `jal value_bool`
entry), memory unchanged, `x11 = srli cmpV 0x3f`, `x10 = sret`, `x9 = sret`. -/
def STailLtPost (cmpV sret : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x800036c8#64 ∧
  gprGet c.σ 11
    = some (shift_bits_right cmpV (Sail.BitVec.extractLsb (0x3f#6) 5 0)) ∧
  gprGet c.σ 10 = some sret ∧
  gprGet c.σ 9 = some sret

/-- Post of the `gt` sign-test route: parked at `0x80003aec` (the `jal value_bool`
entry, after `sgtz`+`mv`), `x11 = sgtz cmpV`. -/
def STailGtPost (cmpV sret : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80003aec#64 ∧
  gprGet c.σ 11
    = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (0#64) cmpV))) ∧
  gprGet c.σ 10 = some sret ∧
  gprGet c.σ 9 = some sret

/-- Post of the `le` sign-test route: parked at `0x80003b00` (the `jal value_bool`
entry, after `slti`+`mv`), `x11 = slti cmpV 1`. -/
def STailLePost (cmpV sret : BitVec 64) (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some 0x80003b00#64 ∧
  gprGet c.σ 11
    = some (zero_extend (m := 64)
        (bool_to_bit (zopz0zI_s cmpV (sign_extend (m := 64) (0x001#12))))) ∧
  gprGet c.σ 10 = some sret ∧
  gprGet c.σ 9 = some sret

theorem sTailLtRow (cmpV sret : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre sTailLt [(11, cmpV), (12, 20#64), (9, sret)] []
      0x800036a4#64 m0) (STailLtPost cmpV sret m0) := by
  apply segToTriple sTailLt [(11, cmpV), (12, 20#64), (9, sret)] []
    0x800036a4#64 m0 (STailLtPost cmpV sret m0)
    (by show ChainOK 0x800036a4#64 [11, 12, 9] sTailLt; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x800036a4#64 [(11, cmpV), (12, 20#64), (9, sret)] [] sTailLt)
      = some 0x800036c8#64
    rw [chainEndPC_eq_bt sTailLt 0x800036a4#64 [(11, cmpV), (12, 20#64), (9, sret)] [] (by decide)]
    rfl
  · exact gholds_lookup _ hregs (by rfl)
  · have e : (sret + sign_extend (m := 64) (0#12) : BitVec 64) = sret := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sret) _ hregs (by rfl)

theorem sTailGtRow (cmpV sret : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre sTailGt [(11, cmpV), (12, 22#64), (9, sret)] []
      0x800036a4#64 m0) (STailGtPost cmpV sret m0) := by
  apply segToTriple sTailGt [(11, cmpV), (12, 22#64), (9, sret)] []
    0x800036a4#64 m0 (STailGtPost cmpV sret m0)
    (by show ChainOK 0x800036a4#64 [11, 12, 9] sTailGt; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x800036a4#64 [(11, cmpV), (12, 22#64), (9, sret)] [] sTailGt)
      = some 0x80003aec#64
    rw [chainEndPC_eq_bt sTailGt 0x800036a4#64 [(11, cmpV), (12, 22#64), (9, sret)] [] (by decide)]
    rfl
  · exact gholds_lookup _ hregs (by rfl)
  · have e : (sret + sign_extend (m := 64) (0#12) : BitVec 64) = sret := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sret) _ hregs (by rfl)

theorem sTailLeRow (cmpV sret : BitVec 64)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (SegPre sTailLe [(11, cmpV), (12, 21#64), (9, sret)] []
      0x800036a4#64 m0) (STailLePost cmpV sret m0) := by
  apply segToTriple sTailLe [(11, cmpV), (12, 21#64), (9, sret)] []
    0x800036a4#64 m0 (STailLePost cmpV sret m0)
    (by show ChainOK 0x800036a4#64 [11, 12, 9] sTailLe; decide)
  intro σ' i' u' hG' _hi' hmem' hpc' _hmi' hregs
  refine ⟨hG', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hmem']; rfl
  · rw [hpc']
    show some (chainEndPC 0x800036a4#64 [(11, cmpV), (12, 21#64), (9, sret)] [] sTailLe)
      = some 0x80003b00#64
    rw [chainEndPC_eq_bt sTailLe 0x800036a4#64 [(11, cmpV), (12, 21#64), (9, sret)] [] (by decide)]
    rfl
  · exact gholds_lookup _ hregs (by rfl)
  · have e : (sret + sign_extend (m := 64) (0#12) : BitVec 64) = sret := by
      rw [show (sign_extend (m := 64) (0#12) : BitVec 64) = 0#64 from by decide, BitVec.add_zero]
    rw [← e]; exact gholds_lookup _ hregs (by rfl)
  · exact gholds_lookup (v := sret) _ hregs (by rfl)

#print axioms sTailLtRow
#print axioms sTailGtRow
#print axioms sTailLeRow

end Vsa.Sim
