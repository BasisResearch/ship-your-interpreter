# `.ge` (token 23) spec/machine divergence investigation

**Question** (PLAN-InterpSim.md:391): does the machine's `eval_binary` dispatch send op
token 23 (`.ge`) to a runtime_error arm while `binOpSem .ge` succeeds?

**Answer: NO. The flag is stale/mistaken.** Token 23 routes through the operator jump
table to the shared comparison arm and computes exactly `value_bool(cmp >= 0)`, matching
`binOpSem .ge`. There is no desugaring and no divergence — and the `ge` eval case was in
fact already proved and landed (commit `526f575`, 2026-08-28, `evalGeSim`, axiom-clean,
registered at `scripts/check_all.sh:237`). The flag lines should simply be deleted.

---

## 1. Front-end: NO desugaring — `>=` becomes a BINOP with token 23

`c/src/lexer.c:110` — `>=` lexes to a dedicated token:

```c
    case '>':
        if (*lx->cur == '=') { lx->cur++; return make_tok(lx, T_GE, start); }
        return make_tok(lx, T_GT, start);
```

`c/src/lexer.h` enum ordering gives the numeric value (counting from `T_EOF = 0`):

```c
    T_EOF, T_ERROR,                                          /* 0,1   */
    T_IDENT, T_NUMBER, T_STRING,                             /* 2..4  */
    T_LPAREN, T_RPAREN, T_LBRACE, T_RBRACE, T_COMMA, T_SEMI, /* 5..10 */
    T_PLUS, T_MINUS, T_STAR, T_SLASH, T_PERCENT,             /* 11..15 */
    T_BANG, T_BANG_EQ, T_EQ, T_EQ_EQ, T_LT, T_LE, T_GT, T_GE,/* 16..23 → T_GE = 23 */
```

This matches `Vsa/MemRepr.lean:63` `binOpTok`: `.ge => 23`.

`c/src/parser.c` — the comparison level includes `T_GE` verbatim and `binary_level`
stores the raw token into the AST node (no swap, no negation, no rewrite):

```c
static Expr *comparison(Parser *p) {
    static const TokType ops[] = { T_LT, T_LE, T_GT, T_GE };
    return binary_level(p, term, ops, 4);
}
```
and inside `binary_level` (parser.c:~240):
```c
                Expr *b = new_expr(EX_BINARY, op.line);
                b->as.binary.op = op.type;      /* T_GE = 23 stored directly */
```

So machine-resident ASTs for programs containing `>=` DO contain kind-6 (`EX_BINARY`)
nodes with op field 23. `.ge` is fully reachable from `Loaded` ASTs.

## 2. C interpreter source: token 23 is a handled, succeeding case

`c/src/interp.c:147-165` (`eval_binary`):

```c
    case T_LT: case T_LE: case T_GT: case T_GE: {
        long long cmp;
        if (l.kind == VAL_STR && r.kind == VAL_STR) {
            cmp = strcmp(l.as.s, r.as.s);
        } else {
            ...
            cmp = (a > b) - (a < b);
        }
        switch (op) {
        case T_LT: return value_bool(cmp < 0);
        case T_LE: return value_bool(cmp <= 0);
        case T_GT: return value_bool(cmp > 0);
        default: return value_bool(cmp >= 0);   /* <- T_GE, succeeds */
        }
    }
    default:
        runtime_error(in, line, "unknown binary operator", 0, 0);
```

The `runtime_error` default is only for tokens with no case — within the jump-table
range those are 16 (`T_BANG`) and 18 (`T_EQ`), which are not in `binOpTok`'s image and
cannot appear in an `ExprRepr .binary` node.

## 3. Compiled machine dispatch: token 23 routes to the comparison arm

`experiments/disasm.txt`, `eval_binary` dispatch (inside `eval_expr`):

```
80003528: ff56079b  addiw a5,a2,-11          # index = token - 11
80003534: 3ef76a63  bltu  a4,a5,80003928     # a4 = 12: error iff index > 12
80003540: 00017717  auipc a4,0x17
80003544: a4470713  addi  a4,a4,-1468        # 80019f84 <CSWTCH.18+0x5c> = opTableBase
8000354c: 0007a783  lw    a5,0(a5)           # slot = table[index]
80003558: 00078067  jr    a5                 # jump to opTableBase + slot
```

Token 23 → index 12 — the **last in-range index**; the `bltu` guard (`12 < index`)
does NOT fire. The runtime_error default at `0x80003928` (loads the message at
`0x80019458`, the "unknown binary operator" string) is reached only for index > 12,
i.e. tokens outside 11..23 — never for token 23.

The slot for index 12 sits at `opTableBase + 48 = 0x80019fb4` with bytes
`a4 96 fe ff` — pinned and machine-checked in `Vsa/Sim/EvalGeChain.lean:44`
(`GeSlotPinned`): target `0x80019f84 + (Int32)0xfffe96a4 = 0x80003628`, the **shared
comparison arm** (same entry lt/le/gt use). The arm (disasm):

```
80003628: addi a5,a0,-3 ; bnez ...           # str/str kind check → strcmp path 0x80003b0c
80003698: 0138a733  slt  a4,a7,s3            # spaceship: cmp = (a>b)-(a<b)
800036a0: 40f705bb  subw a1,a4,a5
800036a4: li a5,21 ; 800036a8: beq a2,a5,80003af8   # T_LE = 21
800036ac: li a5,22 ; 800036b0: beq a2,a5,80003ae4   # T_GT = 22
800036b4: li a5,20 ; 800036b8: beq a2,a5,800036c0   # T_LT = 20 (skip the not)
800036bc: fff5c593  not  a1,a1               # <- token 23 (T_GE) FALLS THROUGH here
800036c0: 03f5d593  srli a1,a1,0x3f          # sign bit of ¬cmp  =  decide (cmp ≥ 0)
800036c8: 930ff0ef  jal  800027f8 <value_bool>
```

Token 23 falls through all three `beq`s into `not a1,a1` then the shared `srli`:
result = `value_bool(¬cmp < 0)` = `value_bool(cmp ≥ 0)`. Exactly the C source's
`default: return value_bool(cmp >= 0)` — GCC compiled the inner switch's *default*
(GE) as the fall-through, which is the likely origin of the misreading: GE is the one
comparison token with no explicit `beq`/case label in either switch, so a quick scan
maps it to "default", and the *outer* switch's default is runtime_error.

## 4. Spec side: agreement

`Vsa/While/Semantics.lean` `binOpSem`:

```lean
  | .ge, .str a, .str b => some (.bool (b < a || a == b))   -- strcmp ≥ 0
  | .ge, .int a, .int b => some (.bool (a ≥ b))             -- cmp ≥ 0
```

Machine and spec agree on both payload kinds. Mixed/non-int-non-str kinds:
spec `none` (falls to `_,_,_`); machine `int_operand` raises a runtime type error —
the same stuck/error correspondence used by every other comparison op, nothing
ge-specific.

`Vsa/While/Ast.lean:15`: `.ge` is an ordinary `BinOp` constructor. `Vsa/MemRepr.lean`
`ExprRepr.binary` requires `read32 m (a+8) = some (binOpTok op)`, so a resident BINOP
node with op field 23 represents precisely `.binary .ge …`. No well-formedness layer
excludes it — correctly so, since the parser emits it (§1).

## 5. Already resolved in the proof stack (the flag is stale)

- Commit `526f575` "Land ge eval case: evalGeSim + blockC_ge green + axiom-clean"
  (2026-08-28): `Vsa/Sim/EvalGeChain.lean` + `Vsa/Sim/rows/EvalGeRow.lean`.
  `evalGeSim` (EvalGeRow.lean:804) proves the `EvalE.binary .ge` **int** case ending in
  `EvalExitD … (.bool (a ≥ b))` — the machine ladder-fallthrough (`not`+`srli`) bridged
  to `decide (a ≥ b)`. Registered: `scripts/check_all.sh:237`.
- `experiments/exponentiation-endgame-design.md` (§ binary-op fan-out) documents the
  landing, including the token-23 fall-through reading above.
- The `.ge` **str** case is unproven — but so are the str cases of lt/le/gt (all four
  landed int-only). Uniform residual coverage, not a divergence.

## RECOMMENDATION — (c): no divergence, nothing to change in Semantics.lean

The flag was a misreading of the compiled dispatch (GE = inner-switch default =
fall-through arm, confused with the outer-switch runtime_error default; the `bltu`
bound is `index > 12`, and 23 maps to index 12 exactly). Both source and binary
handle `>=`; the spec matches; the proof is already landed and axiom-clean.

Concrete cleanup (documentation only, no Lean changes):
1. Delete the FLAG at `PLAN-InterpSim.md:391-392` and the parenthetical at line 418;
   optionally replace with: "`.ge` verified non-divergent — token 23 → CSWTCH.18 slot
   12 → shared comparison arm fall-through (`not`+`srli` = `cmp ≥ 0`); `evalGeSim`
   landed 526f575."
2. Delete the "resolve the semantics decision BEFORE proving" bullet at
   `experiments/interp-sim-completion-plan.md:42-44` (the decision is moot; ge is
   listed as landed elsewhere in the same doc set).

No AST well-formedness premise is needed (option (a) is wrong — token 23 IS emitted
by the parser and IS handled), and no error-amendment to `binOpSem .ge` is needed
(option (b) is wrong — the shipped artifact succeeds on token 23).
