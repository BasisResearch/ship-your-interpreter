# Approved AST readability correction

Status: approved and implemented. See `PROOF_CLOSURE_PLAN.md` for verification.

Require every represented AST byte to lie in normal readable RAM:
`[0x80000000, 0x100000000)`. Retain the approved ownership condition.

## Checked obstruction

The preceding ownership-only boundary admits the source program `0; 0;` with its statement node
at `0x4000`. That address is outside the machine's readable regions, although
its bytes exist in the mathematical memory map and satisfy AST ownership.

The source terminates with empty output. The machine reaches the tag load
`lw a5,0(s0)` at `0x80004014` after 70 proved steps. Memory attributes reject
the read. The admitted register map lacks `mcause`, so handling that trap
returns `Unreachable`. Lean proves that the initial state cannot halt with any
output or exit code.

`Vsa/Sim/AstAccessAudit/AccessRefutation.lean` therefore refutes
`InterpSim BeforeAstReadability.interpRunLayout`, its `RemainingWork`
constructor, and that historical boundary’s behavioral correspondence. See `PROOF_CLOSURE_PLAN.md` for build and audit status.

## Exact additional field

The approved field in concrete `InterpRunReadyFacts` is:

```lean
ast_readable : ∀ p : Vsa.While.Program,
  ProgramRepr c.σ.mem stmts count p →
  ProgramReprWithin c.σ.mem
    (fun k => 0x80000000 ≤ k ∧ k < 0x100000000)
    stmts count p
```

Use the existing hereditary `ProgramReprWithin`. Cover each node field,
pointer-array cell, recursive child, literal, name, and terminating NUL.
Empty arrays consume no cells. Immutable sharing remains allowed.

The normal RAM interval comes from `GoodState`'s fixed memory attributes.
Its upper bound is `0x100000000`; the sparse replay's populated extent ending
at `0x88000000` is not the machine's RAM limit. This proposal excludes AST
storage in IO and signature regions as well as unmapped addresses.

Do not add alignment requirements. The machine supports split unaligned reads.
The existing representation already proves the presence and values of all
consumed bytes; the new field supplies their physical address range.

`AccessReadability.access_not_readable` proves that this exact byte-range
condition excludes the checked witness. It does not prove full refinement.

## Migration and approval scope

Preserve the preceding ownership boundary and its closed counterexample under an
explicit `BeforeAstReadability` layout. Extend its ready-facts record with the
field above. Keep the earlier `BeforeAstOwnership` boundary unchanged.

Derive physical read geometry from the represented byte ranges at actual
execution sites. Preserve readability through the same immutable-byte
agreement used for ownership. Do not assume future execution succeeds.

Approval covers only this hereditary RAM-range field and the corresponding
historical-boundary migration. It does not authorize a resource policy,
register-initialization change, execution assumption, semantic change, or ELF
change. Allocation, finite stack/heap resources, and general recursive
preservation remain separate proof obligations.
