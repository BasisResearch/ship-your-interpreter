# Approved AST ownership correction

Status: approved by the user after review of the output-alias refutation.
Implementation and the 1,407-module integration build passed. The earlier
physical correction remains in force. General write preservation is still open.

Add a data-only requirement that every represented AST read lies outside mutable
storage. Include literal/name bytes and their terminating NUL. Permit immutable
sharing between nodes, literals, names, and string suffixes.

This excludes the checked stdout-buffer alias. It does not establish the repaired
refinement theorem or settle allocation and resource obligations.

## Proposed predicate

Add hereditary `Within` variants of the existing representation relations in
`Vsa/MemRepr.lean`. Preserve their current premises and semantic indices. For
an allowed-byte predicate `P : Nat → Prop`:

```lean
def Covers (P : Nat → Prop) (a width : Nat) : Prop :=
  ∀ i, i < width → P (a + i)

def CStringWithin (m : Mem) (P : Nat → Prop) (a : Nat) (s : String) : Prop :=
  CString m a s ∧ ∀ i, i ≤ s.length → P (a + i)
```

Every `read32` premise additionally requires `Covers P a 4`; `read64` and
`readI64` require width 8. Every CString and recursive representation premise
uses its `Within` variant. This applies to all children, branches, function
bodies, parameter names, and pointer arrays. Empty arrays consume no cells;
their parent pointer/count fields remain covered. Empty strings consume their
NUL byte. The existing CString relation requires ASCII.

Prove that `ProgramReprWithin` implies `ProgramRepr`, and that agreement on `P`
transports the owned representation. These proofs must follow the representation
derivation. No execution or preservation assumption enters the boundary.

## Mutable bytes to exclude

`AstMutableByte m A globalEnv k` is the union of:

1. The fixed writable ELF interval `[0x8001ad00, 0x8001c168)`, covering
   `.tohost`, `.data`, `.init_array.00000`, and `.bss`.
2. The existing `stackSL` interval.
3. The existing arena `A`.
4. The initial global frame's 32-byte header and full-capacity names/value
   arrays. Read capacity and pointers from header offsets 4, 8, and 16; exclude
   `8 * capacity` and `24 * capacity` bytes respectively.

The fourth term is necessary because current `StoreRepr` does not constrain
those arrays to lie inside `A`. It excludes the mutable pointer/value cells,
not the immutable name strings they reference. `.rodata` remains available.

## Exact boundary addition

Add this field to concrete `InterpRunReadyFacts`, using its existing parameters:

```lean
ast_owned : ∀ p : Vsa.While.Program,
  ProgramRepr c.σ.mem stmts count p →
  ProgramReprWithin c.σ.mem
    (fun k => ¬ AstMutableByte c.σ.mem A (φf 0) k)
    stmts count p
```

This narrows the concrete `Loaded` premise while preserving the generic
`Refine.Loaded` shape. Its quantification concerns the fixed initial byte graph.
It does not quantify over future executions or unrelated exit states.

Freeze `P` at the initial memory and region parameters. Derive its preservation
from actual instruction and callee effects. Recomputing the excluded regions
from later, overwritten environment pointers would be unsound.

The checked alias is excluded directly: its empty literal requires ownership
of `0x8001bb97`, which lies in the excluded writable image. The same requirement
covers mutable aliases in names, array cells, and node fields. Pairwise
separation between immutable AST objects is unnecessary.

## Remaining work and approval scope

Prove that actual writes preserve the owned bytes. The current allocator
contract has an arbitrary `privFoot`; its concrete instance needs a proved
relationship to the excluded storage. Ownership does not supply valid allocator
metadata, missing access geometry, sufficient heap, or sufficient C stack.
Those remain separate obligations. No sufficiency claim is made for this repair.

Approval covers only the hereditary ownership field and the four explicit
exclusions above. It does not authorize a resource policy, semantic axiom,
execution-relation change, or ELF change. Preserve the old boundary and its
closed counterexample under explicit historical definitions when migrating.

The ELF is unchanged: SHA256
`b146c6edb76ea9a0f0f30be381f8176ed2de9717e1ae9b37feff4b2b9ca1d0f0`.
The writable extent comes from its section table. The generic representation
variants live in additive `Vsa/MemReprWithin.lean`; existing `MemRepr` constructors
remain available. This avoids invalidating unrelated users of the base relations.
