-- hFn: mined invariant candidate (invgen.py, ANALYSIS ONLY — a DRAFT for the proving agent; Law 4 applies).
-- cluster str-seam  target TermResidualsCore.hFn
namespace InvGen_hFn

-- MINED KIND BRIDGE (machine==spec count, per-seam ordinal aligned): read32[node]&0xff = kindOfExpr node.
--   tag 0  ↔  kindOfExpr node = .int
--   tag 1  ↔  kindOfExpr node = .str
--   tag 4  ↔  kindOfExpr node = .var
--   tag 6  ↔  kindOfExpr node = .binary
--   tag 9  ↔  kindOfExpr node = .call

/-- machine kind byte ↔ spec kind tag, per aligned event. -/
structure KindBridge (mach spec : List Nat) : Prop where
  len : mach.length = spec.length
  agree : mach = spec

-- the MINED pairing (machine tags = spec tags, as traced).
def machTags : List Nat := [0, 1, 4, 6, 9]
def specTags : List Nat := [0, 1, 4, 6, 9]
def mined : Prop := KindBridge machTags specTags
def machTagsMutant : List Nat := [100, 1, 4, 6, 9]
def mutant : Prop := KindBridge machTagsMutant specTags

end InvGen_hFn
