-- hSVarInit: mined invariant candidate (invgen.py, ANALYSIS ONLY — a DRAFT for the proving agent; Law 4 applies).
-- cluster env-seam  target TermResidualsCore.hSVarInit
namespace InvGen_hSVarInit

-- MINED KIND BRIDGE (machine==spec count, per-seam ordinal aligned): read32[node]&0xff = kindOfStmt node.
--   tag 0  ↔  kindOfStmt node = .expr
--   tag 1  ↔  kindOfStmt node = .varDecl
--   tag 2  ↔  kindOfStmt node = .block
--   tag 4  ↔  kindOfStmt node = .whileStmt

/-- machine kind byte ↔ spec kind tag, per aligned event. -/
structure KindBridge (mach spec : List Nat) : Prop where
  len : mach.length = spec.length
  agree : mach = spec

-- the MINED pairing (machine tags = spec tags, as traced).
def machTags : List Nat := [0, 1, 2, 4]
def specTags : List Nat := [0, 1, 2, 4]
def mined : Prop := KindBridge machTags specTags
def machTagsMutant : List Nat := [100, 1, 2, 4]
def mutant : Prop := KindBridge machTagsMutant specTags

end InvGen_hSVarInit
