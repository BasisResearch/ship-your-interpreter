import VsaIris.Vsa.SymData
import VsaIris.Vsa.BinDom
import Vsa.Sim.TextImage

/-!
# Machine-layer glue for piece footprints

Generic membership facts for texts built with `piecesText`: code footprints of a
literal instruction (`codeFoot`), data accesses (`accAddrs`), and the evaluation of
constant-table loads (`imgLoad`). Each fact is one lemma applied to a Boolean check
that `decide` evaluates at the literal address.
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr

/-- The code footprint of the literal bytes `code` at `i` lies in a piece footprint. -/
theorem codeFoot_mem_pieces {ps : List TextPiece} {i : Nat} {code : List (BitVec 8)}
    (h : bytesHasB ps i code = true) : ∀ p ∈ codeFoot i code, (p.1, p.2.2) ∈ piecesText ps := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
  exact mem_piecesText (piecesHasB_of_bytes h hq)

/-- An access of `w` bytes at `a` reads the piece `⟨img, rs⟩` when it lies in `rs`. -/
theorem accAddrs_mem_piece {img : Nat → BitVec 8} {rs : List (Nat × Nat)} {a w : Nat}
    (h : (accAddrs a w).all (inRangesB rs) = true) :
    ∀ b ∈ accAddrs a w, (b, img b) ∈ piecesText [⟨img, rs⟩] := by
  intro b hb
  exact mem_piecesText (by
    simp only [piecesHasB, List.any_cons, List.any_nil, Bool.or_false, beq_self_eq_true,
      Bool.and_true]
    exact List.all_eq_true.1 h b hb)

/-- The byte function of a piece text agrees with memory where the text is loaded. -/
theorem TextLoaded.pin {ps : List TextPiece} {m : Mem} (h : TextLoaded (piecesText ps) m)
    {a : Nat} {b : BitVec 8} (hb : piecesHasB ps a b = true) : m[a]? = some b :=
  TextIn.pin h hb

/-- An eight-byte constant word read from a piece text, from one Boolean check. -/
theorem lpins8_of_text {ps : List TextPiece} {m : Mem} (h : TextLoaded (piecesText ps) m)
    {a : Nat} {bs : List (BitVec 8)} (hl : bs.length = 8) (hb : bytesHasB ps a bs = true) :
    LPins8 m a bs := by
  have g : ∀ k (hk : k < 8), (m[a + k]?).getD 0 = bs.getD k 0#8 := fun k hk => by
    rw [h.pin (bytesHasB_get hb k (by omega))]
    have hk' : k < bs.length := by omega
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk']
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega),
    g 4 (by omega), g 5 (by omega), g 6 (by omega), g 7 (by omega)⟩

open Lean Meta Simp in
/-- Evaluate a load `bytesVal k (bytesAt img a n)` from a closed image function at a closed
    address. The value is computed by the compiled image function and certified by `rfl`
    (kernel reduction of the same expression). -/
simproc_decl imgLoad (bytesVal _ (bytesAt _ _ _)) := fun e => do
  if e.hasFVar || e.hasMVar then return .continue
  -- only a named image function (a closed byte function the kernel evaluates), never a
  -- memory view such as `imgM Mt`
  let e' ← whnfR e
  unless e'.isAppOfArity ``bytesVal 2 do return .continue
  let ba := e'.appArg!
  unless ba.isAppOfArity ``bytesAt 3 && (ba.getArg! 0).isConst do return .continue
  let v ← unsafe evalExpr Nat (mkConst ``Nat)
    (mkApp2 (mkConst ``BitVec.toNat) (mkNatLit 64) e)
  let lit := toExpr (BitVec.ofNat 64 v)
  let pf ← mkExpectedTypeHint (← mkEqRefl e) (← mkEq e lit)
  return .done { expr := lit, proof? := some pf }

end VsaIris.Sym
