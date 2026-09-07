import Vsa.Sim.WriteLogNF

/- Computable byte reads from finite write logs. The initial memory is a
   function parameter; no initial hash map is constructed or unfolded. -/

namespace Vsa.Sim

/-- A byte supplied by one entry. Unsupported widths supply no byte, exactly
as `applyW`. Address tests follow the concrete insert order, newest first. -/
def writeEntryByte (entry : WEntry) (address : Nat) : Option (BitVec 8) :=
  match entry with
  | (base, 1, data) =>
      if base == address then some (sbData data) else none
  | (base, 2, data) =>
      if base + 1 == address then some ((shData data).extractLsb' 8 8)
      else if base == address then some ((shData data).extractLsb' 0 8)
      else none
  | (base, 4, data) =>
      if base + 3 == address then some ((swData data).extractLsb' 24 8)
      else if base + 2 == address then some ((swData data).extractLsb' 16 8)
      else if base + 1 == address then some ((swData data).extractLsb' 8 8)
      else if base == address then some ((swData data).extractLsb' 0 8)
      else none
  | (base, 8, data) =>
      if base + 7 == address then some ((sdData_val data).extractLsb' 56 8)
      else if base + 6 == address then some ((sdData_val data).extractLsb' 48 8)
      else if base + 5 == address then some ((sdData_val data).extractLsb' 40 8)
      else if base + 4 == address then some ((sdData_val data).extractLsb' 32 8)
      else if base + 3 == address then some ((sdData_val data).extractLsb' 24 8)
      else if base + 2 == address then some ((sdData_val data).extractLsb' 16 8)
      else if base + 1 == address then some ((sdData_val data).extractLsb' 8 8)
      else if base == address then some ((sdData_val data).extractLsb' 0 8)
      else none
  | _ => none

/-- One functional update, retaining the prior byte on a miss. -/
def entryRead (prior : Option (BitVec 8)) (entry : WEntry) (address : Nat) :
    Option (BitVec 8) :=
  match writeEntryByte entry address with
  | some byte => some byte
  | none => prior

/-- Lookup in a newest-first log. A matching entry does not evaluate `initial`. -/
def logReadNewest (initial : Nat → Option (BitVec 8)) :
    List WEntry → Nat → Option (BitVec 8)
  | [], address => initial address
  | entry :: rest, address =>
      match writeEntryByte entry address with
      | some byte => some byte
      | none => logReadNewest initial rest address

/-- `writeLog` uses program order. Reverse once, then stop at the newest match. -/
def logRead (initial : Nat → Option (BitVec 8)) (log : List WEntry)
    (address : Nat) : Option (BitVec 8) :=
  logReadNewest initial log.reverse address

/-- Exact one-entry byte semantics, including unsupported widths. -/
theorem applyW_getElem?_entryRead (m : Std.ExtHashMap Nat (BitVec 8))
    (entry : WEntry) (address : Nat) :
    (applyW m entry)[address]? = entryRead (m[address]?) entry address := by
  rcases entry with ⟨base, width, data⟩
  by_cases h1 : width = 1
  · subst width
    simp [applyW, entryRead, writeEntryByte, Std.ExtHashMap.getElem?_insert]
    repeat' (split <;> simp_all)
  by_cases h2 : width = 2
  · subst width
    simp [applyW, entryRead, writeEntryByte, Std.ExtHashMap.getElem?_insert]
    repeat' (split <;> simp_all)
  by_cases h4 : width = 4
  · subst width
    simp only [applyW, entryRead, writeEntryByte, writeMap4,
      Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    by_cases h3 : base + 3 = address
    · simp [h3]
    by_cases h2 : base + 2 = address
    · simp [h2, h3]
    by_cases h1 : base + 1 = address
    · simp [h1, h3, h2]
    by_cases h0 : base = address
    · simp [h0, h3, h2, h1]
    simp [h0, h1, h2, h3]
  by_cases h8 : width = 8
  · subst width
    simp only [applyW, entryRead, writeEntryByte, writeMap8,
      Std.ExtHashMap.getElem?_insert, beq_iff_eq]
    by_cases h7 : base + 7 = address
    · simp [h7]
    by_cases h6 : base + 6 = address
    · simp [h6, h7]
    by_cases h5 : base + 5 = address
    · simp [h5, h7, h6]
    by_cases h4 : base + 4 = address
    · simp [h4, h7, h6, h5]
    by_cases h3 : base + 3 = address
    · simp [h3, h7, h6, h5, h4]
    by_cases h2 : base + 2 = address
    · simp [h2, h7, h6, h5, h4, h3]
    by_cases h1 : base + 1 = address
    · simp [h1, h7, h6, h5, h4, h3, h2]
    by_cases h0 : base = address
    · simp [h0, h7, h6, h5, h4, h3, h2, h1]
    simp [h0, h1, h2, h3, h4, h5, h6, h7]
  · rw [applyW_eq_of_ne m base width data h1 h2 h4 h8]
    simp [entryRead, writeEntryByte, h1, h2, h4, h8]

private theorem writeLog_getElem?_fold (m : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (address : Nat) :
    (writeLog m log)[address]? =
      log.foldl (fun prior entry => entryRead prior entry address) (m[address]?) := by
  induction log generalizing m with
  | nil => rfl
  | cons entry rest ih =>
      change (writeLog (applyW m entry) rest)[address]? =
        rest.foldl (fun prior entry => entryRead prior entry address)
          (entryRead (m[address]?) entry address)
      rw [ih, applyW_getElem?_entryRead]

private theorem logReadNewest_eq_foldr (initial : Nat → Option (BitVec 8))
    (log : List WEntry) (address : Nat) :
    logReadNewest initial log address =
      log.foldr (fun entry prior => entryRead prior entry address) (initial address) := by
  induction log with
  | nil => rfl
  | cons entry rest ih =>
      simp only [logReadNewest, List.foldr_cons, entryRead]
      cases writeEntryByte entry address <;> simp_all
      all_goals rfl

/-- Byte reads reduce to the finite write log and one abstract initial byte.
No size or support hypothesis is required for the initial memory. -/
theorem writeLog_getElem?_logRead (m : Std.ExtHashMap Nat (BitVec 8))
    (log : List WEntry) (address : Nat) :
    (writeLog m log)[address]? = logRead (fun a => m[a]?) log address := by
  rw [writeLog_getElem?_fold, List.foldl_eq_foldr_reverse]
  exact (logReadNewest_eq_foldr (fun a => m[a]?) log.reverse address).symm

/-- Substitute an already-proved initial byte interface before reducing a log. -/
theorem writeLog_getElem?_logRead_of_initial
    (m : Std.ExtHashMap Nat (BitVec 8)) (initial : Nat → Option (BitVec 8))
    (h : ∀ a, m[a]? = initial a) (log : List WEntry) (address : Nat) :
    (writeLog m log)[address]? = logRead initial log address := by
  rw [writeLog_getElem?_logRead]
  have heq : (fun a => m[a]?) = initial := funext h
  rw [heq]

end Vsa.Sim
