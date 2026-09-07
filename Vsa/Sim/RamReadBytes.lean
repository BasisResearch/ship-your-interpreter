import Vsa.Sim.RamReadPolicy

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- A total little-endian byte sequence, including zero-valued absent bytes. -/
def bytesT (m : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : (w : Nat) → BitVec (8 * w)
  | 0 => 0
  | w + 1 => ((bytesT m (a + 1) w).append ((m[a]?).getD 0)).cast (by omega)

/-- The selected bit belongs to its containing byte. -/
theorem getLsbD_bytesT (m : Std.ExtHashMap Nat (BitVec 8)) (w a k : Nat)
    (hk : k < 8 * w) :
    (bytesT m a w).getLsbD k = ((m[a + k / 8]?).getD 0).getLsbD (k % 8) := by
  induction w generalizing a k with
  | zero => simp at hk
  | succ w ih =>
    simp only [bytesT, BitVec.getLsbD_cast, BitVec.append_eq, BitVec.getLsbD_append]
    by_cases hlo : k < 8
    · simp [hlo, Nat.div_eq_of_lt hlo, Nat.mod_eq_of_lt hlo]
    · have hrest : k - 8 < 8 * w := by omega
      rw [if_neg hlo, ih (a + 1) (k - 8) hrest]
      have ha : a + 1 + (k - 8) / 8 = a + k / 8 := by omega
      have hb : (k - 8) % 8 = k % 8 := by omega
      rw [ha, hb]

/-- Extracting consecutive bytes agrees with a total read at the offset. -/
theorem bytesT_extract (m : Std.ExtHashMap Nat (BitVec 8)) (a w off d : Nat)
    (hspan : off + d ≤ w) :
    (bytesT m a w).extractLsb' (8 * off) (8 * d) = bytesT m (a + off) d := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro k hk
  rw [BitVec.getLsbD_extractLsb', getLsbD_bytesT m w a (8 * off + k) (by omega),
    getLsbD_bytesT m d (a + off) k hk]
  have ha : a + (8 * off + k) / 8 = a + off + k / 8 := by omega
  have hb : (8 * off + k) % 8 = k % 8 := by omega
  simp [hk, ha, hb]

/-- The actual Sail byte reader is total and preserves the complete state. -/
theorem readBytes_total (σ : SequentialState RegisterType trivialChoiceSource) (w a : Nat) :
    (PreSail.readBytes (ue := LeanRV64DExecutable.exception) w a).run σ = .ok (bytesT σ.mem a w, none) σ := by
  induction w generalizing a with
  | zero => rfl
  | succ w ih =>
    cases w with
    | zero =>
      simp [PreSail.readBytes, PreSail.readByte, bytesT, BitVec.append_eq, bind, EStateM.bind,
        pure, EStateM.pure, EStateM.run, get, getThe, MonadStateOf.get, EStateM.get]
      simpa using (BitVec.zero_width_append (0#0) ((σ.mem[a]?).getD (0#8))).symm
    | succ w =>
      have hr := ih (a + 1)
      simp only [EStateM.run] at hr
      simp only [PreSail.readBytes, PreSail.readByte, bind, EStateM.bind,
        pure, EStateM.pure, EStateM.run, get, getThe, MonadStateOf.get, EStateM.get]
      rw [hr]
      rfl

/-- Width-generic RAM leaf with the model's total byte semantics. -/
theorem read_ram_total (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) w false).run σ =
      .ok (bytesT σ.mem a.toNat w, ()) σ := by
  have hr := readBytes_total σ w a.toNat
  simp only [EStateM.run] at hr
  simp only [Functions.read_ram, PreSail.sail_mem_read, bind, EStateM.bind,
    pure, EStateM.pure, EStateM.run, Bool.false_eq_true, if_false]
  erw [hr]
  rfl

#print axioms bytesT_extract
#print axioms readBytes_total
#print axioms read_ram_total
#print axioms getLsbD_bytesT
end Vsa.Sim
