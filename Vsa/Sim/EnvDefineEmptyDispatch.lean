import Vsa.Sim.rows.EnvDefineEmptyLane
import Vsa.Sim.WordLoadData
import Vsa.Sim.SegEffect

namespace Vsa.Sim.EnvDefineEmptyDispatch

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.RuntimeRepr Vsa.Alloc

/-- The empty frame supplies the two loads before initial array allocation. -/
structure Pre (env names : BitVec 64) (before : Config) : Prop where
  good : GoodState before.σ
  tick : before.tick < 2
  pc : before.σ.regs.get? Register.PC = some 0x80002a90#64
  minstret : ∃ w, before.σ.regs.get? Register.minstret = some w
  envReg : before.σ.regs.get? Register.x10 = some env
  countReg : before.σ.regs.get? Register.x19 = some 0#64
  geometry : EnvRecordGeom env
  capacity : read32 before.σ.mem (env.toNat + 4) = some 0
  namesRead : read64 before.σ.mem (env.toNat + 8) = some names.toNat
  code : Code.Env_defineLoaded before.σ.mem

/-- The existing zero-capacity span reaches the initial realloc entry. -/
structure Post (names : BitVec 64) (before after : Config) : Prop where
  good : GoodState after.σ
  tick : after.tick < 2
  pc : after.σ.regs.get? Register.PC = some 0x80002b98#64
  minstret : ∃ w, after.σ.regs.get? Register.minstret = some w
  namesReg : after.σ.regs.get? Register.x22 = some names
  capacityReg : after.σ.regs.get? Register.x15 = some 8#64
  requestReg : after.σ.regs.get? Register.x11 = some 64#64
  memory : after.σ.mem = before.σ.mem
  output : after.σ.sailOutput = before.σ.sailOutput
  frame : ∀ R, KeepButS6 R = true → after.σ.regs.get? R = before.σ.regs.get? R

/-- Derive both loads and the taken branches from the represented empty frame. -/
theorem Pre.facts {env names : BitVec 64} {before : Config} (h : Pre env names before) :
    ∃ namesBytes,
      ChainFacts before.σ.mem before.σ.mem (envDefineCapInitL env 0#64)
        [wordLds4 before.σ.mem (env.toNat + 4), namesBytes] envDefineCapInitZeroSeg ∧
      bytesVal .ld namesBytes = names := by
  let L := envDefineCapInitL env 0#64
  let loadCap := mkLine 0x80002bf4#64 0x00452783#32
  let loadNames := mkLine 0x80002bfc#64 0x00853b03#32
  let capBytes := wordLds4 before.σ.mem (env.toNat + 4)
  have capAddr : (eaddrM loadCap L).toNat = env.toNat + 4 := by
    change (env + 4#64).toNat = env.toNat + 4
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.geometry.hi; change env.toNat + 4 < 2^64; omega)]
    rfl
  have capFacts : MemFacts before.σ.mem L capBytes loadCap := by
    unfold MemFacts
    change (0x80000000 ≤ (eaddrM loadCap L).toNat ∧
      (eaddrM loadCap L).toNat + 4 ≤ 0x100000000 ∧
      ((eaddrM loadCap L).toNat + 4 ≤ tohostAddr ∨
        tohostAddr + 8 ≤ (eaddrM loadCap L).toNat)) ∧ _
    rw [capAddr]
    refine ⟨⟨?_, ?_, ?_⟩, by simp [LPins4, capBytes, wordLds4]⟩
    · have := h.geometry.lo; omega
    · have := h.geometry.hi; omega
    · have := h.geometry.htif; omega
  have capValue : bytesVal .lw capBytes = 0#64 :=
    bytesVal_lw_wordLds4 before.σ.mem (env.toNat + 4) 0 (by decide) h.capacity
  let Lnames := runGM [loadCap] L [capBytes]
  have namesAddr : (eaddrM loadNames Lnames).toNat = env.toNat + 8 := by
    change (env + 8#64).toNat = env.toNat + 8
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by
      have := h.geometry.hi; change env.toNat + 8 < 2^64; omega)]
    rfl
  obtain ⟨namesBytes, B⟩ := wordLoadFacts_of_read64 before.σ.mem Lnames loadNames names rfl
    (by rw [namesAddr]; have := h.geometry.lo; omega)
    (by rw [namesAddr]; have := h.geometry.hi; omega)
    (by rw [namesAddr]; have := h.geometry.htif; omega)
    (by rw [namesAddr]; exact h.namesRead)
  refine ⟨namesBytes, ?_, B.value⟩
  chain_facts h.code with "Vsa.Sim.Code.env_define_at_"
  · change guardB bop.BGE (0#64) (0#64) = true
    decide
  · exact capFacts
  · change guardB bop.BNE (bytesVal .lw capBytes) (0#64) = false
    rw [capValue]; decide
  · exact B.facts
  · change guardB bop.BNE (bytesVal .lw capBytes) (0#64) = false
    rw [capValue]; decide

/-- Execute the initial-allocation dispatch while preserving the caller's saved registers. -/
theorem run {env names : BitVec 64} {before : Config} (h : Pre env names before) :
    ∃ after, Steps before after ∧ Post names before after := by
  obtain ⟨namesBytes, facts, namesValue⟩ := h.facts
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed envDefineCapInitZeroSeg (envDefineCapInitL env 0#64)
    [wordLds4 before.σ.mem (env.toNat + 4), namesBytes] 0x80002a90#64 vm
    (fun _ => False) KeepButS6 [(22, names), (15, 8#64), (11, 64#64)] before
    h.good h.pc hvm ⟨h.countReg, h.envReg, trivial⟩ (by change KeysOK [19, 10]; decide) facts
    (by change ChainOK 0x80002a90#64 [19, 10] envDefineCapInitZeroSeg; decide) h.tick
    (by intro k _; rfl) (by decide) (by decide) (by
      change some (bytesVal .ld namesBytes) = some names ∧
        some 8#64 = some 8#64 ∧ some 64#64 = some 64#64 ∧ True
      simp only [namesValue, and_true])
  obtain ⟨namesReg, capacityReg, requestReg, _⟩ := C.selected_regs
  exact ⟨after, C.steps,
    { good := C.good, tick := C.tick, pc := C.pc, minstret := C.minstret
      namesReg := namesReg, capacityReg := capacityReg, requestReg := requestReg
      memory := C.mem, output := C.output, frame := C.reg_frame }⟩

#print axioms Pre.facts
#print axioms run

end Vsa.Sim.EnvDefineEmptyDispatch
