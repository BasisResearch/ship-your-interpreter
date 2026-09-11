import Vsa.Sim.StrlenWordRun

namespace Vsa.Sim.StrlenRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Vsa.Machine Vsa.MemRepr Vsa.Alloc Vsa.Logic

/-- A completed strlen call, including the reached clock parity. -/
structure Returned (p r : BitVec 64) (len : Nat) (m0 : Mem) (c : Config) : Prop
    extends Done p r len m0 c where
  tick : c.tick < 2

/-- The tail loads only bytes from the final scanned word. -/
theorem tailLoad {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before) (k : Nat) (hk : k ≤ 7)
    (L : GRegs) (line : MInstr) (kind : line.kind = .lbu)
    (addr : (eaddrM line L).toNat = p.toNat + (off + 8*j) + k) :
    MemFacts before.σ.mem L [(m0[p.toNat + (off + 8*j) + k]?).getD 0] line := by
  obtain ⟨lo, hi, htif⟩ := tail_lbu_boundsG p len off j k h.regions h.jlo hk
  unfold MemFacts
  rw [kind]
  change (0x80000000 ≤ _ ∧ _ + 1 ≤ 0x100000000 ∧
    (_ + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ _)) ∧ _
  rw [addr]
  refine ⟨⟨lo, hi, htif⟩, ?_⟩
  change (before.σ.mem[p.toNat + (off + 8*j) + k]?).getD 0 = _
  rw [h.mem]
  rfl

/-- Address arithmetic for each byte load in the final word. -/
theorem tailAddress {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (k : Nat) (hk : k ≤ 7) (imm : BitVec 12)
    (himm : sign_extend (m := 64) imm = -(BitVec.ofNat 64 (8-k))) :
    ((p + BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) imm).toNat =
      p.toNat + (off + 8*j) + k := by
  rw [lbu_addrG p off j k (by omega) imm himm]
  rw [ptrN p (off + 8*j + k) (by
    have := h.regions.nowrap; have := h.jlo; omega)]
  omega

def tail0Seg : List BBlock := strlenX6d2cTSeg ++ strlenX6d9cSeg

/-- The actual byte-tail path for offset 0. -/
theorem tail0 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 0 = len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail0Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = true
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  have result : (BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xff8#12) = BitVec.ofNat 64 len :=
    exit_addi_valG off j len 0 0xff8#12 (by decide) last (by decide)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed tail0Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail0Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (((pos - p)) + sign_extend (m := 64) (0xff8#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, result, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc, a0 := ha0, ra := hra,
                  mem := C.mem.trans h.mem, tick := C.tick } }⟩

#print axioms tail0

def tail1Seg : List BBlock := strlenX6d2cFSeg ++ strlenX6d38TSeg ++ strlenX6d94Seg

/-- The actual byte-tail path for offset 1. -/
theorem tail1 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 1 = len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0], [byte 1]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail1Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = false
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 1 (by decide) _ _ rfl
      exact tailAddress h 1 (by decide) 0xff9#12 (by decide)
    · change ((zero_extend (m := 64) (byte 1)) == 0#64) = true
      rw [tdec_guardG p len off j 1 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  have result : (BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xff9#12) = BitVec.ofNat 64 len :=
    exit_addi_valG off j len 1 0xff9#12 (by decide) last (by decide)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed tail1Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail1Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (((pos - p)) + sign_extend (m := 64) (0xff9#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, result, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc, a0 := ha0, ra := hra,
                  mem := C.mem.trans h.mem, tick := C.tick } }⟩

#print axioms tail1

def tail2Seg : List BBlock := strlenX6d2cFSeg ++ strlenX6d38FSeg ++ strlenX6d40TSeg ++ strlenX6dacSeg

/-- The actual byte-tail path for offset 2. -/
theorem tail2 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 2 = len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0], [byte 1], [byte 2]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail2Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = false
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 1 (by decide) _ _ rfl
      exact tailAddress h 1 (by decide) 0xff9#12 (by decide)
    · change ((zero_extend (m := 64) (byte 1)) == 0#64) = false
      rw [tdec_guardG p len off j 1 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 2 (by decide) _ _ rfl
      exact tailAddress h 2 (by decide) 0xffa#12 (by decide)
    · change ((zero_extend (m := 64) (byte 2)) == 0#64) = true
      rw [tdec_guardG p len off j 2 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  have result : (BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xffa#12) = BitVec.ofNat 64 len :=
    exit_addi_valG off j len 2 0xffa#12 (by decide) last (by decide)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed tail2Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail2Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (((pos - p)) + sign_extend (m := 64) (0xffa#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, result, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc, a0 := ha0, ra := hra,
                  mem := C.mem.trans h.mem, tick := C.tick } }⟩

#print axioms tail2

def tail3Seg : List BBlock := strlenX6d2cFSeg ++ strlenX6d38FSeg ++ strlenX6d40FSeg ++ strlenX6d48TSeg ++ strlenX6da4Seg

/-- The actual byte-tail path for offset 3. -/
theorem tail3 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 3 = len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0], [byte 1], [byte 2], [byte 3]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail3Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = false
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 1 (by decide) _ _ rfl
      exact tailAddress h 1 (by decide) 0xff9#12 (by decide)
    · change ((zero_extend (m := 64) (byte 1)) == 0#64) = false
      rw [tdec_guardG p len off j 1 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 2 (by decide) _ _ rfl
      exact tailAddress h 2 (by decide) 0xffa#12 (by decide)
    · change ((zero_extend (m := 64) (byte 2)) == 0#64) = false
      rw [tdec_guardG p len off j 2 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 3 (by decide) _ _ rfl
      exact tailAddress h 3 (by decide) 0xffb#12 (by decide)
    · change ((zero_extend (m := 64) (byte 3)) == 0#64) = true
      rw [tdec_guardG p len off j 3 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  have result : (BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xffb#12) = BitVec.ofNat 64 len :=
    exit_addi_valG off j len 3 0xffb#12 (by decide) last (by decide)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed tail3Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail3Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (((pos - p)) + sign_extend (m := 64) (0xffb#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, result, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc, a0 := ha0, ra := hra,
                  mem := C.mem.trans h.mem, tick := C.tick } }⟩

#print axioms tail3

def tail4Seg : List BBlock := strlenX6d2cFSeg ++ strlenX6d38FSeg ++ strlenX6d40FSeg ++ strlenX6d48FSeg ++ strlenX6d50TSeg ++ strlenX6db4Seg

/-- The actual byte-tail path for offset 4. -/
theorem tail4 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 4 = len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0], [byte 1], [byte 2], [byte 3], [byte 4]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail4Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = false
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 1 (by decide) _ _ rfl
      exact tailAddress h 1 (by decide) 0xff9#12 (by decide)
    · change ((zero_extend (m := 64) (byte 1)) == 0#64) = false
      rw [tdec_guardG p len off j 1 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 2 (by decide) _ _ rfl
      exact tailAddress h 2 (by decide) 0xffa#12 (by decide)
    · change ((zero_extend (m := 64) (byte 2)) == 0#64) = false
      rw [tdec_guardG p len off j 2 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 3 (by decide) _ _ rfl
      exact tailAddress h 3 (by decide) 0xffb#12 (by decide)
    · change ((zero_extend (m := 64) (byte 3)) == 0#64) = false
      rw [tdec_guardG p len off j 3 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 4 (by decide) _ _ rfl
      exact tailAddress h 4 (by decide) 0xffc#12 (by decide)
    · change ((zero_extend (m := 64) (byte 4)) == 0#64) = true
      rw [tdec_guardG p len off j 4 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  have result : (BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xffc#12) = BitVec.ofNat 64 len :=
    exit_addi_valG off j len 4 0xffc#12 (by decide) last (by decide)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed tail4Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail4Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (((pos - p)) + sign_extend (m := 64) (0xffc#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, result, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc, a0 := ha0, ra := hra,
                  mem := C.mem.trans h.mem, tick := C.tick } }⟩

#print axioms tail4

def tail5Seg : List BBlock := strlenX6d2cFSeg ++ strlenX6d38FSeg ++ strlenX6d40FSeg ++ strlenX6d48FSeg ++ strlenX6d50FSeg ++ strlenX6d58TSeg ++ strlenX6dbcSeg

/-- The actual byte-tail path for offset 5. -/
theorem tail5 {p r : BitVec 64} {len off j : Nat} {cs : List Char} {m0 : Mem}
    {before : Config} (h : WTailG p r len cs m0 off j before)
    (last : off + 8*j + 5 = len) (retAlign : r.toNat % 4 = 0) :
    ∃ after, Steps before after ∧ Retained (Returned p r len m0) before after := by
  let pos := p + BitVec.ofNat 64 (off + 8*(j+1))
  let L : GRegs := [(14, pos), (10, p), (1, r)]
  let byte := fun n => (m0[p.toNat + (off + 8*j) + n]?).getD 0
  let bytes := [[byte 0], [byte 1], [byte 2], [byte 3], [byte 4], [byte 5]]
  have facts : ChainFacts before.σ.mem before.σ.mem L bytes tail5Seg := by
    chain_facts h.loaded with "Vsa.Sim.Code.strlen_at_"
    · apply tailLoad h 0 (by decide) _ _ rfl
      exact tailAddress h 0 (by decide) 0xff8#12 (by decide)
    · change ((zero_extend (m := 64) (byte 0)) == 0#64) = false
      rw [tdec_guardG p len off j 0 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 1 (by decide) _ _ rfl
      exact tailAddress h 1 (by decide) 0xff9#12 (by decide)
    · change ((zero_extend (m := 64) (byte 1)) == 0#64) = false
      rw [tdec_guardG p len off j 1 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 2 (by decide) _ _ rfl
      exact tailAddress h 2 (by decide) 0xffa#12 (by decide)
    · change ((zero_extend (m := 64) (byte 2)) == 0#64) = false
      rw [tdec_guardG p len off j 2 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 3 (by decide) _ _ rfl
      exact tailAddress h 3 (by decide) 0xffb#12 (by decide)
    · change ((zero_extend (m := 64) (byte 3)) == 0#64) = false
      rw [tdec_guardG p len off j 3 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 4 (by decide) _ _ rfl
      exact tailAddress h 4 (by decide) 0xffc#12 (by decide)
    · change ((zero_extend (m := 64) (byte 4)) == 0#64) = false
      rw [tdec_guardG p len off j 4 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_false_iff_not]
      omega
    · apply tailLoad h 5 (by decide) _ _ rfl
      exact tailAddress h 5 (by decide) 0xffd#12 (by decide)
    · change ((zero_extend (m := 64) (byte 5)) == 0#64) = true
      rw [tdec_guardG p len off j 5 cs m0 h.cstr h.hlen (by omega)]
      simp only [decide_eq_true_eq]
      omega
    · change (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1).toNat % 4 = 0
      rw [ret_tgt r retAlign]
      exact retAlign
  have result : (BitVec.ofNat 64 (off + 8*(j+1))) + sign_extend (m := 64) (0xffd#12) = BitVec.ofNat 64 len :=
    exit_addi_valG off j len 5 0xffd#12 (by decide) last (by decide)
  obtain ⟨vm, hvm⟩ := h.minstret
  obtain ⟨after, C⟩ := segEval_selected_framed tail5Seg L bytes 0x80006d2c#64 vm
    (fun _ => False) AbiPreserved [(10, BitVec.ofNat 64 len), (1, r)] before
    h.good h.pc hvm ⟨h.a4, h.a0, h.ra, trivial⟩
    (by change KeysOK [14, 10, 1]; decide) facts
    (by change ChainOK 0x80006d2c#64 [14, 10, 1] tail5Seg; decide) h.tick
    (by intro a _; rfl) (by decide) (by decide) (by
      change some (((pos - p)) + sign_extend (m := 64) (0xffd#12)) =
        some (BitVec.ofNat 64 len) ∧ some r = some r ∧ True
      simp only [pos, sub_a4_a0_val, result, and_self])
  obtain ⟨ha0, hra, _⟩ := C.selected_regs
  have pc : after.σ.regs.get? Register.PC = some r := by
    have pc := C.pc
    change after.σ.regs.get? Register.PC =
      some (BitVec.update (r + sign_extend (m := 64) (0#12)) 0 0#1) at pc
    rwa [ret_tgt r retAlign] at pc
  exact ⟨after, C.steps,
    { output := C.output, frame := C.reg_frame
      state := { good := C.good, pc := pc, a0 := ha0, ra := hra,
                  mem := C.mem.trans h.mem, tick := C.tick } }⟩

#print axioms tail5

end Vsa.Sim.StrlenRun
