import VsaIris.Vsa.Tools
import VsaIris.MachWP
import Vsa.Sim.HtifStepObs
import Vsa.Sim.TermEntry
import Vsa.Sim.DecodeTable.Batch14Part06
import Vsa.Sim.DecodeTable.Batch17

/-!
# The console on VSA's machine (INTERP_DESIGN.md §2, package F2)

The generic console rules are `MachWP.runOut` (print) and
`MachWP.haltConsole` (exit, with the output read off the console cell), in
`MachWP.lean`, for either WP. This file
instantiates both at VSA's HTIF `tohost` store.

An HTIF console store is one `sd rs2, imm(rs1)` whose effective address is
`tohost` (`0x8001ad00`). It is MMIO: memory is unchanged, and the Sail HTIF
registers decide the effect (`Vsa/Sim/Htif.lean`):

* the putchar word `0x0101…00 ||| c` appends the character `c` to
  `sailOutput` and the machine continues (`stepObs_tohost_putchar`);
* the exit word `(e <<< 1) ||| 1` sets `htif_done`, so the same `stepOnce`
  halts with code `e` and the output unchanged (`stepOnce_tohost_G`).

Both need the mailbox idle (`htif_payload_writes = 0`), which is
`VsaOk.htifIdle`. One descriptor `TohostSite` (the store's PC, bytes, decoded
fields and base register) with a decided `Cert` serves both. The newlib
instances are `_write`'s putchar store at `0x8000005c` and `_exit`'s store at
`0x80000190` (`experiments/disasm.txt`).
-/

namespace VsaIris.Inst

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1
open Vsa.Machine (Config Step MState output)
open Vsa.Sim

/-! ## Output and PC arithmetic -/

/-- Pushing a chunk onto `sailOutput` appends it to `output`. -/
theorem output_push {σ σ' : MState} {x : String} (h : σ'.sailOutput = σ.sailOutput.push x) :
    output σ' = output σ ++ x := by
  unfold output
  rw [h, Array.toList_push, String.join_append]
  simp

theorem addInt_ofNat_four (p : Nat) :
    BitVec.addInt (BitVec.ofNat 64 p) 4 = BitVec.ofNat 64 (p + 4) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.addInt, BitVec.toNat_add]

/-- The HTIF putchar command word for byte `c` (device 1, command 1). -/
abbrev putcWord (c : BitVec 8) : BitVec 64 := 0x0101000000000000#64 ||| BitVec.zeroExtend 64 c

/-- The HTIF exit command word for code `e`. -/
abbrev exitWord (e : BitVec 64) : BitVec 64 := (e <<< 1) ||| 1#64

/-- What one putchar store prints. -/
abbrev putcStr (c : BitVec 8) : String := toString (Char.ofNat c.toNat)

/-! ## The site descriptor -/

/-- A `sd rs2, imm(rs1)` store to `tohost`, as read off the disassembly. -/
structure TohostSite where
  pc : Nat
  b0 : BitVec 8
  b1 : BitVec 8
  b2 : BitVec 8
  b3 : BitVec 8
  w : BitVec 32
  imm : BitVec 12
  rs1 : Nat
  rs2 : Nat
  /-- The value of `rs1` the store uses (the `auipc` result). -/
  base : BitVec 64

namespace TohostSite

/-- The store's four code bytes. -/
abbrev code (S : TohostSite) : List (BitVec 8) := [S.b0, S.b1, S.b2, S.b3]

/-- The decided facts about a site: its bytes decode to the store, the store
addresses `tohost`, and the PC is aligned in RAM below `tohost`. -/
structure Cert (S : TohostSite) : Prop where
  word : ((S.b3.append S.b2).append S.b1).append S.b0 = S.w
  notrvc : Sail.BitVec.extractLsb (((S.b3.append S.b2).append S.b1).append S.b0) 1 0 =
    (0b11#2 : BitVec 2)
  dec : ∀ σ : MState,
    σ.regs.get? Register.misa = some ((initMisa) : RegisterType Register.misa) →
    σ.regs.get? Register.cur_privilege =
      some (Privilege.Machine : RegisterType Register.cur_privilege) →
    σ.regs.get? Register.mseccfg = some ((0#64) : RegisterType Register.mseccfg) →
    (ext_decode S.w).run σ = .ok (instruction.STORE (S.imm, gprIdx S.rs2, gprIdx S.rs1, 8)) σ
  addr : S.base + sign_extend (m := 64) S.imm = BitVec.ofNat 64 tohostAddr
  rs1 : 1 ≤ S.rs1 ∧ S.rs1 ≤ 31
  rs2 : 1 ≤ S.rs2 ∧ S.rs2 ≤ 31
  lo : 0x80000000 ≤ S.pc
  hi : S.pc + 4 ≤ tohostAddr
  align : S.pc % 4 = 0

/-- The registers a site reads: the base and the stored word. -/
abbrev regsRead (S : TohostSite) (q1 q2 : DFrac) (data : BitVec 64) :
    List (Nat × DFrac × BitVec 64) :=
  [(S.rs1, q1, S.base), (S.rs2, q2, data)]

/-- Everything the store's step lemmas consume, at a state holding the site's
footprint. -/
structure Pins (S : TohostSite) (data : BitVec 64) (σ : MState) : Prop where
  pc : σ.regs.get? Register.PC = some (BitVec.ofNat 64 S.pc)
  rs1 : (rX_bits (gprIdx S.rs1)).run (afterNextPC (afterPrelude σ) (BitVec.ofNat 64 S.pc)) =
    .ok S.base (afterNextPC (afterPrelude σ) (BitVec.ofNat 64 S.pc))
  rs2 : (rX_bits (gprIdx S.rs2)).run (afterNextPC (afterPrelude σ) (BitVec.ofNat 64 S.pc)) =
    .ok data (afterNextPC (afterPrelude σ) (BitVec.ofNat 64 S.pc))
  b0 : σ.mem[(BitVec.ofNat 64 S.pc).toNat]? = some S.b0
  b1 : σ.mem[(BitVec.ofNat 64 S.pc).toNat + 1]? = some S.b1
  b2 : σ.mem[(BitVec.ofNat 64 S.pc).toNat + 2]? = some S.b2
  b3 : σ.mem[(BitVec.ofNat 64 S.pc).toNat + 3]? = some S.b3
  lo : 0x80000000 ≤ (BitVec.ofNat 64 S.pc).toNat
  hi : (BitVec.ofNat 64 S.pc).toNat + 4 ≤ tohostAddr
  align : (BitVec.ofNat 64 S.pc).toNat % 4 = 0
  dec : (ext_decode S.w).run (afterPrelude σ) =
    .ok (instruction.STORE (S.imm, gprIdx S.rs2, gprIdx S.rs1, 8)) (afterPrelude σ)

theorem pc_toNat {S : TohostSite} (hS : S.Cert) : (BitVec.ofNat 64 S.pc).toNat = S.pc := by
  have := hS.hi
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by unfold tohostAddr at this; omega)

theorem rX_of_vsaReg {live : Nat → Prop} {c : Config} (hok : VsaOk live c) (pc : BitVec 64)
    {n : Nat} (hn : 1 ≤ n ∧ n ≤ 31) {v : BitVec 64} (h : vsaReg c n = v) :
    (rX_bits (gprIdx n)).run (afterNextPC (afterPrelude c.σ) pc) =
      .ok v (afterNextPC (afterPrelude c.σ) pc) := by
  have hg := gprGet_eq_of_vsaReg hok hn.1 hn.2 h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact rX_src c.σ pc (m + 1) hn.2 v hg

/-- The site's footprint gives every pin its step lemmas consume. `RR` may
list further registers (the exit rule's PC); `MR` must contain the code. -/
theorem pins {live : Nat → Prop} {S : TohostSite} (hS : S.Cert) {data : BitVec 64}
    {c : Config} (hok : VsaOk live c) (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1)
    (hpc : pcVal c.σ = BitVec.ofNat 64 S.pc)
    (hr1 : vsaReg c S.rs1 = S.base) (hr2 : vsaReg c S.rs2 = data)
    (hmr : ∀ p ∈ codeFoot S.pc S.code, (vsaModel live).mem c p.1 = p.2.2) :
    Pins S data c.σ := by
  have hcode := code_present hok _ hmr hlive
  have e := pc_toNat hS
  have hb : ∀ k (b : BitVec 8), (S.pc + k, DFrac.discard, b) ∈ codeFoot S.pc S.code →
      c.σ.mem[(BitVec.ofNat 64 S.pc).toNat + k]? = some b := fun k b hm => by
    rw [e]; exact hcode _ hm
  obtain ⟨v, hv⟩ := hok.good.PC
  refine ⟨?_, rX_of_vsaReg hok _ hS.rs1 hr1, rX_of_vsaReg hok _ hS.rs2 hr2,
    hb 0 S.b0 (by simp [codeFoot]), hb 1 S.b1 (by simp [codeFoot]),
    hb 2 S.b2 (by simp [codeFoot]), hb 3 S.b3 (by simp [codeFoot]),
    by rw [e]; exact hS.lo, by rw [e]; exact hS.hi, by rw [e]; exact hS.align,
    hS.dec _ (by rw [get?_afterPrelude _ _ (by decide)]; exact hok.good.misa)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact hok.good.cur_privilege)
      (by rw [get?_afterPrelude _ _ (by decide)]; exact hok.good.mseccfg)⟩
  · unfold pcVal at hpc
    rw [hv] at hpc ⊢
    exact congrArg some hpc

end TohostSite

/-! ## The putchar store prints one character -/

/-- GPRs through the putchar step's register frame. -/
theorem gprGet_of_putcFrame {σ' σ : MState}
    (hframe : ∀ R : Register,
      (Register.PC == R) = false → (Register.minstret == R) = false →
      (Register.minstret_increment == R) = false → (Register.nextPC == R) = false →
      (Register.htif_cmd_write == R) = false → (Register.htif_payload_writes == R) = false →
      (Register.htif_tohost == R) = false →
      (Register.mip == R) = false → (Register.mtime == R) = false →
      (Register.mcycle == R) = false →
      σ'.regs.get? R = σ.regs.get? R) (n : Nat) :
    gprGet σ' n = gprGet σ n := by
  unfold gprGet
  split <;> first
    | rfl
    | exact hframe _ (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- **The putchar store as a printing run.** From the site's footprint (the
PC, the base register, the putchar word for `c` in `rs2`, the code bytes),
one step advances the PC by 4, changes no other owned cell, and prints
`c`. -/
theorem putc_runFact (live : Nat → Prop) (S : TohostSite) (hS : S.Cert) (c : BitVec 8)
    (q1 q2 : DFrac) (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    RunFactO (vsaModel live) 0 (S.regsRead q1 q2 (putcWord c)) (codeFoot S.pc S.code)
      [(VsaIris.PC, BitVec.ofNat 64 S.pc, BitVec.ofNat 64 (S.pc + 4))] []
      (some (putcStr c)) := by
  intro cfg hok hfoot
  have hok : VsaOk live cfg := hok
  obtain ⟨hRR, hMR, hRW, _⟩ := hfoot
  have hP := TohostSite.pins hS hok hlive (hRW _ List.mem_cons_self)
    (hRR _ List.mem_cons_self) (hRR _ (.tail _ List.mem_cons_self)) hMR
  obtain ⟨vm, hvm⟩ := hok.good.minstret
  obtain ⟨th, hth⟩ := hok.good.htif_tohost
  obtain ⟨σ', i', hstep, hi', hG', hmem', hout', hpc', _, hpw', _, hframe⟩ :=
    stepObs_tohost_putchar cfg.σ cfg.tick cfg.steps (BitVec.ofNat 64 S.pc) vm S.w S.imm
      (gprIdx S.rs2) (gprIdx S.rs1) S.base (putcWord c) (putcWord c) c th
      S.b0 S.b1 S.b2 S.b3 hok.good hP.pc hvm hS.word hS.notrvc hP.dec hP.rs1 hP.rs2 hS.addr
      rfl hok.htifIdle hth rfl hP.b0 hP.b1 hP.b2 hP.b3 hP.lo hP.hi hP.align hok.tick
  have hgpr := gprGet_of_putcFrame hframe
  refine ⟨⟨σ', i', cfg.steps + 1⟩, .succ (vsaStep_of_step hstep) (.zero _),
    ⟨hG', hi', fun n h1 h31 => by rw [hgpr n]; exact hok.gpr n h1 h31,
      fun a ha => by change (σ'.mem[a]?).isSome; rw [hmem']; exact hok.live a ha, hpw'⟩,
    ?_, output_push hout'⟩
  constructor
  · intro p hp
    rcases List.mem_singleton.mp hp with rfl
    change pcVal σ' = _
    unfold pcVal
    rw [hpc', addInt_ofNat_four]
    rfl
  · intro k hk
    have hkpc : k ≠ VsaIris.PC := fun e => hk _ List.mem_cons_self e.symm
    change vsaReg _ k = vsaReg cfg k
    rw [vsaReg_gpr hkpc, vsaReg_gpr (c := cfg) hkpc, hgpr k]
  · intro p hp; cases hp
  · intro a _
    change (σ'.mem[a]?).getD 0 = (cfg.σ.mem[a]?).getD 0
    rw [hmem']

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

/-- **The putchar rule on VSA**, for either WP. Owning the PC at the site,
the base and putchar word, the code and the console cell `s`, the store
prints `c`: the continuation gets the PC past the store and the console at
`s ++ c`. -/
theorem wp_putcW (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (S : TohostSite) (hS : S.Cert) (c : BitVec 8) (q1 q2 : DFrac) (s : String)
    (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    instrAt (GF := GF) S.pc S.code ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 S.pc ∗
      S.rs1 ↦ᵣ{q1} S.base ∗ S.rs2 ↦ᵣ{q2} putcWord c ∗ consoleOwn s ∗
      (VsaIris.PC ↦ᵣ BitVec.ofNat 64 (S.pc + 4) -∗ S.rs1 ↦ᵣ{q1} S.base -∗
        S.rs2 ↦ᵣ{q2} putcWord c -∗ consoleOwn (s ++ putcStr c) -∗ Wp.W Φ)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, Hpc, H1, H2, Hs, Hk⟩
  iapply Wp.runOut 0 _ _ _ _ (putcStr c) s (putc_runFact live S hS c q1 q2 hlive)
  unfold footPre footPost
  rw [← instrAt_eq]
  simp only [sepL_cons, sepL_nil]
  iframe Hi Hs H1 H2 Hpc
  iintro ⟨⟨H1, H2, -⟩, -, ⟨Hpc, -⟩, -⟩ Hs
  iapply Hk $$ Hpc H1 H2 Hs

/-- The putchar rule for the total WP. -/
theorem wp_putc {Φ : Nat × String → IProp GF} (S : TohostSite) (hS : S.Cert) (c : BitVec 8)
    (q1 q2 : DFrac) (s : String) (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    instrAt (GF := GF) S.pc S.code ∗ VsaIris.PC ↦ᵣ BitVec.ofNat 64 S.pc ∗
      S.rs1 ↦ᵣ{q1} S.base ∗ S.rs2 ↦ᵣ{q2} putcWord c ∗ consoleOwn s ∗
      (VsaIris.PC ↦ᵣ BitVec.ofNat 64 (S.pc + 4) -∗ S.rs1 ↦ᵣ{q1} S.base -∗
        S.rs2 ↦ᵣ{q2} putcWord c -∗ consoleOwn (s ++ putcStr c) -∗ mTWP (vsaModel live) Φ)
    ⊢ mTWP (vsaModel live) Φ :=
  wp_putcW (twpW (vsaModel live)) S hS c q1 q2 s hlive

end Wp

/-! ## The exit store halts, reporting the console -/

/-- **The exit store as a halt.** From the site's footprint with the exit
word for `e` in `rs2`, the machine's next step is the HTIF exit with code
`e`, and the exit reports the output so far (the store prints nothing). -/
theorem exit_haltFact (live : Nat → Prop) (S : TohostSite) (hS : S.Cert) (e : BitVec 64)
    (he : e.toNat < 2 ^ 47) (q0 q1 q2 : DFrac) (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    HaltFact (vsaModel live) ((VsaIris.PC, q0, BitVec.ofNat 64 S.pc) :: S.regsRead q1 q2 (exitWord e))
      (codeFoot S.pc S.code) e.toNat := by
  intro cfg hok hfoot
  have hok : VsaOk live cfg := hok
  obtain ⟨hRR, hMR, _, _⟩ := hfoot
  have hP := TohostSite.pins hS hok hlive (hRR _ List.mem_cons_self)
    (hRR _ (.tail _ List.mem_cons_self)) (hRR _ (.tail _ (.tail _ List.mem_cons_self))) hMR
  obtain ⟨vm, hvm⟩ := hok.good.minstret
  obtain ⟨th, hth⟩ := hok.good.htif_tohost
  have hstep := stepOnce_tohost_G cfg.σ cfg.tick cfg.steps (BitVec.ofNat 64 S.pc) vm S.w S.imm
    (gprIdx S.rs2) (gprIdx S.rs1) S.base (exitWord e) (exitWord e) e th S.b0 S.b1 S.b2 S.b3
    hok.good hP.pc hvm hS.word hS.notrvc hP.dec hP.rs1 hP.rs2 hS.addr rfl hok.htifIdle hth he rfl
    hP.b0 hP.b1 hP.b2 hP.b3 hP.lo hP.hi hP.align
  change vsaStep cfg = .halt e.toNat (output cfg.σ)
  unfold vsaStep
  rw [hstep]
  rfl

section Wp

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {live : Nat → Prop}

/-- **Halt/console agreement on VSA**, for either WP. At the exit store with
the console cell `s`, the loop's WP holds as soon as the postcondition holds
at `(e, s)`: the halting step reports exactly the console's contents. With
adequacy this is `Halts c s e`. -/
theorem wp_exitW (Wp : MachWP (GF := GF) (vsaModel live)) {Φ : Nat × String → IProp GF}
    (S : TohostSite) (hS : S.Cert) (e : BitVec 64) (he : e.toNat < 2 ^ 47) (q0 q1 q2 : DFrac)
    (s : String) (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    instrAt (GF := GF) S.pc S.code ∗ VsaIris.PC ↦ᵣ{q0} BitVec.ofNat 64 S.pc ∗
      S.rs1 ↦ᵣ{q1} S.base ∗ S.rs2 ↦ᵣ{q2} exitWord e ∗ consoleOwn s ∗ Φ (e.toNat, s)
    ⊢ Wp.W Φ := by
  iintro ⟨#Hi, Hpc, H1, H2, Hs, HΦ⟩
  iapply Wp.haltConsole _ _ e.toNat s (exit_haltFact live S hS e he q0 q1 q2 hlive)
  unfold footPre
  rw [← instrAt_eq]
  simp only [sepL_cons, sepL_nil]
  iframe Hi Hs HΦ
  isplitl [Hpc H1 H2]
  · iframe Hpc H1 H2
  isplitr
  · iempintro
  iempintro

/-- Halt/console agreement for the total WP. -/
theorem wp_exit {Φ : Nat × String → IProp GF} (S : TohostSite) (hS : S.Cert) (e : BitVec 64)
    (he : e.toNat < 2 ^ 47) (q0 q1 q2 : DFrac) (s : String)
    (hlive : ∀ p ∈ codeFoot S.pc S.code, live p.1) :
    instrAt (GF := GF) S.pc S.code ∗ VsaIris.PC ↦ᵣ{q0} BitVec.ofNat 64 S.pc ∗
      S.rs1 ↦ᵣ{q1} S.base ∗ S.rs2 ↦ᵣ{q2} exitWord e ∗ consoleOwn s ∗ Φ (e.toNat, s)
    ⊢ mTWP (vsaModel live) Φ :=
  wp_exitW (twpW (vsaModel live)) S hS e he q0 q1 q2 s hlive

end Wp

/-! ## From the exit to `Halts` -/

/-- **Adequacy with any exit condition.** If, from the initial ownership and
the console cell at the initial output, the loop's total WP holds with a pure
postcondition `φ`, VSA's machine halts with some code `e` and output `out`
satisfying `φ`. The exit rule (`wp_exit`) supplies `φ` at `(e, s)` with `s`
the console cell, so the halting output is read from the ghost. -/
theorem vsa_adequacy_exit {GF : BundledGFunctors} [MachGpreS GF] (live : Nat → Prop)
    (c : Config) (mr : NatMap (BitVec 64)) (mm : NatMap (BitVec 8))
    (hr : RegAgree (vsaModel live) mr c) (hm : MemAgree (vsaModel live) mm c)
    (hok : VsaOk live c) (φ : Nat × String → Prop)
    (H : AdequacyHyp GF (vsaModel live) mr mm (output c.σ) φ) :
    ∃ e out, Vsa.Machine.Halts c out e ∧ φ (e, out) := by
  obtain ⟨e, out, ⟨cf, hre, hh⟩, hφ⟩ :=
    mach_adequacy (GF := GF) (M := vsaModel live) c mr mm hr hm hok _ H
  obtain ⟨σf, hhalt, hout⟩ := vsaStep_halt hh
  exact ⟨e, out, ⟨cf, σf, steps_of_reaches hre, hhalt, hout⟩, hφ⟩

/-! ## The newlib sites -/

/-- `_write`'s console store, `0x8000005c: sd a5,-856(a6)`, with
`a6 = 0x8001b058` from the `auipc` before it. -/
def putcSite : TohostSite where
  pc := 0x8000005c
  b0 := 0x23#8
  b1 := 0x34#8
  b2 := 0xf8#8
  b3 := 0xca#8
  w := 0xcaf83423#32
  imm := 0xca8#12
  rs1 := 16
  rs2 := 15
  base := 0x8001b058#64

theorem putcSite_cert : putcSite.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => DecodeTable.decode_caf83423 σ h1 h2 h3
  addr := by decide
  rs1 := by decide
  rs2 := by decide
  lo := by decide
  hi := by decide
  align := by decide

/-- `_exit`'s store, `0x80000190: sd a5,-1164(a4)`, with `a4 = 0x8001b18c`
from the `auipc` before it. -/
def exitSite : TohostSite where
  pc := 0x80000190
  b0 := 0x23#8
  b1 := 0x3a#8
  b2 := 0xf7#8
  b3 := 0xb6#8
  w := 0xb6f73a23#32
  imm := 0xb74#12
  rs1 := 14
  rs2 := 15
  base := 0x8001b18c#64

theorem exitSite_cert : exitSite.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => DecodeTable.decode_b6f73a23 σ h1 h2 h3
  addr := by decide
  rs1 := by decide
  rs2 := by decide
  lo := by decide
  hi := by decide
  align := by decide

end VsaIris.Inst
