import Vsa.Sim.rows.EnvDefineScanRows
import Vsa.Sim.BridgeSegFull
import Vsa.Sim.BridgeSegFramed

/-!
# `EnvDefineScanCallOut` — the scan's argument loads and `jal strcmp`, with output

`envDefineScanCallRead64` (`EnvDefineScanRows.lean`) runs the two argument loads
at `0x80002ab0` and the `jal strcmp` at `0x80002ab8` but exports no
`sailOutput` clause, so the framed scan (`EnvDefineScanFramed.lean`) could not
carry the console output past the `strcmp` seam.  This file lands the same run
through `bridgeOfSegFull` (`BridgeSegFull.lean`), whose `SegCallFacts.output`
keeps the output, as the named-field carrier `EnvDefineScanCallOut`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (MState Config Step Steps)

namespace Vsa.Sim

/-- The state parked at `strcmp`'s entry after the scan's argument loads: the
loaded name pointer in `a0`, the queried name in `a1`, the link at the branch,
the ABI frame and the console output unchanged. -/
structure EnvDefineScanCallOut (cursor name : BitVec 64) (q : Nat) (c c' : Config) : Prop where
  steps : Steps c c'
  good : GoodState c'.σ
  tick : c'.tick < 2
  mem : c'.σ.mem = c.σ.mem
  pc : c'.σ.regs.get? Register.PC = some 0x80006ea0#64
  ra : c'.σ.regs.get? Register.x1 = some 0x80002abc#64
  a0 : c'.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 q)
  a1 : c'.σ.regs.get? Register.x11 = some name
  minstret : ∃ w, c'.σ.regs.get? Register.minstret = some w
  abi : ∀ R, Vsa.Alloc.AbiPreserved R = true → c'.σ.regs.get? R = c.σ.regs.get? R
  out : c'.σ.sailOutput = c.σ.sailOutput

/-- The `x1`-avoiding register frame of the scan call seg. -/
private theorem scanCallFrame {σ' σ : MState}
    (hframe : ∀ R, (∀ r ∈ noiseRegs, (r == R) = false) →
      (∀ n ∈ wrChain envDefineScanCallSeg, (gprReg n == R) = false) →
      (Register.x1 == R) = false → σ'.regs.get? R = σ.regs.get? R) :
    ∀ R, Vsa.Alloc.AbiPreserved R = true → σ'.regs.get? R = σ.regs.get? R := by
  intro R hR
  exact hframe R (noise_avoids abiPreserved_noise hR)
    (wrChain_avoids (by show WrChainAvoids Vsa.Alloc.AbiPreserved envDefineScanCallSeg; decide) hR)
    (regAvoids_ne hR (by decide))

/-- `envDefineScanCallRead64` with the console output retained. -/
theorem envDefineScanCallRead64Out
    (cursor name : BitVec 64) (q : Nat) (c : Config)
    (hG : GoodState c.σ)
    (hpc : c.σ.regs.get? Register.PC = some 0x80002ab0#64)
    (hcursor : c.σ.regs.get? Register.x9 = some cursor)
    (hname : c.σ.regs.get? Register.x18 = some name)
    (hread : Vsa.MemRepr.read64 c.σ.mem cursor.toNat = some q)
    (hlo : 0x80000000 ≤ cursor.toNat)
    (hhi : cursor.toNat + 8 ≤ 0x100000000)
    (hhtif : cursor.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ cursor.toNat)
    (_halign : cursor.toNat % 8 = 0)
    (hloaded : Vsa.Sim.Code.Env_defineLoaded c.σ.mem)
    (htick : c.tick < 2) :
    ∃ c', EnvDefineScanCallOut cursor name q c c' := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7,
      hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7, _⟩ :=
    read64_bytes_eg4 c.σ.mem cursor.toNat q hread
  let bs := [b0, b1, b2, b3, b4, b5, b6, b7]
  have hpins : LPins8 c.σ.mem cursor.toNat bs := by
    simp [LPins8, bs, hb0, hb1, hb2, hb3, hb4, hb5, hb6, hb7]
  have hea : eaddrM (mkLine 0x80002ab0#64 0x0004b503#32)
      (envDefineScanCallL cursor name) = cursor := by
    change cursor + sign_extend (m := 64) (0#12) = cursor
    rw [sext_zero, BitVec.add_zero]
  have hfacts : ChainFacts c.σ.mem c.σ.mem
      (envDefineScanCallL cursor name) [bs] envDefineScanCallSeg := by
    chain_facts hloaded with "Vsa.Sim.Code.env_define_at_"
    unfold MemFacts
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hea]; exact hlo
    · rw [hea]; exact hhi
    · rw [hea]; exact hhtif
    · rw [hea]; exact hpins
  have hL : GHolds c.σ (envDefineScanCallL cursor name) := by
    exact ⟨by simpa [gprGet] using hcursor,
      by simpa [gprGet] using hname, trivial⟩
  have hmemLog : writeLog c.σ.mem (evalBlocks envDefineScanCallSeg
      (SegEvalState.init (envDefineScanCallL cursor name) [bs])).log = c.σ.mem := by
    rfl
  have hval : (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8)) : BitVec 64) = BitVec.ofNat 64 q :=
    ld_value_eq_read64 c.σ.mem cursor.toNat q b0 b1 b2 b3 b4 b5 b6 b7 hread
      hb0 hb1 hb2 hb3 hb4 hb5 hb6 hb7
  obtain ⟨after, S⟩ := bridgeOfSegFull envDefineScanCallSeg (envDefineScanCallL cursor name) [bs]
    0x80002ab0#64 0x80006ea0#64 0x80002abc#64 c hG hpc hG.minstret htick hL
    (by show KeysOK [9, 18]; decide) hfacts
    (by show ChainOK 0x80002ab0#64 [9, 18] envDefineScanCallSeg; decide)
    (by show KeysOK [11, 10, 9, 18]; decide)
    (by
      have h : keysG (evalBlocks envDefineScanCallSeg
        (SegEvalState.init (envDefineScanCallL cursor name) [bs])).regs =
          [11, 10, 9, 18] := rfl
      show ∀ n ∈ keysG _, n ≠ 1
      rw [h]
      decide)
    (by
      intro middle hGm htm hpcm hmim hmemm _
      obtain ⟨σ', i', u'⟩ := middle
      obtain ⟨vm', hmi'v⟩ := hmim
      have hpcE : evalBlocksPC 0x80002ab0#64
          (SegEvalState.init (envDefineScanCallL cursor name) [bs])
          envDefineScanCallSeg = 0x80002ab8#64 := by rfl
      have hloaded' : Vsa.Sim.Code.Env_defineLoaded σ'.mem := by
        show Vsa.Sim.Code.Env_defineLoaded (⟨σ', i', u'⟩ : Config).σ.mem
        rw [hmemm, hmemLog]
        exact hloaded
      obtain ⟨σ2, i2, hstep, hi2, hG2, hmem2, hobs⟩ :=
        site_80002ab8_ed σ' i' u' 0x80002ab8#64 vm' hGm (hpcE ▸ hpcm) hmi'v hloaded' rfl
          (by decide) htm
      have hlink : BitVec.addInt 0x80002ab8#64 4 = (0x80002abc#64 : BitVec 64) := by
        apply BitVec.eq_of_toNat_eq; decide
      rw [hlink] at hobs
      exact ⟨⟨σ2, i2, u' + 1⟩, jalCallFacts_of_obs hstep hi2 hG2 hmem2 hobs
        (by apply BitVec.eq_of_toNat_eq; decide)⟩)
  have hx10 : gprGet after.σ 10 = some (BitVec.ofNat 64 q) := by
    apply gholds_lookup _ S.registers
    change some (sign_extend (m := 64)
      ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
        : BitVec (8 * 8))) = some (BitVec.ofNat 64 q)
    rw [hval]
  have hx11 : gprGet after.σ 11 = some name := by
    apply gholds_lookup _ S.registers
    change some (name + sign_extend (m := 64) (0#12)) = some name
    rw [sext_zero, BitVec.add_zero]
  refine ⟨after, S.run, S.good, S.tick, S.mem.trans hmemLog, S.pc, S.ra, ?_, ?_, S.minstret,
    scanCallFrame S.frame, S.output⟩
  · simpa [gprGet] using hx10
  · simpa [gprGet] using hx11

#print axioms envDefineScanCallRead64Out

end Vsa.Sim
