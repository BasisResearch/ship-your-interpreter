import Vsa.Sim.rows.EnvDefineMissHead

/-!
# `EnvDefineEmptyLane` — the empty frame: entry to the `env_define` return

On a frame with no binding (`count = 0`) the helper takes `blez s3` at
`0x80002a90` to the CAP-INIT block `0x80002bf4`: `lw a5,4(a0)`; `bne a5,s3`
(`cap ≠ 0`: the append head `0x80002b1c`); `ld s6,8(a0)`; `bnez a5`
(unreachable: `a5 = s3 = 0`); `li a1,64`; `li a5,8`; `j 0x80002b98` (the grow
lane's `realloc(NULL,64)`/`realloc(NULL,192)` entry, `EnvDefineGrowKind.init`).

The block is decoded as three `#derive_case` segs.  `envDefineEmptyLane`
runs the framed prologue (`envDefinePrologueExit`), the reachable route as a
`segRowKeepGhost` row (the ABI frame but `s6` kept), and then
`envDefineAppendLane` (`cap ≠ 0`) or `envDefineGrowEntry_run` (`cap = 0`).
`envDefineCapInitGrow_unreachable` proves the `bnez` route's chain facts
contradictory at `s3 = 0`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`; no Mathlib.
-/

namespace Vsa.Sim

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Register
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic (Triple)
open Vsa.RuntimeRepr Vsa.MemRepr Vsa.While Vsa.Alloc
open Vsa.Sim.Code

/-! ## 1. The empty-frame arm (CAP-INIT), decoded

`0x80002a90 blez s3,0x80002bf4` (taken: `count = 0`), then
`0x80002bf4 lw a5,4(a0)`; `0x80002bf8 bne a5,s3,0x80002b1c` (`cap ≠ 0`: the
append head); `0x80002bfc ld s6,8(a0)`; `0x80002c00 bnez a5,0x80002b90`
(unreachable after the `bne`: `a5 = s3 = 0`); `0x80002c04 li a1,64`;
`0x80002c08 li a5,8`; `0x80002c0c j 0x80002b98` (`cap := 8`, then
`realloc(NULL,64)` and `realloc(NULL,192)` in the grow lane's second half). -/

#derive_case envDefineCapInitAppendSeg chain
  [] terminator ⟨0x80002a90#64, 0x17305263#32,
    0x63#8, 0x52#8, 0x30#8, 0x17#8,
    .br bop.BGE true, 0, 19, 0x0164#13, 0#21, 0#12⟩ ;;
  [(0x80002bf4#64, 0x00452783#32)]
  terminator ⟨0x80002bf8#64, 0xf33792e3#32,
    0xe3#8, 0x92#8, 0x37#8, 0xf3#8,
    .br bop.BNE true, 15, 19, 0x1f24#13, 0#21, 0#12⟩

#derive_case envDefineCapInitGrowSeg chain
  [] terminator ⟨0x80002a90#64, 0x17305263#32,
    0x63#8, 0x52#8, 0x30#8, 0x17#8,
    .br bop.BGE true, 0, 19, 0x0164#13, 0#21, 0#12⟩ ;;
  [(0x80002bf4#64, 0x00452783#32)]
  terminator ⟨0x80002bf8#64, 0xf33792e3#32,
    0xe3#8, 0x92#8, 0x37#8, 0xf3#8,
    .br bop.BNE false, 15, 19, 0x1f24#13, 0#21, 0#12⟩ ;;
  [(0x80002bfc#64, 0x00853b03#32)]
  terminator ⟨0x80002c00#64, 0xf80798e3#32,
    0xe3#8, 0x98#8, 0x07#8, 0xf8#8,
    .br bop.BNE true, 15, 0, 0x1f90#13, 0#21, 0#12⟩

#derive_case envDefineCapInitZeroSeg chain
  [] terminator ⟨0x80002a90#64, 0x17305263#32,
    0x63#8, 0x52#8, 0x30#8, 0x17#8,
    .br bop.BGE true, 0, 19, 0x0164#13, 0#21, 0#12⟩ ;;
  [(0x80002bf4#64, 0x00452783#32)]
  terminator ⟨0x80002bf8#64, 0xf33792e3#32,
    0xe3#8, 0x92#8, 0x37#8, 0xf3#8,
    .br bop.BNE false, 15, 19, 0x1f24#13, 0#21, 0#12⟩ ;;
  [(0x80002bfc#64, 0x00853b03#32)]
  terminator ⟨0x80002c00#64, 0xf80798e3#32,
    0xe3#8, 0x98#8, 0x07#8, 0xf8#8,
    .br bop.BNE false, 15, 0, 0x1f90#13, 0#21, 0#12⟩ ;;
  [(0x80002c04#64, 0x04000593#32),
   (0x80002c08#64, 0x00800793#32)]
  terminator ⟨0x80002c0c#64, 0xf8dff06f#32,
    0x6f#8, 0xf0#8, 0xdf#8, 0xf8#8,
    .j, 0, 0, 0#13, 0x1fff8c#21, 0#12⟩

/-- The CAP-INIT arm's pins: the count in `s3`, the environment in `a0`. -/
def envDefineCapInitL (env count : BitVec 64) : GRegs := [(19, count), (10, env)]

/-- The reflected endpoint of a CAP-INIT route (loads only: memory unchanged). -/
def EnvDefineCapInitPost (seg : List BBlock) (pc env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some pc ∧
  GHolds c.σ (evalBlocks seg (SegEvalState.init (envDefineCapInitL env count) lds)).regs ∧
  c.tick < 2

theorem envDefineCapInitAppendRow (env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple (SegPre envDefineCapInitAppendSeg (envDefineCapInitL env count) lds 0x80002a90#64 m0)
      (EnvDefineCapInitPost envDefineCapInitAppendSeg 0x80002b1c#64 env count lds m0) := by
  apply segToTriple envDefineCapInitAppendSeg (envDefineCapInitL env count) lds 0x80002a90#64 m0 _
    (by show ChainOK 0x80002a90#64 [19, 10] envDefineCapInitAppendSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa [envDefineCapInitAppendSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  · rw [hpc']; rfl

theorem envDefineCapInitGrowRow (env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple (SegPre envDefineCapInitGrowSeg (envDefineCapInitL env count) lds 0x80002a90#64 m0)
      (EnvDefineCapInitPost envDefineCapInitGrowSeg 0x80002b90#64 env count lds m0) := by
  apply segToTriple envDefineCapInitGrowSeg (envDefineCapInitL env count) lds 0x80002a90#64 m0 _
    (by show ChainOK 0x80002a90#64 [19, 10] envDefineCapInitGrowSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa [envDefineCapInitGrowSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  · rw [hpc']; rfl

theorem envDefineCapInitZeroRow (env count : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple (SegPre envDefineCapInitZeroSeg (envDefineCapInitL env count) lds 0x80002a90#64 m0)
      (EnvDefineCapInitPost envDefineCapInitZeroSeg 0x80002b98#64 env count lds m0) := by
  apply segToTriple envDefineCapInitZeroSeg (envDefineCapInitL env count) lds 0x80002a90#64 m0 _
    (by show ChainOK 0x80002a90#64 [19, 10] envDefineCapInitZeroSeg; decide)
  intro σ' i' u' hG' hi' hmem' hpc' _hmi' hregs'
  refine ⟨hG', ?_, ?_, hregs', hi'⟩
  · simpa [envDefineCapInitZeroSeg, evalBlocks, SegEvalState.init, writeLog] using hmem'
  · rw [hpc']; rfl

#print axioms envDefineCapInitAppendRow
#print axioms envDefineCapInitGrowRow
#print axioms envDefineCapInitZeroRow


/-! ## 2. The reflected lines and the frame the block keeps -/

private theorem capInitLwLine :
    mkLine 0x80002bf4#64 0x00452783#32 =
      ⟨0x80002bf4#64, 0x00452783#32, 0x83#8, 0x27#8, 0x45#8, 0x00#8,
        .lw, 15, 10, 0, 0x004#12⟩ := by rfl

private theorem capInitLdLine :
    mkLine 0x80002bfc#64 0x00853b03#32 =
      ⟨0x80002bfc#64, 0x00853b03#32, 0x03#8, 0x3b#8, 0x85#8, 0x00#8,
        .ld, 22, 10, 0, 0x008#12⟩ := by rfl

private theorem capInitLiA1Line :
    mkLine 0x80002c04#64 0x04000593#32 =
      ⟨0x80002c04#64, 0x04000593#32, 0x93#8, 0x05#8, 0x00#8, 0x04#8,
        .addi, 11, 0, 0, 0x040#12⟩ := by rfl

private theorem capInitLiA5Line :
    mkLine 0x80002c08#64 0x00800793#32 =
      ⟨0x80002c08#64, 0x00800793#32, 0x93#8, 0x07#8, 0x80#8, 0x00#8,
        .addi, 15, 0, 0, 0x008#12⟩ := by rfl

private theorem sext64_bv : (sign_extend (m := 64) (0x040#12) : BitVec 64) = 64#64 := by decide
private theorem sext8_bv : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by decide

/-- The ABI frame but `s6` (the CAP-INIT block's `ld s6,8(a0)`). -/
def KeepButS6 (R : Register) : Bool := AbiPreserved R && !(R == Register.x22)

theorem KeepButS6.of {R : Register} (hA : AbiPreserved R = true) (h22 : R ≠ Register.x22) :
    KeepButS6 R = true := by
  simp [KeepButS6, hA, h22]

/-! ## 3. The `bnez` route is unreachable -/

/-- At `s3 = 0` the fall-through `bne a5,s3` pins `a5 = 0`, so the `bnez a5`
guard of the grow route is false: its chain facts are contradictory. -/
theorem envDefineCapInitGrow_unreachable (m m' : Mem) (env : BitVec 64)
    (lds : List (List (BitVec 8)))
    (h : ChainFacts m m' (envDefineCapInitL env 0#64) lds envDefineCapInitGrowSeg) : False := by
  obtain ⟨_, ⟨_, _, ht2⟩, ⟨_, _, ht3⟩, _⟩ := h
  simp only [runGM, TermFactsO, TermFactsT] at ht2 ht3
  rw [capInitLwLine] at ht2 ht3
  rw [capInitLdLine] at ht3
  simp only [runGM, stepGM, stepLdsM, ldsRunM, wvalM] at ht2 ht3
  simp [guardB, srcVal, lookupG, eraseG, envDefineCapInitL] at ht2 ht3
  rw [ht2] at ht3
  exact absurd ht3 (by decide)

/-! ## 4. The empty-frame lane -/

/-- The machine side at the CAP-INIT block's exit from the prologue exit and
a `KeepButS6` row: the seg keeps every ABI register but `s6`, leaves memory
and output unchanged. -/
theorem envDefineEmptyRegs
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (v8 v9 v18 v19 v20 v21 v22 : BitVec 64) (pn : Nat) (c1 c2 : Config)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (Q : EnvDefinePrologueExit g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
      v8 v9 v18 v19 v20 v21 v22 pn c1)
    (hG : GoodState c2.σ) (htick : c2.tick < 2)
    (hmem : c2.σ.mem = envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
    (hmi : ∃ w, c2.σ.regs.get? Register.minstret = some w)
    (hkeep : ∀ R, KeepButS6 R = true → c2.σ.regs.get? R = c1.σ.regs.get? R)
    (hout : c2.σ.sailOutput = out) :
    EnvDefineMissRegs g A SL st env esp aEnv aName pv r out M exts
      (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) Q.facts.env_lt c2 := by
  have P := Q.post
  have hsp1 := hE.stack.1
  have hsp2 := hE.stack.2.1
  have hsp3 := hE.stack.2.2
  have hhr := L.headroom_le
  have hsp64 : (esp - 64#64).toNat = esp.toNat - 64 := sp_sub64_toNat esp (by omega)
  have hmem12 : c2.σ.mem = c1.σ.mem := hmem.trans P.mem.symm
  exact
    { good := hG
      tick := htick
      mem := hmem
      out := hout
      minstret := hmi
      sp := (hkeep _ (by decide)).trans P.sp
      gp := (hkeep _ (by decide)).trans Q.gp
      s2 := (hkeep _ (by decide)).trans P.s2
      s3 := (hkeep _ (by decide)).trans P.s3
      s4 := (hkeep _ (by decide)).trans P.s4
      s5 := (hkeep _ (by decide)).trans P.s5
      rest := fun R hA hRes h2 => by
        obtain ⟨_, hK, _, _, h22⟩ := envDefineRest_facts R hA hRes h2
        exact (hkeep R (KeepButS6.of hA h22)).trans (P.keep R hK)
      saved := Q.saved.of_mem_eq hmem12
      stack := by refine ⟨?_, ?_, ?_⟩ <;> rw [hsp64] <;> omega
      ainv := L.ainv_stable c1.σ c2.σ (hkeep _ (by decide)).symm
        (fun a _ => by rw [hmem12]) Q.ainv }

/-- **The empty-frame lane.**  From the contract entry on a frame without a
binding to the return state, under both ledgers. -/
theorem envDefineEmptyLane
    (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st : Vsa.While.St) (env : Addr) (x : String) (v : Value)
    (esp aEnv aName pv r : BitVec 64) (m : Mem) (out : Array String)
    {gpv : BitVec 64} {headroom maxReq : Nat}
    (M : MallocContract A SL gpv headroom maxReq) (exts : List Extent)
    (hE : EnvDefineMem N A SL φf φc st env x v aEnv aName pv esp m)
    (L : EnvDefineUpdateLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (LM : EnvDefineMissLedger g N A SL φf φc st env x v esp aEnv aName pv r m M exts)
    (hempty : ∀ (h : env < st.store.frames.size), st.store.frames[env].vars.length = 0) :
    Triple (EnvDefineEntryState g N A SL φf φc st env x v esp aEnv aName pv r m out)
      (EnvDefineReturnState g N A SL φf φc st env x v esp r m out) := by
  intro c h
  obtain ⟨c1, hs1, v8, v9, v18, v19, v20, v21, v22, pn, Q⟩ :=
    envDefinePrologueExit g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
      (EnvDefineUpdateOracles.of_entry h.facts L) c h
  have Sf := Q.facts
  have P := Q.post
  have henvLt := Sf.env_lt
  have hcount0 : st.store.frames[env].vars.length = 0 := hempty henvLt
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hAlo := L.arena_ram.1
  have hAhi := L.arena_ram.2
  have hAhtif := L.arena_htif
  obtain ⟨henvArena, henvAlign⟩ := hE.store.frames_arena env henvLt
  unfold Arena.contains at henvArena
  have henvNat : aEnv.toNat = φf env := Sf.env_addr
  -- the frame at the scanned memory
  obtain ⟨_, ⟨cap, hcapR, _⟩, ⟨pn', pvals, hpn', hpvals, _⟩, _⟩ := Sf.store0.frames env henvLt
  have hpnEq : pn' = pn := Option.some.inj (hpn'.symm.trans Sf.pn_read)
  subst pn'
  have hcapSigned : cap < 2^31 := by
    obtain ⟨alloc, shared, readable, writes, hheap, _, _, _⟩ := Sf.owned0
    exact (hheap.store.frames env henvLt).capSigned hheap.ledger hcapR hAhi
  have hcapA : read32 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (aEnv.toNat + 4) =
      some cap := by rw [henvNat]; exact hcapR
  have hpnA : read64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (aEnv.toNat + 8) =
      some pn := by rw [henvNat]; exact Sf.pn_read
  obtain ⟨b0, b1, b2, b3, hb0, hb1, hb2, hb3, hrec⟩ := read32_bytes_ed _ _ cap hcapA
  obtain ⟨d0, d1, d2, d3, d4, d5, d6, d7, hd0, hd1, hd2, hd3, hd4, hd5, hd6, hd7, _⟩ :=
    read64_bytes_eg4 _ _ pn hpnA
  let bs4 : List (BitVec 8) := [b0, b1, b2, b3]
  let bs8 : List (BitVec 8) := [d0, d1, d2, d3, d4, d5, d6, d7]
  have hpins4 : LPins4 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (aEnv.toNat + 4)
      bs4 :=
    ⟨by simpa [bs4] using lpin_of_present hb0, by simpa [bs4] using lpin_of_present hb1,
      by simpa [bs4] using lpin_of_present hb2, by simpa [bs4] using lpin_of_present hb3⟩
  have hpins8 : LPins8 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) (aEnv.toNat + 8)
      bs8 :=
    ⟨by simpa [bs8] using lpin_of_present hd0, by simpa [bs8] using lpin_of_present hd1,
      by simpa [bs8] using lpin_of_present hd2, by simpa [bs8] using lpin_of_present hd3,
      by simpa [bs8] using lpin_of_present hd4, by simpa [bs8] using lpin_of_present hd5,
      by simpa [bs8] using lpin_of_present hd6, by simpa [bs8] using lpin_of_present hd7⟩
  have hcapWord : bytesVal .lw bs4 = BitVec.ofNat 64 cap := by
    simpa [bytesVal, bs4] using sext_count_ed b0 b1 b2 b3 cap hcapSigned hrec
  have hpnWord : bytesVal .ld bs8 = BitVec.ofNat 64 pn := by
    simpa [bs8] using ld_value_eq_read64 _ (aEnv.toNat + 8) pn d0 d1 d2 d3 d4 d5 d6 d7 hpnA
      hd0 hd1 hd2 hd3 hd4 hd5 hd6 hd7
  have henv4 : (aEnv + sign_extend (m := 64) (0x004#12)).toNat = aEnv.toNat + 4 := by
    rw [BitVec.toNat_add, sext4_64, Nat.mod_eq_of_lt (by omega)]
  have henv8 : (aEnv + sign_extend (m := 64) (0x008#12)).toNat = aEnv.toNat + 8 := by
    rw [BitVec.toNat_add, sext8_64, Nat.mod_eq_of_lt (by omega)]
  -- the seg entry
  have hs3 : c1.σ.regs.get? Register.x19 = some 0#64 := by
    have := P.s3; rwa [hcount0] at this
  have hL : GHolds c1.σ (envDefineCapInitL aEnv 0#64) :=
    ⟨by simpa [gprGet] using hs3, by simpa [gprGet] using P.a0, trivial⟩
  have hcode1 : Env_defineLoaded c1.σ.mem := by rw [P.mem]; exact Sf.code0
  let g1 : (R : Register) → Option (RegisterType R) := fun R => c1.σ.regs.get? R
  have hmiss : ∀ j (hj : j < (st.store.frames[env]'Sf.env_lt).vars.length),
      ((st.store.frames[env]'Sf.env_lt).vars[j]'hj).1 ≠ x := fun j hj => by omega
  have F := envDefineMissFacts_of_scan g N A SL φf φc st env x v esp aEnv aName pv r m M exts
    v8 v9 v18 v19 v20 v21 v22 pn _ hE L LM Sf hmiss cap hcapR
  rcases Nat.eq_zero_or_pos cap with hcap0 | hcapPos
  · -- `cap = 0`: the zero route to the grow lane's `realloc(NULL,·)` entry
    subst hcap0
    have hfacts : ChainFacts c1.σ.mem c1.σ.mem (envDefineCapInitL aEnv 0#64) [bs4, bs8]
        envDefineCapInitZeroSeg := by
      chain_facts hcode1 with "Vsa.Sim.Code.env_define_at_"
      · change guardB bop.BGE (srcVal 0 (envDefineCapInitL aEnv 0#64))
          (srcVal 19 (envDefineCapInitL aEnv 0#64)) = true
        have h19 : srcVal 19 (envDefineCapInitL aEnv 0#64) = 0#64 := by
          simp [srcVal, lookupG, envDefineCapInitL]
        have h0 : srcVal 0 (envDefineCapInitL aEnv 0#64) = 0#64 := rfl
        rw [h19, h0]
        decide
      · refine memFactsLw (aEnv.toNat + 4) (by decide) ?_ (by omega) (by omega)
          (by right; omega) ?_
        · rw [capInitLwLine]
          simpa [eaddrM, envDefineCapInitL, srcVal, lookupG] using henv4
        · rw [P.mem]; exact hpins4
      · rw [capInitLwLine]
        simp only [runGM, stepGM, stepLdsM, ldsRunM, wvalM]
        change guardB bop.BNE
          (srcVal 15 ((15, bytesVal MKind.lw bs4) :: eraseG 15 (envDefineCapInitL aEnv 0#64)))
          (srcVal 19 ((15, bytesVal MKind.lw bs4) :: eraseG 15 (envDefineCapInitL aEnv 0#64))) =
          false
        rw [hcapWord]
        simp [envDefineCapInitL, guardB, srcVal, lookupG, eraseG]
      · refine memFactsLd (aEnv.toNat + 8) (by decide) ?_ (by omega) (by omega)
          (by right; omega) ?_
        · rw [capInitLdLine, capInitLwLine]
          simpa [eaddrM, envDefineCapInitL, srcVal, lookupG, eraseG, runGM, stepGM, stepLdsM,
            ldsRunM, wvalM] using henv8
        · rw [capInitLwLine]
          simp only [wlogM, writeLog, List.foldl]
          rw [P.mem]; exact hpins8
      · rw [capInitLwLine, capInitLdLine]
        simp only [runGM, stepGM, stepLdsM, ldsRunM, wvalM]
        change guardB bop.BNE
          (srcVal 15 ((22, bytesVal MKind.ld bs8) :: eraseG 22
            ((15, bytesVal MKind.lw bs4) :: eraseG 15 (envDefineCapInitL aEnv 0#64))))
          (srcVal 0 ((22, bytesVal MKind.ld bs8) :: eraseG 22
            ((15, bytesVal MKind.lw bs4) :: eraseG 15 (envDefineCapInitL aEnv 0#64)))) = false
        rw [hcapWord]
        simp [envDefineCapInitL, guardB, srcVal, lookupG, eraseG]
    have hpre : SegPre envDefineCapInitZeroSeg (envDefineCapInitL aEnv 0#64) [bs4, bs8]
        0x80002a90#64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) c1 :=
      ⟨P.good, P.mem, P.pc, P.minstret, hL, (by show KeysOK [19, 10]; decide),
        hfacts, P.tick⟩
    obtain ⟨c2, hs2, ⟨hG2, hmem2, hpc2, htick2, hmi2, hregs2⟩, hk2⟩ :=
      segRowKeepGhost envDefineCapInitZeroSeg (envDefineCapInitL aEnv 0#64) [bs4, bs8]
        0x80002a90#64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) KeepButS6 g1 out
        (fun c => GoodState c.σ ∧
          c.σ.mem = writeLog (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
            (evalBlocks envDefineCapInitZeroSeg
              (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4, bs8])).log ∧
          c.σ.regs.get? Register.PC = some (evalBlocksPC 0x80002a90#64
            (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4, bs8])
            envDefineCapInitZeroSeg) ∧
          c.tick < 2 ∧ (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
          GHolds c.σ (evalBlocks envDefineCapInitZeroSeg
            (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4, bs8])).regs)
        (by show ChainOK 0x80002a90#64 [19, 10] envDefineCapInitZeroSeg; decide)
        (by show ∀ rr ∈ noiseRegs, KeepButS6 rr = false; decide)
        (by show WrChainAvoids KeepButS6 envDefineCapInitZeroSeg; decide)
        (fun σ' i' u' hG hi hmem hpc hmi hregs => ⟨hG, hmem, hpc, hi, hmi, hregs⟩)
        c1 ⟨hpre, fun _ _ => rfl, P.out⟩
    have hmemA : c2.σ.mem = envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22 := by
      simpa [envDefineCapInitZeroSeg, evalBlocks, SegEvalState.init, writeLog] using hmem2
    have hpcA : c2.σ.regs.get? Register.PC = some 0x80002b98#64 := by rw [hpc2]; rfl
    have reg (n : Nat) (w : BitVec 64)
        (hl : lookupG n (evalBlocks envDefineCapInitZeroSeg
          (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4, bs8])).regs = some w) :
        gprGet c2.σ n = some w := gholds_lookup _ hregs2 hl
    have ha5 : c2.σ.regs.get? Register.x15 = some 8#64 := by
      simpa [gprGet] using reg 15 8#64 (by
        simp only [envDefineCapInitZeroSeg, evalBlocks, evalBlock, SegEvalState.init]
        rw [capInitLwLine, capInitLdLine, capInitLiA1Line, capInitLiA5Line]
        simp [runGM, stepGM, stepLdsM, ldsRunM, wvalM, lookupG, eraseG, envDefineCapInitL,
          srcVal, sext8_bv, sext64_bv])
    have ha1 : c2.σ.regs.get? Register.x11 = some 64#64 := by
      simpa [gprGet] using reg 11 64#64 (by
        simp only [envDefineCapInitZeroSeg, evalBlocks, evalBlock, SegEvalState.init]
        rw [capInitLwLine, capInitLdLine, capInitLiA1Line, capInitLiA5Line]
        simp [runGM, stepGM, stepLdsM, ldsRunM, wvalM, lookupG, eraseG, envDefineCapInitL,
          srcVal, sext8_bv, sext64_bv])
    have hs6 : c2.σ.regs.get? Register.x22 = some (BitVec.ofNat 64 pn) := by
      rw [← hpnWord]
      simpa [gprGet] using reg 22 (bytesVal .ld bs8) (by
        simp only [envDefineCapInitZeroSeg, evalBlocks, evalBlock, SegEvalState.init]
        rw [capInitLwLine, capInitLdLine, capInitLiA1Line, capInitLiA5Line]
        simp [runGM, stepGM, stepLdsM, ldsRunM, wvalM, lookupG, eraseG, envDefineCapInitL,
          srcVal, sext8_bv, sext64_bv])
    have Rg := envDefineEmptyRegs g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
      v8 v9 v18 v19 v20 v21 v22 pn c1 c2 hE L Q hG2 htick2 hmemA hmi2 hk2.keep hk2.out
    obtain ⟨c3, hs3', hret⟩ :=
      envDefineGrowEntry_run g N A SL φf φc st env x v esp aEnv aName pv r m out M exts exts _
        hE L LM c2 ⟨0, pn, pvals, F, Rg, hcount0, Sf.pn_read, hpvals, by omega,
          .init rfl hpcA ha5 ha1, hs6⟩
    exact ⟨c3, hs1.trans (hs2.trans hs3'), hret⟩
  · -- `cap ≠ 0`: the append head, entered without the scan
    have hne : BitVec.ofNat 64 cap ≠ 0#64 := by
      intro h0
      have := congrArg BitVec.toNat h0
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this
      omega
    have hfacts : ChainFacts c1.σ.mem c1.σ.mem (envDefineCapInitL aEnv 0#64) [bs4]
        envDefineCapInitAppendSeg := by
      chain_facts hcode1 with "Vsa.Sim.Code.env_define_at_"
      · change guardB bop.BGE (srcVal 0 (envDefineCapInitL aEnv 0#64))
          (srcVal 19 (envDefineCapInitL aEnv 0#64)) = true
        have h19 : srcVal 19 (envDefineCapInitL aEnv 0#64) = 0#64 := by
          simp [srcVal, lookupG, envDefineCapInitL]
        have h0 : srcVal 0 (envDefineCapInitL aEnv 0#64) = 0#64 := rfl
        rw [h19, h0]
        decide
      · refine memFactsLw (aEnv.toNat + 4) (by decide) ?_ (by omega) (by omega)
          (by right; omega) ?_
        · rw [capInitLwLine]
          simpa [eaddrM, envDefineCapInitL, srcVal, lookupG] using henv4
        · rw [P.mem]; exact hpins4
      · rw [capInitLwLine]
        simp only [runGM, stepGM, stepLdsM, ldsRunM, wvalM]
        change guardB bop.BNE
          (srcVal 15 ((15, bytesVal MKind.lw bs4) :: eraseG 15 (envDefineCapInitL aEnv 0#64)))
          (srcVal 19 ((15, bytesVal MKind.lw bs4) :: eraseG 15 (envDefineCapInitL aEnv 0#64))) =
          true
        rw [hcapWord]
        simp [envDefineCapInitL, guardB, srcVal, lookupG, eraseG, hne]
    have hpre : SegPre envDefineCapInitAppendSeg (envDefineCapInitL aEnv 0#64) [bs4]
        0x80002a90#64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) c1 :=
      ⟨P.good, P.mem, P.pc, P.minstret, hL, (by show KeysOK [19, 10]; decide),
        hfacts, P.tick⟩
    obtain ⟨c2, hs2, ⟨hG2, hmem2, hpc2, htick2, hmi2, _⟩, hk2⟩ :=
      segRowKeepGhost envDefineCapInitAppendSeg (envDefineCapInitL aEnv 0#64) [bs4]
        0x80002a90#64 (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22) KeepButS6 g1 out
        (fun c => GoodState c.σ ∧
          c.σ.mem = writeLog (envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22)
            (evalBlocks envDefineCapInitAppendSeg
              (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4])).log ∧
          c.σ.regs.get? Register.PC = some (evalBlocksPC 0x80002a90#64
            (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4])
            envDefineCapInitAppendSeg) ∧
          c.tick < 2 ∧ (∃ w, c.σ.regs.get? Register.minstret = some w) ∧
          GHolds c.σ (evalBlocks envDefineCapInitAppendSeg
            (SegEvalState.init (envDefineCapInitL aEnv 0#64) [bs4])).regs)
        (by show ChainOK 0x80002a90#64 [19, 10] envDefineCapInitAppendSeg; decide)
        (by show ∀ rr ∈ noiseRegs, KeepButS6 rr = false; decide)
        (by show WrChainAvoids KeepButS6 envDefineCapInitAppendSeg; decide)
        (fun σ' i' u' hG hi hmem hpc hmi hregs => ⟨hG, hmem, hpc, hi, hmi, hregs⟩)
        c1 ⟨hpre, fun _ _ => rfl, P.out⟩
    have hmemA : c2.σ.mem = envDefineScannedMem m esp r v8 v9 v18 v19 v20 v21 v22 := by
      simpa [envDefineCapInitAppendSeg, evalBlocks, SegEvalState.init, writeLog] using hmem2
    have hpcA : c2.σ.regs.get? Register.PC = some 0x80002b1c#64 := by rw [hpc2]; rfl
    have Rg := envDefineEmptyRegs g N A SL φf φc st env x v esp aEnv aName pv r m out M exts
      v8 v9 v18 v19 v20 v21 v22 pn c1 c2 hE L Q hG2 htick2 hmemA hmi2 hk2.keep hk2.out
    obtain ⟨c3, hs3', hret⟩ :=
      envDefineAppendLane g N A SL φf φc st env x v esp aEnv aName pv r m out M exts exts _
        cap hE L LM c2 ⟨F, Rg, hpcA, by rw [hcount0]; exact hcapPos⟩
    exact ⟨c3, hs1.trans (hs2.trans hs3'), hret⟩

#print axioms envDefineCapInitGrow_unreachable
#print axioms envDefineEmptyRegs
#print axioms envDefineEmptyLane

end Vsa.Sim
