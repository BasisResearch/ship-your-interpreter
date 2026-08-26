import Vsa.Sim.EvalLogical2
import Vsa.Sim.EvalLogical3
import Vsa.Sim.EvalOrSim
import Vsa.Sim.EvalAndSim
import Vsa.Sim.EvalBinSim

/-!
# Layer 4 — M4 recursive case: the logical `.or`-FALSE two-eval constructor

The `EvalE.orFalse` constructor: `l` evaluates to a falsy `vl`, so the `.or`
does NOT short-circuit — it evaluates `r` (→ `vr`) and yields `.bool vr.truthy`.

`blockC_orFalse` consumes the same `SubEvalReturn @0x8000356c` (LEFT value `vl`
at `sp-968`) that `blockC_orTrue` does — the op-dispatch and value_truthy(vl)
prefix is IDENTICAL (op == 25 ⇒ beq TAKEN ⇒ OR arm @0x80003978) — but at the
`beqz` (`0x80003998`) the branch IS taken (`vl.truthy = false`), so control
jumps to the two-eval continue at `0x80003a00`:

```
80003a00: ld   x12,0x18(x8)   -- RIGHT operand ptr (node offset 24)
80003a04: addi x11,x18,0x0    -- a1 := interp* (from s2/x18)
80003a08: addi x10,x2,0x90    -- sret_R = (sp-1088)+144 = sp-944
80003a0c: jal  eval_expr      -- RIGHT call (armTail_rec); ra := 0x80003a10
80003a10: ld   x13,0x90(x2)   -- rv kind  @ sp-944
80003a14: ld   x14,0x98(x2)   -- rv pay   @ sp-936
80003a18: ld   x15,0xa0(x2)   -- rv[16..) @ sp-928
80003a1c: j    0x800035bc     -- join SHARED tail (blockC_logTail)
```

`blockC_orFalse = <orTrue prefix σ1..σ12> ≫ beqz-taken ≫ <x12/x11/x10 setup>
≫ armTail_rec(RIGHT) ≫ <3 loads> ≫ blockC_logTail`, producing
`PreEpilogueVD … (.bool vr.truthy) 0x800033ec`.

NO `sorry`/`axiom`/`native_decide`/`bv_decide`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.RuntimeRepr
open Vsa.MemRepr
open Vsa.While
open Vsa.Alloc
open Vsa.Sim.Code

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `blockC_orFalse` — the `.or` post-call two-eval (falsy left) tail

From `SubEvalReturn @0x8000356c` (LEFT value `vl` at `sp-968`) for a
`.logical .or el er` node with `vl.truthy = false`, plus the IH for the RIGHT
operand `er`: op-dispatch (`beq` TAKEN → OR arm @0x80003978), copy `vl` into the
`value_truthy` arg buffer `sp-1024`, `value_truthy(vl) = 0`, `beqz` TAKEN →
`0x80003a00` two-eval continue, evaluate `er` (RIGHT `armTail_rec`, buffer
`sp-944`), then the shared `blockC_logTail` (`value_truthy(vr)`+`value_bool`) →
`.bool vr.truthy`.

Output: `PreEpilogueVD … (.bool vr.truthy) 0x800033ec` (fed to `blockD_v_rec`). -/
theorem blockC_orFalse
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (vl vr : Value)
    (sp r sret aExpr aEnv aRight : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (el er : Expr) (m0 : Mem)
    (hvlfalse : vl.truthy = false)
    (hIHr : EvalIH st' d env er st'' vr)
    -- store-size stability (mirrors `blockB_binary`'s `hSizeF`/`hSizeC` residual):
    (hSizeF : st'.store.frames.size = st''.store.frames.size)
    (hSizeC : st'.store.closures.size = st''.store.closures.size) :
    Triple
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc st' vl sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)) (0x8000356c#64)
          v8 v9 v18 mcall c ∧
        gpre Register.x8 = some aExpr ∧
        gpre Register.x18 = some aEnv ∧
        ExprRepr mcall aExpr.toNat (.logical .or el er) ∧
        read64 mcall (aExpr.toNat + 24) = some aRight.toNat ∧
        (∀ a : Nat, (∃ b, mcall[a]? = some b)) ∧
        aExpr.toNat % 8 = 0 ∧
        0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
        aExpr.toNat + 32 ≤ 0x100000000 ∧
        tohostAddr + 8 ≤ aExpr.toNat ∧
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        (aExpr.toNat + 32 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat) ∧
        (aExpr.toNat + 32 ≤ A.lo ∨ A.hi ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ sp.toNat - 968 ∨ sp.toNat - 968 + 24 ≤ aExpr.toNat) ∧
        -- RIGHT operand geometry (the second sub-call's `aExpr`):
        (∀ m' : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
            mcall[a]? = m'[a]?) →
          ExprRepr m' aRight.toNat er) ∧
        aRight.toNat % 8 = 0 ∧
        0x80000000 ≤ aRight.toNat ∧ aRight.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ aRight.toNat ∧
        (aRight.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aRight.toNat) ∧
        -- RIGHT-value payload disjointness (mirrors `pay_disj`, for the `blockC_logTail` copy):
        (∀ (mR : Mem) (φ : Addr → Nat) (p : Nat) (s : String),
          ValueRepr mR N φ (sp.toNat - 944) vr → read64 mR (sp.toNat - 944 + 8) = some p →
          ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)) ∧
        -- RIGHT-value map coherence (the value/store closure maps agree on the
        -- allocated prefix; ValueRepr transports between them — a `.closure`-only
        -- residual, trivial for leaf values):
        (∀ (mR : Mem) (φa φb : Addr → Nat),
          (∀ i, i < st''.store.closures.size → φa i = φb i) →
          ValueRepr mR N φa (sp.toNat - 944) vr → ValueRepr mR N φb (sp.toNat - 944) vr) ∧
        String.join out0.toList = st'.out ∧
        sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
        r.toNat % 4 = 0 ∧
        SL.lo + 3264 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        c.σ.sailOutput = out0 ∧
        Value_truthyLoaded mcall ∧ Value_boolLoaded mcall ∧
        Value_intLoaded mcall ∧ IntSlotPinned mcall ∧
        (∀ φc' : Addr → Nat, ValueRepr c.σ.mem N φc' (sp.toNat - 968) vl →
          LogicalBufExtras N A SL φc' vl sp sret c.σ.mem) ∧
        (sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo) ∧
        (sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo) ∧
        (A.hi ≤ 0x8000282c ∨ 0x8000285c ≤ A.lo) ∧
        (A.hi ≤ 0x800027f8 ∨ 0x8000280c ≤ A.lo) ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        ((0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c) ∧
        ((0x80019f58 : Nat) + 4 ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58) ∧
        (A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo) ∧
        (A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo) ∧
        (A.hi ≤ 0x8000280c ∨ 0x8000281c ≤ A.lo) ∧
        (A.hi ≤ jumpTableBase ∨ jumpTableBase + 4 ≤ A.lo) ∧
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
          mcall[a]? = m0[a]?) ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ sp.toNat % 16 = 0 ∧
        SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (fun c => ∃ (mpre : Mem) (φfe φce : Addr → Nat) (outF : Array String),
        PhiExtends φf φfe st''.store.frames.size ∧
        PhiExtends φc φce st''.store.closures.size ∧
        PreEpilogueVD g N A SL φfe φce st'' (.bool vr.truthy) sp r sret v8 v9 v18 outF m0 mpre c) := by
  intro c hpre
  obtain ⟨mcall, hSub, hgx8, hgx18, hexpr, hPayRight, hStackPop, hexprAl, hexprLo, hexprHi, hexprHi32,
    hexprWin, hexprSL, hexprSL32, hexprA, hexprA32, hexprSub,
    hRightSurv, hropAl, hropLo, hropHi, hropWin, hropStk, hPayDisjRight, hVrMapCoh,
    houtStr, hsretAl, hsretLo, hsretHi, hsretWin, hsretStk, hsretEvalCode, hSretBoolCode,
    hraAl, hSLloSp, hSLlo, hSLwin,
    hout0eq, hVtruthyMcall, hVboolMcall, hViIntMcall, hViSlotMcall, hBufExtras,
    hTruthyStk, hBoolStk, hTruthyArena, hBoolArena, hcodeStk, hviStk, htableStk,
    harenaStk, harenaCode, harenaVi, harenaTable, hsretInSL, hMcallM0,
    hsphiRam, hsp8, hsp16, hSLhiRam, hspSLhi, hgv8, hgv9, hgv18, hgv2, hbridge⟩ := hpre
  obtain ⟨hG, htick, hpc, ha0, hra, hs1, hsp, ⟨vmi, hmi⟩, hout, hframe,
    ⟨φcv, hpcv, hvalSub⟩, hstoreBundle, hcode,
    hslotRa, hslotS0, hslotS1, hslotS2, hmemFrame, hMemExt⟩ := hSub
  obtain ⟨φf', φc', hpf', hpc', hstore', hstoreSurv'⟩ := hstoreBundle
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hsp1088 : 1088 ≤ sp.toNat := by omega
  have hspsub : (sp - 1088#64).toNat = sp.toNat - 1088 := by
    rw [BitVec.toNat_sub]
    have h1088 : (1088#64 : BitVec 64).toNat = 1088 := by decide
    rw [h1088]; have := sp.isLt; omega
  have hsub968 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 :=
    spill_addr sp (0x078#12) 968 (by decide) (by omega) hsp1088
  have hvalSub' : ValueRepr c.σ.mem N φcv (sp.toNat - 968) vl := by rwa [hsub968] at hvalSub
  have hBE : LogicalBufExtras N A SL φcv vl sp sret c.σ.mem := hBufExtras φcv hvalSub'
  have hx8 : c.σ.regs.get? Register.x8 = some aExpr := (hframe Register.x8 (by decide)).trans hgx8
  have hx18 : c.σ.regs.get? Register.x18 = some aEnv := (hframe Register.x18 (by decide)).trans hgx18
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  -- ExprRepr (.logical .or el er): kind = 7, op-token = logOpTok .or = 25
  obtain ⟨lptr, rptr, hk7, hoptok, hlptr, hlR, hrptr, hrR⟩ : ∃ lp rp,
      read32 mcall aExpr.toNat = some 7 ∧ read32 mcall (aExpr.toNat + 8) = some (logOpTok .or) ∧
      read64 mcall (aExpr.toNat + 16) = some lp ∧ ExprRepr mcall lp el ∧
      read64 mcall (aExpr.toNat + 24) = some rp ∧ ExprRepr mcall rp er := by
    cases hexpr with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hoptok25 : read32 mcall (aExpr.toNat + 8) = some 25 := by simpa [logOpTok] using hoptok
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes mcall (aExpr.toNat + 8) 25 hoptok25
  have hAgOp : ∀ k : Nat, aExpr.toNat + 8 ≤ k → k < aExpr.toNat + 12 →
      c.σ.mem[k]? = mcall[k]? := by
    intro k hk1 hk2
    rcases hmemFrame k
      (by rw [hspsub] at *; rcases hexprSL with h | h <;> omega)
      (by rcases hexprA with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hexprSub with h | h <;> omega)
    · exact heq
  have hoc0 : c.σ.mem[aExpr.toNat + 8]? = some ob0 := (hAgOp _ (by omega) (by omega)).trans hob0
  have hoc1 : c.σ.mem[aExpr.toNat + 8 + 1]? = some ob1 := (hAgOp _ (by omega) (by omega)).trans hob1
  have hoc2 : c.σ.mem[aExpr.toNat + 8 + 2]? = some ob2 := (hAgOp _ (by omega) (by omega)).trans hob2
  have hoc3 : c.σ.mem[aExpr.toNat + 8 + 3]? = some ob3 := (hAgOp _ (by omega) (by omega)).trans hob3
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (25#64 : BitVec 64) := by
    rw [sext_word_small _ 25 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  have hli25 : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x019#12)) = (25#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have heq2525 : ((25#64 : BitVec 64) == (25#64 : BitVec 64)) = true := by decide
  -- the whole 24-byte sub-Value buffer bytes at c.σ.mem[sp-968 .. +24) (present).
  have hStackPopC : ∀ a : Nat, ∃ b, c.σ.mem[a]? = some b :=
    fun a => stackpop_present hMemExt hStackPop a
  obtain ⟨kb0, hkb0⟩ := hStackPopC (sp.toNat - 968)
  obtain ⟨kb1, hkb1⟩ := hStackPopC (sp.toNat - 968 + 1)
  obtain ⟨kb2, hkb2⟩ := hStackPopC (sp.toNat - 968 + 2)
  obtain ⟨kb3, hkb3⟩ := hStackPopC (sp.toNat - 968 + 3)
  obtain ⟨kb4, hkb4⟩ := hStackPopC (sp.toNat - 968 + 4)
  obtain ⟨kb5, hkb5⟩ := hStackPopC (sp.toNat - 968 + 5)
  obtain ⟨kb6, hkb6⟩ := hStackPopC (sp.toNat - 968 + 6)
  obtain ⟨kb7, hkb7⟩ := hStackPopC (sp.toNat - 968 + 7)
  obtain ⟨pb0, hpb0⟩ := hStackPopC (sp.toNat - 960)
  obtain ⟨pb1, hpb1⟩ := hStackPopC (sp.toNat - 960 + 1)
  obtain ⟨pb2, hpb2⟩ := hStackPopC (sp.toNat - 960 + 2)
  obtain ⟨pb3, hpb3⟩ := hStackPopC (sp.toNat - 960 + 3)
  obtain ⟨pb4, hpb4⟩ := hStackPopC (sp.toNat - 960 + 4)
  obtain ⟨pb5, hpb5⟩ := hStackPopC (sp.toNat - 960 + 5)
  obtain ⟨pb6, hpb6⟩ := hStackPopC (sp.toNat - 960 + 6)
  obtain ⟨pb7, hpb7⟩ := hStackPopC (sp.toNat - 960 + 7)
  obtain ⟨qb0, hqb0⟩ := hStackPopC (sp.toNat - 952)
  obtain ⟨qb1, hqb1⟩ := hStackPopC (sp.toNat - 952 + 1)
  obtain ⟨qb2, hqb2⟩ := hStackPopC (sp.toNat - 952 + 2)
  obtain ⟨qb3, hqb3⟩ := hStackPopC (sp.toNat - 952 + 3)
  obtain ⟨qb4, hqb4⟩ := hStackPopC (sp.toNat - 952 + 4)
  obtain ⟨qb5, hqb5⟩ := hStackPopC (sp.toNat - 952 + 5)
  obtain ⟨qb6, hqb6⟩ := hStackPopC (sp.toNat - 952 + 6)
  obtain ⟨qb7, hqb7⟩ := hStackPopC (sp.toNat - 952 + 7)
  let K13 : BitVec 64 := sign_extend (m := 64)
    ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))
  let PV : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  let QV : BitVec 64 := sign_extend (m := 64)
    ((((((((qb7.append qb6).append qb5).append qb4).append qb3).append qb2).append qb1).append qb0) : BitVec (8*8))
  have haddr120 : ((sp - 1088#64) + sign_extend (m := 64) (0x078#12)).toNat = sp.toNat - 968 := hsub968
  have haddr128 : ((sp - 1088#64) + sign_extend (m := 64) (0x080#12)).toNat = sp.toNat - 960 :=
    spill_addr sp (0x080#12) 960 (by decide) (by omega) hsp1088
  have haddr136 : ((sp - 1088#64) + sign_extend (m := 64) (0x088#12)).toNat = sp.toNat - 952 :=
    spill_addr sp (0x088#12) 952 (by decide) (by omega) hsp1088
  have haddr64 : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 :=
    spill_addr sp (0x040#12) 1024 (by decide) (by omega) hsp1088
  have haddr72 : ((sp - 1088#64) + sign_extend (m := 64) (0x048#12)).toNat = sp.toNat - 1016 :=
    spill_addr sp (0x048#12) 1016 (by decide) (by omega) hsp1088
  have haddr80 : ((sp - 1088#64) + sign_extend (m := 64) (0x050#12)).toNat = sp.toNat - 1008 :=
    spill_addr sp (0x050#12) 1008 (by decide) (by omega) hsp1088
  ------------------------------------------------------------------------
  -- 0x8000356c → 0x80003584: op check (beq NOT taken), loads, addi.
  ------------------------------------------------------------------------
  -- 0x8000356c: lw a4,8(s0) → x14 := 24 (op token)
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_8000356c_lg c.σ c.tick c.steps (0x8000356c#64) vmi aExpr
      ob0 ob1 ob2 ob3 hG hpc hmi hx8 hcode rfl
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      (by rw [hop8]; exact hoc0) (by rw [hop8]; exact hoc1)
      (by rw [hop8]; exact hoc2) (by rw [hop8]; exact hoc3) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x80003570#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x8000356c#64) 4 = (0x80003570#64 : BitVec 64) from by decide] at this
  have hx14_1 : σ1.regs.get? Register.x14 = some (25#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hopVal] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other hobs1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some aExpr := obs_alu_other hobs1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8
  have hx18_1 : σ1.regs.get? Register.x18 = some aEnv := obs_alu_other hobs1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout0eq
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- 0x80003570: li a5,25 → x15 := 25
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_80003570_lg σ1 i1 (c.steps + 1) (0x80003570#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x80003574#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x80003570#64) 4 = (0x80003574#64 : BitVec 64) from by decide] at this
  have hx15_2 : σ2.regs.get? Register.x15 = some (25#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hli25] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (25#64) := obs_alu_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other hobs2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_1
  have hx8_2 : σ2.regs.get? Register.x8 = some aExpr := obs_alu_other hobs2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_1
  have hx18_2 : σ2.regs.get? Register.x18 = some aEnv := obs_alu_other hobs2 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- 0x80003574: ld a2,120(sp) → x12 := K13 (kind dword)
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_80003574_lg σ2 i2 (c.steps + 1 + 1) (0x80003574#64) vmi2 (sp - 1088#64)
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [haddr120]; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, htoh]; right; omega) (by rw [haddr120]; omega)
      (by rw [haddr120, hmem2e]; exact hkb0) (by rw [haddr120, hmem2e]; exact hkb1)
      (by rw [haddr120, hmem2e]; exact hkb2) (by rw [haddr120, hmem2e]; exact hkb3)
      (by rw [haddr120, hmem2e]; exact hkb4) (by rw [haddr120, hmem2e]; exact hkb5)
      (by rw [haddr120, hmem2e]; exact hkb6) (by rw [haddr120, hmem2e]; exact hkb7) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = c.σ.mem := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x80003578#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x80003574#64) 4 = (0x80003578#64 : BitVec 64) from by decide] at this
  have hx12_3 : σ3.regs.get? Register.x12 = some K13 :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_3 : σ3.regs.get? Register.x14 = some (25#64) := obs_alu_other hobs3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_2
  have hx15_3 : σ3.regs.get? Register.x15 = some (25#64) := obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other hobs3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_2
  have hx8_3 : σ3.regs.get? Register.x8 = some aExpr := obs_alu_other hobs3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_2
  have hx18_3 : σ3.regs.get? Register.x18 = some aEnv := obs_alu_other hobs3 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- 0x80003578: beq a4,a5 (TAKEN, 25 == 25) → 0x80003978 (OR arm)
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_80003578_taken_lg σ3 i3 (c.steps + 1 + 1 + 1) (0x80003578#64) vmi3 (25#64) (25#64)
      hG3 hpc3 hmi3 hx14_3 hx15_3 hcode3 rfl heq2525 hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = c.σ.mem := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x80003978#64) := by
    have := obs_branch_taken_pc hobs4
    rwa [site_80003578_taken_lg_tgt] at this
  have hx12_4 : σ4.regs.get? Register.x12 = some K13 := obs_branch_taken_other hobs4 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_branch_taken_other hobs4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_taken_other hobs4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_3
  have hx8_4 : σ4.regs.get? Register.x8 = some aExpr := obs_branch_taken_other hobs4 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_3
  have hx18_4 : σ4.regs.get? Register.x18 = some aEnv := obs_branch_taken_other hobs4 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_3
  obtain ⟨vmi4, hmi4⟩ := obs_branch_taken_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_branch_taken]; exact hout3
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- 0x80003978: ld a4,128(sp) → x14 := PV
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_80003978_lg σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80003978#64) vmi4 (sp - 1088#64)
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haddr128]; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, htoh]; right; omega) (by rw [haddr128]; omega)
      (by rw [haddr128, hmem4e]; exact hpb0) (by rw [haddr128, hmem4e]; exact hpb1)
      (by rw [haddr128, hmem4e]; exact hpb2) (by rw [haddr128, hmem4e]; exact hpb3)
      (by rw [haddr128, hmem4e]; exact hpb4) (by rw [haddr128, hmem4e]; exact hpb5)
      (by rw [haddr128, hmem4e]; exact hpb6) (by rw [haddr128, hmem4e]; exact hpb7) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = c.σ.mem := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x8000397c#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x80003978#64) 4 = (0x8000397c#64 : BitVec 64) from by decide] at this
  have hx14_5 : σ5.regs.get? Register.x14 = some PV :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12_5 : σ5.regs.get? Register.x12 = some K13 := obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_4
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_alu_other hobs5 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs5 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_4
  have hx8_5 : σ5.regs.get? Register.x8 = some aExpr := obs_alu_other hobs5 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_4
  have hx18_5 : σ5.regs.get? Register.x18 = some aEnv := obs_alu_other hobs5 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_alu]; exact hout4
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  -- 0x8000397c: ld a5,136(sp) → x15 := QV
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_8000397c_lg σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x8000397c#64) vmi5 (sp - 1088#64)
      qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7 hG5 hpc5 hmi5 hsp_5 hcode5 rfl
      (by rw [haddr136]; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, htoh]; right; omega) (by rw [haddr136]; omega)
      (by rw [haddr136, hmem5e]; exact hqb0) (by rw [haddr136, hmem5e]; exact hqb1)
      (by rw [haddr136, hmem5e]; exact hqb2) (by rw [haddr136, hmem5e]; exact hqb3)
      (by rw [haddr136, hmem5e]; exact hqb4) (by rw [haddr136, hmem5e]; exact hqb5)
      (by rw [haddr136, hmem5e]; exact hqb6) (by rw [haddr136, hmem5e]; exact hqb7) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6'
  have hmem6e : σ6.mem = c.σ.mem := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003980#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x8000397c#64) 4 = (0x80003980#64 : BitVec 64) from by decide] at this
  have hx15_6 : σ6.regs.get? Register.x15 = some QV :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12_6 : σ6.regs.get? Register.x12 = some K13 := obs_alu_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_5
  have hx14_6 : σ6.regs.get? Register.x14 = some PV := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_5
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other hobs6 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs6 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_5
  have hx8_6 : σ6.regs.get? Register.x8 = some aExpr := obs_alu_other hobs6 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_5
  have hx18_6 : σ6.regs.get? Register.x18 = some aEnv := obs_alu_other hobs6 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact hout5
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  -- 0x80003980: addi a0,sp,64 → x10 := (sp-1088)+64 = sp-1024 (buf)
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80003980_lg σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003980#64) vmi6 (sp - 1088#64)
      hG6 hpc6 hmi6 hsp_6 hcode6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7'
  have hmem7e : σ7.mem = c.σ.mem := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003984#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80003980#64) 4 = (0x80003984#64 : BitVec 64) from by decide] at this
  have hx10_7 : σ7.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx12_7 : σ7.regs.get? Register.x12 = some K13 := obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_6
  have hx14_7 : σ7.regs.get? Register.x14 = some PV := obs_alu_other hobs7 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_6
  have hx15_7 : σ7.regs.get? Register.x15 = some QV := obs_alu_other hobs7 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_alu_other hobs7 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs7 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_6
  have hx8_7 : σ7.regs.get? Register.x8 = some aExpr := obs_alu_other hobs7 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_6
  have hx18_7 : σ7.regs.get? Register.x18 = some aEnv := obs_alu_other hobs7 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_alu]; exact hout6
  have hcode7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode
  ------------------------------------------------------------------------
  -- 0x80003984 / 3988 / 398c: the three copy stores. Memory towers m1/m2/m3.
  ------------------------------------------------------------------------
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)
  let m3 : Mem := writeMap8 m2 (sp.toNat - 1008) (sdData_val QV)
  -- 0x80003984: sd a2,64(sp) → m1 (stores x12 = K13)
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80003984_lg σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003984#64) vmi7 (sp - 1088#64) K13
      hG7 hpc7 hmi7 hsp_7 hx12_7 hcode7 rfl
      (by rw [haddr64]; omega) (by rw [haddr64]; omega) (by rw [haddr64, htoh]; omega) (by rw [haddr64]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = m1 := by rw [hmem8, mem_afterNextPC, haddr64, hmem7e]
  have hpc8 : σ8.regs.get? Register.PC = some (0x80003988#64) := by
    have := obs_store_pc_val hobs8
    rwa [show BitVec.addInt (0x80003984#64) 4 = (0x80003988#64 : BitVec 64) from by decide] at this
  have hx10_8 := obs_store_other_val hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_7
  have hx14_8 := obs_store_other_val hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx14_7
  have hx15_8 := obs_store_other_val hobs8 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_7
  have hs1_8 := obs_store_other_val hobs8 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_7
  have hsp_8 := obs_store_other_val hobs8 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_7
  have hx8_8 := obs_store_other_val hobs8 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_7
  have hx18_8 := obs_store_other_val hobs8 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret_val hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_store]; exact hout7
  have hcode8 : Eval_exprLoaded σ8.mem := by
    rw [hmem8e]
    exact loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  -- 0x80003988: sd a4,72(sp) → m2 (stores x14 = PV)
  obtain ⟨σ9, i9, hs9', hi9, hG9, hmem9, hobs9⟩ :=
    site_80003988_lg σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003988#64) vmi8 (sp - 1088#64) PV
      hG8 hpc8 hmi8 hsp_8 hx14_8 hcode8 rfl
      (by rw [haddr72]; omega) (by rw [haddr72]; omega) (by rw [haddr72, htoh]; omega) (by rw [haddr72]; omega) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9'
  have hmem9e : σ9.mem = m2 := by rw [hmem9, mem_afterNextPC, haddr72, hmem8e]
  have hpc9 : σ9.regs.get? Register.PC = some (0x8000398c#64) := by
    have := obs_store_pc_val hobs9
    rwa [show BitVec.addInt (0x80003988#64) 4 = (0x8000398c#64 : BitVec 64) from by decide] at this
  have hx10_9 := obs_store_other_val hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_8
  have hx15_9 := obs_store_other_val hobs9 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx15_8
  have hs1_9 := obs_store_other_val hobs9 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_8
  have hsp_9 := obs_store_other_val hobs9 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_8
  have hx8_9 := obs_store_other_val hobs9 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_8
  have hx18_9 := obs_store_other_val hobs9 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_val hobs9
  have hout9 : σ9.sailOutput = out0 := by rw [hobs9.out, sailOutput_sigmaPost_store]; exact hout8
  have hcode9 : Eval_exprLoaded σ9.mem := by
    rw [hmem9e]
    exact loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem8e ▸ hcode8)
  -- 0x8000398c: sd a5,80(sp) → m3 (stores x15 = QV)
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_8000398c_lg σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000398c#64) vmi9 (sp - 1088#64) QV
      hG9 hpc9 hmi9 hsp_9 hx15_9 hcode9 rfl
      (by rw [haddr80]; omega) (by rw [haddr80]; omega) (by rw [haddr80, htoh]; omega) (by rw [haddr80]; omega) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10'
  have hmem10e : σ10.mem = m3 := by rw [hmem10, mem_afterNextPC, haddr80, hmem9e]
  have hpc10 : σ10.regs.get? Register.PC = some (0x80003990#64) := by
    have := obs_store_pc_val hobs10
    rwa [show BitVec.addInt (0x8000398c#64) 4 = (0x80003990#64 : BitVec 64) from by decide] at this
  have hx10_10 := obs_store_other_val hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_9
  have hs1_10 := obs_store_other_val hobs10 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_9
  have hsp_10 := obs_store_other_val hobs10 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_9
  have hx8_10 := obs_store_other_val hobs10 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_9
  have hx18_10 := obs_store_other_val hobs10 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret_val hobs10
  have hout10 : σ10.sailOutput = out0 := by rw [hobs10.out, sailOutput_sigmaPost_store]; exact hout9
  have hcode_m3 : Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem9e ▸ hcode9)
  have hcode10 : Eval_exprLoaded σ10.mem := by rw [hmem10e]; exact hcode_m3
  have hx10_10' : σ10.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) := hx10_10
  ------------------------------------------------------------------------
  -- the copied 24-byte buffer represents `vl`: ValueRepr m3 (sp-1024) vl.
  ------------------------------------------------------------------------
  have hm3_out : ∀ a, (a < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ a) → m3[a]? = c.σ.mem[a]? := by
    intro a ha
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) a (sdData_val QV) (by omega)]
    show (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) a (sdData_val PV) (by omega)]
    show (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[a]? = c.σ.mem[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) a (sdData_val K13) (by omega)]
  obtain ⟨eK0, eK1, eK2, eK3, eK4, eK5, eK6, eK7⟩ := sdData_sext_bytes kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7
  obtain ⟨eP0, eP1, eP2, eP3, eP4, eP5, eP6, eP7⟩ := sdData_sext_bytes pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7
  obtain ⟨eQ0, eQ1, eQ2, eQ3, eQ4, eQ5, eQ6, eQ7⟩ := sdData_sext_bytes qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7
  have hK : ∀ o : Nat, o < 8 →
      m3[sp.toNat - 1024 + o]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[sp.toNat - 1024 + o]? := by
    intro o ho
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[_]? = _
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) _ (sdData_val QV) (by omega)]
    show (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[_]? = _
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) _ (sdData_val PV) (by omega)]
  have hP : ∀ o : Nat, o < 8 →
      m3[sp.toNat - 1016 + o]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[sp.toNat - 1016 + o]? := by
    intro o ho
    show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[_]? = _
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) _ (sdData_val QV) (by omega)]
  have hm3_copy : ∀ j, j < 24 → m3[(sp.toNat - 1024) + j]? = c.σ.mem[(sp.toNat - 968) + j]? := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hK 0 (by omega), show sp.toNat-1024+0 = sp.toNat-1024 from by omega,
        getElem_writeMap8_0, eK0, show sp.toNat-968+0 = sp.toNat-968 from by omega]; exact hkb0.symm
    · rw [hK 1 (by omega), getElem_writeMap8_1, eK1]; exact hkb1.symm
    · rw [hK 2 (by omega), getElem_writeMap8_2, eK2]; exact hkb2.symm
    · rw [hK 3 (by omega), getElem_writeMap8_3, eK3]; exact hkb3.symm
    · rw [hK 4 (by omega), getElem_writeMap8_4, eK4]; exact hkb4.symm
    · rw [hK 5 (by omega), getElem_writeMap8_5, eK5]; exact hkb5.symm
    · rw [hK 6 (by omega), getElem_writeMap8_6, eK6]; exact hkb6.symm
    · rw [hK 7 (by omega), getElem_writeMap8_7, eK7]; exact hkb7.symm
    · rw [show sp.toNat-1024+8 = sp.toNat-1016+0 from by omega, hP 0 (by omega),
        show sp.toNat-1016+0 = sp.toNat-1016 from by omega, getElem_writeMap8_0, eP0,
        show sp.toNat-968+8 = sp.toNat-960 from by omega]; exact hpb0.symm
    · rw [show sp.toNat-1024+9 = sp.toNat-1016+1 from by omega, hP 1 (by omega), getElem_writeMap8_1, eP1,
        show sp.toNat-968+9 = sp.toNat-960+1 from by omega]; exact hpb1.symm
    · rw [show sp.toNat-1024+10 = sp.toNat-1016+2 from by omega, hP 2 (by omega), getElem_writeMap8_2, eP2,
        show sp.toNat-968+10 = sp.toNat-960+2 from by omega]; exact hpb2.symm
    · rw [show sp.toNat-1024+11 = sp.toNat-1016+3 from by omega, hP 3 (by omega), getElem_writeMap8_3, eP3,
        show sp.toNat-968+11 = sp.toNat-960+3 from by omega]; exact hpb3.symm
    · rw [show sp.toNat-1024+12 = sp.toNat-1016+4 from by omega, hP 4 (by omega), getElem_writeMap8_4, eP4,
        show sp.toNat-968+12 = sp.toNat-960+4 from by omega]; exact hpb4.symm
    · rw [show sp.toNat-1024+13 = sp.toNat-1016+5 from by omega, hP 5 (by omega), getElem_writeMap8_5, eP5,
        show sp.toNat-968+13 = sp.toNat-960+5 from by omega]; exact hpb5.symm
    · rw [show sp.toNat-1024+14 = sp.toNat-1016+6 from by omega, hP 6 (by omega), getElem_writeMap8_6, eP6,
        show sp.toNat-968+14 = sp.toNat-960+6 from by omega]; exact hpb6.symm
    · rw [show sp.toNat-1024+15 = sp.toNat-1016+7 from by omega, hP 7 (by omega), getElem_writeMap8_7, eP7,
        show sp.toNat-968+15 = sp.toNat-960+7 from by omega]; exact hpb7.symm
    · rw [show sp.toNat-1024+16 = sp.toNat-1008 from by omega, getElem_writeMap8_0, eQ0,
        show sp.toNat-968+16 = sp.toNat-952 from by omega]; exact hqb0.symm
    · rw [show sp.toNat-1024+17 = sp.toNat-1008+1 from by omega, getElem_writeMap8_1, eQ1,
        show sp.toNat-968+17 = sp.toNat-952+1 from by omega]; exact hqb1.symm
    · rw [show sp.toNat-1024+18 = sp.toNat-1008+2 from by omega, getElem_writeMap8_2, eQ2,
        show sp.toNat-968+18 = sp.toNat-952+2 from by omega]; exact hqb2.symm
    · rw [show sp.toNat-1024+19 = sp.toNat-1008+3 from by omega, getElem_writeMap8_3, eQ3,
        show sp.toNat-968+19 = sp.toNat-952+3 from by omega]; exact hqb3.symm
    · rw [show sp.toNat-1024+20 = sp.toNat-1008+4 from by omega, getElem_writeMap8_4, eQ4,
        show sp.toNat-968+20 = sp.toNat-952+4 from by omega]; exact hqb4.symm
    · rw [show sp.toNat-1024+21 = sp.toNat-1008+5 from by omega, getElem_writeMap8_5, eQ5,
        show sp.toNat-968+21 = sp.toNat-952+5 from by omega]; exact hqb5.symm
    · rw [show sp.toNat-1024+22 = sp.toNat-1008+6 from by omega, getElem_writeMap8_6, eQ6,
        show sp.toNat-968+22 = sp.toNat-952+6 from by omega]; exact hqb6.symm
    · rw [show sp.toNat-1024+23 = sp.toNat-1008+7 from by omega, getElem_writeMap8_7, eQ7,
        show sp.toNat-968+23 = sp.toNat-952+7 from by omega]; exact hqb7.symm
  have hbufRepr : ValueRepr m3 N φcv (sp.toNat - 1024) vl :=
    valueRepr_copy_of_writeWindow (srcAddr := sp.toNat - 968) (dstAddr := sp.toNat - 1024)
      hm3_copy hm3_out
      (fun p s hp k hk => hBE.pay_disj p s hvalSub' hp k hk) hvalSub'
  ------------------------------------------------------------------------
  -- 0x80003990: jal value_truthy → PC := value_truthy entry, ra := 0x80003994
  ------------------------------------------------------------------------
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80003990_lg σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003990#64) vmi10
      hG10 hpc10 hmi10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11'
  have hmem11e : σ11.mem = m3 := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000282c#64) := by
    have := obs_jal_pc hobs11
    rwa [show ((0x80003990#64 : BitVec 64) + sign_extend (m := 64) (0x1fee9c#21)) = 0x8000282c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink11 : σ11.regs.get? Register.x1 = some (0x80003994#64) := by
    have := obs_jal_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003990#64 : BitVec 64) 4 = (0x80003994#64:BitVec 64) from by decide] at this
  have hx10_11 : σ11.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_jal_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_10'
  have hs1_11 : σ11.regs.get? Register.x9 = some sret := obs_jal_other hobs11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_10
  have hx8_11 : σ11.regs.get? Register.x8 = some aExpr := obs_jal_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_10
  have hx18_11 : σ11.regs.get? Register.x18 = some aEnv := obs_jal_other hobs11 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_10
  obtain ⟨vmi11, hmi11⟩ := obs_jal_minstret hobs11
  have hout11 : σ11.sailOutput = out0 := by rw [hobs11.out, sailOutput_sigmaPost_jal]; exact hout10
  -- Value_truthyLoaded / Value_boolLoaded at c.σ.mem
  have hVtruthy_c : Value_truthyLoaded c.σ.mem := by
    refine loaded_truthy_agreeP mcall c.σ.mem (fun a ha => ?_) hVtruthyMcall
    rcases hmemFrame a (by rw [hspsub] at *; rcases hTruthyStk with h | h <;> omega)
      (by rcases hTruthyArena with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hTruthyStk with h | h <;> omega)
    · exact heq.symm
  have hVbool_c : Value_boolLoaded c.σ.mem := by
    refine loaded_bool_agreeP mcall c.σ.mem (fun a ha => ?_) hVboolMcall
    rcases hmemFrame a (by rw [hspsub] at *; rcases hBoolStk with h | h <;> omega)
      (by rcases hBoolArena with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hBoolStk with h | h <;> omega)
    · exact heq.symm
  have hVtruthy_m3 : Value_truthyLoaded m3 :=
    loaded_truthy_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV) (by rcases hTruthyStk with h | h <;> omega)
      (loaded_truthy_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV) (by rcases hTruthyStk with h | h <;> omega)
        (loaded_truthy_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13) (by rcases hTruthyStk with h | h <;> omega) hVtruthy_c))
  have hbuftag : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) = (sp - 1024#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub]
    have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    have : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 := haddr64
    rw [this, h1024]; have := sp.isLt; omega
  have hbufNat : (sp - 1024#64 : BitVec 64).toNat = sp.toNat - 1024 := by
    rw [BitVec.toNat_sub]; have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    rw [h1024]; have := sp.isLt; omega
  have hTruthyReg : TruthyRegion (sp - 1024#64) :=
    ⟨by rw [hbufNat]; omega, by rw [hbufNat]; have := hBE.buf_lo; omega,
     by rw [hbufNat]; omega, by rw [hbufNat, htoh]; have := hBE.buf_win; rw [htoh] at this; omega⟩
  have hrettgt_t : (BitVec.update ((0x80003994#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  have hbufRepr' : ValueRepr m3 N φcv (sp - 1024#64).toNat vl := by rw [hbufNat]; exact hbufRepr
  have hx10_11' : σ11.regs.get? Register.x10 = some (sp - 1024#64) := by rw [hx10_11, hbuftag]
  ------------------------------------------------------------------------
  -- value_truthy(vl) via value_truthy_spec, buf = sp-1024, ra = 0x80003994
  ------------------------------------------------------------------------
  obtain ⟨cT, hsT, hGT, hpcT, ha0T, hraT, ⟨vmiT, hmiT⟩, htickT, hmemT, houtT, hframeT⟩ :=
    value_truthy_spec (fun R => σ11.regs.get? R) (sp - 1024#64) (0x80003994#64) N φcv vl m3 out0
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG11, hmem11e ▸ hVtruthy_m3, hmem11e, hpc11, hx10_11', hlink11, ⟨vmi11, hmi11⟩, hi11,
        hbufRepr', hTruthyReg, hrettgt_t, hout11, fun R _ => rfl⟩
  have hmemT' : cT.σ.mem = m3 := hmemT
  have hpcT' : cT.σ.regs.get? Register.PC = some (0x80003994#64) := by
    rw [hpcT, show (BitVec.update ((0x80003994#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x80003994#64 from by apply BitVec.eq_of_toNat_eq; decide]
  -- value_truthy returns a0 = cond vl.truthy 0 (falsy left → short-circuit not taken)
  have ha0T1 : cT.σ.regs.get? Register.x10 = some (0#64) := by
    rw [ha0T, hvlfalse]; rfl
  have hs1_T : cT.σ.regs.get? Register.x9 = some sret := by
    rw [hframeT Register.x9 (by decide)]; exact hs1_11
  have hsp_T : cT.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeT Register.x2 (by decide)]; exact hsp_11
  have hx8_T : cT.σ.regs.get? Register.x8 = some aExpr := by
    rw [hframeT Register.x8 (by decide)]; exact hx8_11
  have hx18_T : cT.σ.regs.get? Register.x18 = some aEnv := by
    rw [hframeT Register.x18 (by decide)]; exact hx18_11
  have hcode_T : Eval_exprLoaded cT.σ.mem := by rw [hmemT']; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x80003994: ld a3,0(sp) → reload env (dead; only need PC/regs)
  ------------------------------------------------------------------------
  have hspill0Nat : ((sp - 1088#64) + sign_extend (m := 64) (0x000#12)).toNat = sp.toNat - 1088 :=
    spill_addr sp (0x000#12) 1088 (by decide) (by omega) hsp1088
  have hStackPopM3 : ∀ a : Nat, ∃ b, m3[a]? = some b := by
    intro a
    obtain ⟨b, hb⟩ := hStackPopC a
    exact ((MemExtends.refl c.σ.mem).trans
      ((memExtends_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13)).trans
        ((memExtends_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)).trans
          (memExtends_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV))))) a b hb
  obtain ⟨eb0, heb0⟩ := hStackPopM3 (sp.toNat - 1088)
  obtain ⟨eb1, heb1⟩ := hStackPopM3 (sp.toNat - 1088 + 1)
  obtain ⟨eb2, heb2⟩ := hStackPopM3 (sp.toNat - 1088 + 2)
  obtain ⟨eb3, heb3⟩ := hStackPopM3 (sp.toNat - 1088 + 3)
  obtain ⟨eb4, heb4⟩ := hStackPopM3 (sp.toNat - 1088 + 4)
  obtain ⟨eb5, heb5⟩ := hStackPopM3 (sp.toNat - 1088 + 5)
  obtain ⟨eb6, heb6⟩ := hStackPopM3 (sp.toNat - 1088 + 6)
  obtain ⟨eb7, heb7⟩ := hStackPopM3 (sp.toNat - 1088 + 7)
  obtain ⟨σ12, i12, hs12', hi12, hG12, hmem12, hobs12⟩ :=
    site_80003994_lg cT.σ cT.tick cT.steps (0x80003994#64) vmiT (sp - 1088#64)
      eb0 eb1 eb2 eb3 eb4 eb5 eb6 eb7 hGT hpcT' hmiT hsp_T (hmemT' ▸ hcode_m3) rfl
      (by rw [hspill0Nat]; omega) (by rw [hspill0Nat]; omega)
      (by rw [hspill0Nat, htoh]; right; omega) (by rw [hspill0Nat]; omega)
      (by rw [hspill0Nat, hmemT']; exact heb0) (by rw [hspill0Nat, hmemT']; exact heb1)
      (by rw [hspill0Nat, hmemT']; exact heb2) (by rw [hspill0Nat, hmemT']; exact heb3)
      (by rw [hspill0Nat, hmemT']; exact heb4) (by rw [hspill0Nat, hmemT']; exact heb5)
      (by rw [hspill0Nat, hmemT']; exact heb6) (by rw [hspill0Nat, hmemT']; exact heb7) htickT
  have hstep12 : Step cT ⟨σ12, i12, cT.steps + 1⟩ := by cases cT; exact hs12'
  have hmem12e : σ12.mem = m3 := by rw [hmem12]; exact hmemT'
  have hpc12 : σ12.regs.get? Register.PC = some (0x80003998#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x80003994#64) 4 = (0x80003998#64 : BitVec 64) from by decide] at this
  have ha0_12 : σ12.regs.get? Register.x10 = some (0#64) := obs_alu_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0T1
  have hs1_12 : σ12.regs.get? Register.x9 = some sret := obs_alu_other hobs12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_T
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_T
  have hx8_12 : σ12.regs.get? Register.x8 = some aExpr := obs_alu_other hobs12 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_T
  have hx18_12 : σ12.regs.get? Register.x18 = some aEnv := obs_alu_other hobs12 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_T
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hout12 : σ12.sailOutput = out0 := by rw [hobs12.out, sailOutput_sigmaPost_alu]; exact houtT
  have hcode_12 : Eval_exprLoaded σ12.mem := by rw [hmem12e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x80003998: beqz a0 → TAKEN (a0 = 0) → 0x80003a00 (or-false continue)
  ------------------------------------------------------------------------
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_80003998_taken_lg σ12 i12 (cT.steps + 1) (0x80003998#64) vmi12 (0#64)
      hG12 hpc12 hmi12 ha0_12 hcode_12 rfl (by decide) hi12
  have hstep13 : Step ⟨σ12, i12, cT.steps + 1⟩ ⟨σ13, i13, cT.steps + 1 + 1⟩ := hs13'
  have hmem13e : σ13.mem = m3 := by rw [hmem13]; exact hmem12e
  have hpc13 : σ13.regs.get? Register.PC = some (0x80003a00#64) := by
    have := obs_branch_taken_pc hobs13
    rwa [site_80003998_taken_lg_tgt] at this
  have hs1_13 : σ13.regs.get? Register.x9 = some sret := obs_branch_taken_other hobs13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_taken_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_12
  have hx8_13 : σ13.regs.get? Register.x8 = some aExpr := obs_branch_taken_other hobs13 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_12
  have hx18_13 : σ13.regs.get? Register.x18 = some aEnv := obs_branch_taken_other hobs13 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_12
  obtain ⟨vmi13, hmi13⟩ := obs_branch_taken_minstret hobs13
  have hout13 : σ13.sailOutput = out0 := by rw [hobs13.out, sailOutput_sigmaPost_branch_taken]; exact hout12
  have hcode_13 : Eval_exprLoaded σ13.mem := by rw [hmem13e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- Second eval setup: ld x12,24(s0); addi x11,x18,0; addi x10,x2,0x90; jal.
  ------------------------------------------------------------------------
  -- the RIGHT-operand pointer bytes at aExpr+24 (from `read64 mcall = aRight.toNat`);
  -- transport them from mcall to c.σ.mem (node AST memory) and then to m3 (buffer disjoint).
  obtain ⟨rp0, rp1, rp2, rp3, rp4, rp5, rp6, rp7, hrp0, hrp1, hrp2, hrp3, hrp4, hrp5, hrp6, hrp7, hrpsext⟩ :=
    spill_roundtrip_ee mcall (aExpr.toNat + 24) aRight hPayRight
  have hoff24_s0 : (aExpr + sign_extend (m := 64) (0x018#12)).toNat = aExpr.toNat + 24 := by
    have hs : (sign_extend (m := 64) (0x018#12) : BitVec 64) = 24#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (24#64 : BitVec 64).toNat = 24 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  -- mcall ↔ c.σ.mem at the node-24 window (node disjoint from stack ∪ arena ∪ subsret)
  have hAgNode : ∀ k : Nat, aExpr.toNat + 24 ≤ k → k < aExpr.toNat + 32 →
      c.σ.mem[k]? = mcall[k]? := by
    intro k hk1 hk2
    rcases hmemFrame k
      (by rw [hspsub] at *; rcases hexprSL32 with h | h <;> omega)
      (by rcases hexprA32 with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hexprSub with h | h <;> omega)
    · exact heq
  -- c.σ.mem ↔ m3 at the node-24 window (node disjoint from the sp-1024 buffer)
  have hNodeM3 : ∀ k : Nat, aExpr.toNat + 24 ≤ k → k < aExpr.toNat + 32 →
      m3[k]? = c.σ.mem[k]? := by
    intro k hk1 hk2
    exact hm3_out k (by rcases hexprSub with h | h <;> omega)
  have hr24m3_0 : m3[aExpr.toNat + 24]? = some rp0 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp0)
  have hr24m3_1 : m3[aExpr.toNat + 24 + 1]? = some rp1 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp1)
  have hr24m3_2 : m3[aExpr.toNat + 24 + 2]? = some rp2 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp2)
  have hr24m3_3 : m3[aExpr.toNat + 24 + 3]? = some rp3 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp3)
  have hr24m3_4 : m3[aExpr.toNat + 24 + 4]? = some rp4 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp4)
  have hr24m3_5 : m3[aExpr.toNat + 24 + 5]? = some rp5 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp5)
  have hr24m3_6 : m3[aExpr.toNat + 24 + 6]? = some rp6 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp6)
  have hr24m3_7 : m3[aExpr.toNat + 24 + 7]? = some rp7 := (hNodeM3 _ (by omega) (by omega)).trans ((hAgNode _ (by omega) (by omega)).trans hrp7)
  -- 0x80003a00: ld x12,0x18(x8) → x12 := aRight
  obtain ⟨τ1, j1, ht1', hj1, hGτ1, hmemτ1, hoτ1⟩ :=
    site_80003a00_lg σ13 i13 (cT.steps + 1 + 1) (0x80003a00#64) vmi13 aExpr
      rp0 rp1 rp2 rp3 rp4 rp5 rp6 rp7 hG13 hpc13 hmi13 hx8_13 hcode_13 rfl
      (by rw [hoff24_s0]; omega) (by rw [hoff24_s0]; omega)
      (by rw [hoff24_s0]; right; rw [htoh] at hexprWin ⊢; omega) (by rw [hoff24_s0]; have := hexprAl; omega)
      (by rw [hoff24_s0, hmem13e]; exact hr24m3_0) (by rw [hoff24_s0, hmem13e]; exact hr24m3_1)
      (by rw [hoff24_s0, hmem13e]; exact hr24m3_2) (by rw [hoff24_s0, hmem13e]; exact hr24m3_3)
      (by rw [hoff24_s0, hmem13e]; exact hr24m3_4) (by rw [hoff24_s0, hmem13e]; exact hr24m3_5)
      (by rw [hoff24_s0, hmem13e]; exact hr24m3_6) (by rw [hoff24_s0, hmem13e]; exact hr24m3_7) hi13
  have hstepτ1 : Step ⟨σ13, i13, cT.steps + 1 + 1⟩ ⟨τ1, j1, cT.steps + 1 + 1 + 1⟩ := ht1'
  have hmemτ1e : τ1.mem = m3 := by rw [hmemτ1]; exact hmem13e
  have hpcτ1 : τ1.regs.get? Register.PC = some (0x80003a04#64) := by
    have := obs_alu_pc hoτ1
    rwa [show BitVec.addInt (0x80003a00#64) 4 = (0x80003a04#64 : BitVec 64) from by decide] at this
  have hx12τ1 : τ1.regs.get? Register.x12 = some aRight := by
    have := obs_alu_rd hoτ1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hrpsext] at this
  have hs1τ1 : τ1.regs.get? Register.x9 = some sret := obs_alu_other hoτ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_13
  have hspτ1 : τ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_13
  have hx8τ1 : τ1.regs.get? Register.x8 = some aExpr := obs_alu_other hoτ1 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_13
  have hx18τ1 : τ1.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ1 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18_13
  obtain ⟨vmiτ1, hmiτ1⟩ := obs_alu_minstret hoτ1
  have houtτ1 : τ1.sailOutput = out0 := by rw [hoτ1.out, sailOutput_sigmaPost_alu]; exact hout13
  have hcodeτ1 : Eval_exprLoaded τ1.mem := by rw [hmemτ1e]; exact hcode_m3
  -- 0x80003a04: addi x11,x18,0 → x11 := aEnv
  obtain ⟨τ2, j2, ht2', hj2, hGτ2, hmemτ2, hoτ2⟩ :=
    site_80003a04_lg τ1 j1 (cT.steps + 1 + 1 + 1) (0x80003a04#64) vmiτ1 aEnv
      hGτ1 hpcτ1 hmiτ1 hx18τ1 hcodeτ1 rfl hj1
  have hstepτ2 : Step ⟨τ1, j1, cT.steps + 1 + 1 + 1⟩ ⟨τ2, j2, cT.steps + 1 + 1 + 1 + 1⟩ := ht2'
  have hmemτ2e : τ2.mem = m3 := by rw [hmemτ2]; exact hmemτ1e
  have hpcτ2 : τ2.regs.get? Register.PC = some (0x80003a08#64) := by
    have := obs_alu_pc hoτ2
    rwa [show BitVec.addInt (0x80003a04#64) 4 = (0x80003a08#64 : BitVec 64) from by decide] at this
  have hx11τ2 : τ2.regs.get? Register.x11 = some aEnv := by
    have := obs_alu_rd hoτ2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (aEnv + sign_extend (m := 64) (0x000#12)) = aEnv from by
      apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_add]
      have : (sign_extend (m := 64) (0x000#12) : BitVec 64).toNat = 0 := by decide
      rw [this]; have := aEnv.isLt; omega] at this
  have hx12τ2 : τ2.regs.get? Register.x12 = some aRight := obs_alu_other hoτ2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ1
  have hs1τ2 : τ2.regs.get? Register.x9 = some sret := obs_alu_other hoτ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ1
  have hspτ2 : τ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ1
  have hx8τ2 : τ2.regs.get? Register.x8 = some aExpr := obs_alu_other hoτ2 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8τ1
  have hx18τ2 : τ2.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ2 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ1
  obtain ⟨vmiτ2, hmiτ2⟩ := obs_alu_minstret hoτ2
  have houtτ2 : τ2.sailOutput = out0 := by rw [hoτ2.out, sailOutput_sigmaPost_alu]; exact houtτ1
  have hcodeτ2 : Eval_exprLoaded τ2.mem := by rw [hmemτ2e]; exact hcode_m3
  -- 0x80003a08: addi x10,x2,0x90 → x10 := (sp-1088)+144 = sp-944 (sretR)
  obtain ⟨τ3, j3, ht3', hj3, hGτ3, hmemτ3, hoτ3⟩ :=
    site_80003a08_lg τ2 j2 (cT.steps + 1 + 1 + 1 + 1) (0x80003a08#64) vmiτ2 (sp - 1088#64)
      hGτ2 hpcτ2 hmiτ2 hspτ2 hcodeτ2 rfl hj2
  have hstepτ3 : Step ⟨τ2, j2, cT.steps + 1 + 1 + 1 + 1⟩ ⟨τ3, j3, cT.steps + 1 + 1 + 1 + 1 + 1⟩ := ht3'
  have hmemτ3e : τ3.mem = m3 := by rw [hmemτ3]; exact hmemτ2e
  have hpcτ3 : τ3.regs.get? Register.PC = some (0x80003a0c#64) := by
    have := obs_alu_pc hoτ3
    rwa [show BitVec.addInt (0x80003a08#64) 4 = (0x80003a0c#64 : BitVec 64) from by decide] at this
  have ha0τ3 : τ3.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) :=
    obs_alu_rd hoτ3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx11τ3 : τ3.regs.get? Register.x11 = some aEnv := obs_alu_other hoτ3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11τ2
  have hx12τ3 : τ3.regs.get? Register.x12 = some aRight := obs_alu_other hoτ3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12τ2
  have hs1τ3 : τ3.regs.get? Register.x9 = some sret := obs_alu_other hoτ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1τ2
  have hspτ3 : τ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoτ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspτ2
  have hgR3_8 : τ3.regs.get? Register.x8 = some aExpr := obs_alu_other hoτ3 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8τ2
  have hgR3_18 : τ3.regs.get? Register.x18 = some aEnv := obs_alu_other hoτ3 Register.x18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx18τ2
  obtain ⟨vmiτ3, hmiτ3⟩ := obs_alu_minstret hoτ3
  have houtτ3 : τ3.sailOutput = out0 := by rw [hoτ3.out, sailOutput_sigmaPost_alu]; exact houtτ2
  have hcodeτ3 : Eval_exprLoaded τ3.mem := by rw [hmemτ3e]; exact hcode_m3
  -- the sretR buffer address (sp-1088)+144 = sp-944
  have haddr240 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  ------------------------------------------------------------------------
  -- RIGHT recursive call via armTail_rec: subsret = sp-944, retPC = 0x80003a10.
  -- pre-call memory = m3 (the sp-1024 buffer scribble; disjoint from store/code/
  -- table/arena/right-node — so all the armTail_rec preconditions survive it).
  ------------------------------------------------------------------------
  -- m3 ↔ c.σ.mem outside the stack region [SL.lo, sp)
  have hAgM3stk : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < sp.toNat) → m3[k]? = c.σ.mem[k]? :=
    fun k hk => hm3_out k (by omega)
  -- StoreRepr m3 st'.store + survival (from the SubEvalReturn store bundle at φf'/φc')
  have hstoreM3 : StoreRepr m3 N A φf' φc' st'.store :=
    hstoreSurv' m3 (fun k hk => (hAgM3stk k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩)).symm)
  have hstoreSurvM3 : ∀ m' : Mem,
      (∀ k, ¬ (SL.lo ≤ k ∧ k < sp.toNat) →
        ¬ (sret.toNat ≤ k ∧ k < sret.toNat + 24) → m3[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store := by
    intro m' hag
    refine hstoreSurv' m' (fun k hk => ?_)
    rw [← hAgM3stk k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩)]
    exact hag k (fun ⟨ha, hb⟩ => hk ⟨ha, by omega⟩)
      (fun ⟨ha, hb⟩ => hk ⟨by omega, by omega⟩)
  -- ExprRepr m3 aRight er (right node disjoint from the buffer + stack + arena)
  have hExprM3 : ExprRepr m3 aRight.toNat er :=
    hRightSurv m3 (fun a ha1 ha2 => by
      -- mcall[a]? = c.σ.mem[a]? (hmemFrame outside sub-stack/arena/subsret)
      have e1 : mcall[a]? = c.σ.mem[a]? := by
        rcases hmemFrame a (by omega) ha2 with hin | heq
        · exact absurd hin (by omega)
        · exact heq.symm
      -- c.σ.mem[a]? = m3[a]? (buffer disjoint since a outside stack)
      rw [e1, (hm3_out a (by omega)).symm])
  -- Value_intLoaded / IntSlotPinned m3 (from mcall, through c.σ.mem, through the buffer)
  have hViInt_c : Value_intLoaded c.σ.mem := by
    refine loaded_value_int_agreeP mcall c.σ.mem (fun a ha => ?_) hViIntMcall
    rcases hmemFrame a (by rw [hspsub] at *; rcases hviStk with h | h <;> omega)
      (by rcases harenaVi with h | h <;> omega) with hin | heq
    · exact absurd hin (by rcases hviStk with h | h <;> omega)
    · exact heq.symm
  have hViInt_m3 : Value_intLoaded m3 :=
    loaded_value_int_agreeP c.σ.mem m3 (fun a ha => (hm3_out a (by rcases hviStk with h | h <;> omega)).symm) hViInt_c
  have hViSlot_c : IntSlotPinned c.σ.mem := by
    obtain ⟨q0, q1, q2, q3⟩ := hViSlotMcall
    have ag : ∀ i : Nat, i < 4 → mcall[jumpTableBase + i]? = c.σ.mem[jumpTableBase + i]? := by
      intro i hi
      rcases hmemFrame (jumpTableBase + i)
        (by simp only [jumpTableBase] at *; rw [hspsub] at *; rcases htableStk with h | h <;> omega)
        (by simp only [jumpTableBase] at harenaTable ⊢; rcases harenaTable with h | h <;> omega) with hin | heq
      · exact absurd hin (by simp only [jumpTableBase] at *; rcases htableStk with h | h <;> omega)
      · exact heq.symm
    exact ⟨(ag 0 (by omega)).symm.trans q0, (ag 1 (by omega)).symm.trans q1,
      (ag 2 (by omega)).symm.trans q2, (ag 3 (by omega)).symm.trans q3⟩
  have hViSlot_m3 : IntSlotPinned m3 := by
    obtain ⟨q0, q1, q2, q3⟩ := hViSlot_c
    have ag : ∀ i : Nat, i < 4 → m3[jumpTableBase + i]? = c.σ.mem[jumpTableBase + i]? := by
      intro i hi
      exact hm3_out (jumpTableBase + i)
        (by simp only [jumpTableBase]; rcases htableStk with h | h <;> omega)
    exact ⟨(ag 0 (by omega)).trans q0, (ag 1 (by omega)).trans q1,
      (ag 2 (by omega)).trans q2, (ag 3 (by omega)).trans q3⟩
  -- the OUTER spill slots survive into m3 (buffer stores are all below sp-1008)
  have hslotRaM3 : read64 m3 (sp.toNat - 8) = some r.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 8 ≤ k ∧ k < sp.toNat) (m := m3) (m' := c.σ.mem)
      (fun j hj => hm3_out j (by omega)) (fun j hj => by omega)]; exact hslotRa
  have hslotS0M3 : read64 m3 (sp.toNat - 16) = some v8.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 16 ≤ k ∧ k < sp.toNat - 8) (m := m3) (m' := c.σ.mem)
      (fun j hj => hm3_out j (by omega)) (fun j hj => by omega)]; exact hslotS0
  have hslotS1M3 : read64 m3 (sp.toNat - 24) = some v9.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 24 ≤ k ∧ k < sp.toNat - 16) (m := m3) (m' := c.σ.mem)
      (fun j hj => hm3_out j (by omega)) (fun j hj => by omega)]; exact hslotS1
  have hslotS2M3 : read64 m3 (sp.toNat - 32) = some v18.toNat := by
    rw [read64_agreeP (P := fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat - 24) (m := m3) (m' := c.σ.mem)
      (fun j hj => hm3_out j (by omega)) (fun j hj => by omega)]; exact hslotS2
  -- the RIGHT ghost is the post-setup register file gR3 := τ3.regs.get?. It agrees
  -- with `gpre` on every AbiPreservedNoise register (all intermediate writes are
  -- caller-saved x12/x11/x10; nothing callee-saved is touched).
  have abi_ne' : ∀ {X R : Register}, AbiPreserved X = false → AbiPreserved R = true →
      (X == R) = false := by
    intro X R hX hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hR; exact absurd hR (by decide)
  -- frame from τ3 back to `gpre` (across the whole prefix σ1..σ13 + τ1..τ3 + value_truthy)
  have hframeτ3 : ∀ R : Register, AbiPreservedNoise R → τ3.regs.get? R = gpre R := by
    intro R hR
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have hx10R : (Register.x10 == R) = false := abi_ne' (by decide) hab
    have hx11R : (Register.x11 == R) = false := abi_ne' (by decide) hab
    have hx12R : (Register.x12 == R) = false := abi_ne' (by decide) hab
    have hx13R : (Register.x13 == R) = false := abi_ne' (by decide) hab
    have hx14R : (Register.x14 == R) = false := abi_ne' (by decide) hab
    have hx15R : (Register.x15 == R) = false := abi_ne' (by decide) hab
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide) hab
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx14R hnpcR hmiiR)
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx15R hnpcR hmiiR)
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx12R hnpcR hmiiR)
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_branch_taken _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    have f5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx14R hnpcR hmiiR)
    have f6 : σ6.regs.get? R = σ5.regs.get? R :=
      (hobs6.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx15R hnpcR hmiiR)
    have f7 : σ7.regs.get? R = σ6.regs.get? R :=
      (hobs7.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx10R hnpcR hmiiR)
    have f8 : σ8.regs.get? R = σ7.regs.get? R := frame_store_v hobs8 R ⟨hx11R, hx15R, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have f9 : σ9.regs.get? R = σ8.regs.get? R := frame_store_v hobs9 R ⟨hx11R, hx15R, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have f10 : σ10.regs.get? R = σ9.regs.get? R := frame_store_v hobs10 R ⟨hx11R, hx15R, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have f11 : σ11.regs.get? R = σ10.regs.get? R :=
      (hobs11.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmiR hpcR hx1R hnpcR hmiiR)
    have fT : cT.σ.regs.get? R = σ11.regs.get? R :=
      hframeT R ⟨hx10R, hx14R, hx15R, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have f12 : σ12.regs.get? R = cT.σ.regs.get? R :=
      (hobs12.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx13R hnpcR hmiiR)
    have f13 : σ13.regs.get? R = σ12.regs.get? R :=
      (hobs13.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_branch_taken _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    have ft1 : τ1.regs.get? R = σ13.regs.get? R :=
      (hoτ1.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx12R hnpcR hmiiR)
    have ft2 : τ2.regs.get? R = τ1.regs.get? R :=
      (hoτ2.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx11R hnpcR hmiiR)
    have ft3 : τ3.regs.get? R = τ2.regs.get? R :=
      (hoτ3.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx10R hnpcR hmiiR)
    rw [ft3, ft2, ft1, f13, f12, fT, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1]
    exact hframe R hR'
  -- gpre x8/x18 witnesses (for armTail_rec's `spill_defined`)
  have hgpre8 : (∃ w, gpre Register.x8 = some w) := ⟨aExpr, hgx8⟩
  have hgpre18 : (∃ w, gpre Register.x18 = some w) := ⟨aEnv, hgx18⟩
  ------------------------------------------------------------------------
  -- RIGHT recursive call via armTail_rec (subsret = sp-944, retPC = 0x80003a10).
  ------------------------------------------------------------------------
  obtain ⟨cR, hsR, hpostR⟩ :=
    armTail_rec (fun R => τ3.regs.get? R) N A SL φf' φc' st' st'' d env er vr
      (0x80003a0c#64) (0x80003a10#64) (0x1ff758#21)
      sp r sret ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) aEnv aRight
      v8 v9 v18 out0 m3
      (by apply BitVec.eq_of_toNat_eq; simp only [evalExprEntry]; decide)
      (by apply BitVec.eq_of_toNat_eq; decide)
      (by decide)
      (fun σ i u vmi hGσ hpcσ hmiσ hcodeσ hiσ =>
        site_80003a0c_lg σ i u (0x80003a0c#64) vmi hGσ hpcσ hmiσ hcodeσ rfl hiσ)
      hIHr
      ⟨τ3, j3, cT.steps + 1 + 1 + 1 + 1 + 1⟩
      ⟨hGτ3, hj3, hpcτ3, ha0τ3, hs1τ3, hx11τ3, hx12τ3, hspτ3, ⟨vmiτ3, hmiτ3⟩,
        houtτ3, houtStr, hmemτ3e, hcode_m3, hViInt_m3, hViSlot_m3, hExprM3, hstoreM3, hstoreSurvM3,
        (fun R _ => rfl), ⟨⟨aExpr, hgR3_8⟩, ⟨aEnv, hgR3_18⟩⟩,
        hslotRaM3, hslotS0M3, hslotS1M3, hslotS2M3,
        hropAl, hropLo, hropHi, hropWin, hropStk,
        (by rw [haddr240]; omega), (by rw [haddr240]; omega), (by rw [haddr240]; omega),
        hSLloSp, hspSLhi, hsp16, hsphiRam, hSLlo, hSLhiRam, hSLwin,
        hcodeStk, hviStk, htableStk, harenaStk, harenaCode⟩
  -- unpack the RIGHT SubEvalReturn
  obtain ⟨hGR, htickR, hpcR, ha0R, hraR, hs1R, hspR, ⟨vmiR, hmiR⟩, houtR, hframeR,
    ⟨φcvR, hpcvR, hvalR⟩, hstoreBundleR, hcodeR,
    hslotRaR, hslotS0R, hslotS1R, hslotS2R, hmemFrameR, hMemExtR⟩ := hpostR
  obtain ⟨φf2, φc2, hpf2, hpc2'', hstore2', hstoreSurv2'⟩ := hstoreBundleR
  have hsub848R : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 := haddr240
  have hvalR848 : ValueRepr cR.σ.mem N φcvR (sp.toNat - 944) vr := by rw [hsub848R] at hvalR; exact hvalR
  -- Value_truthy / Value_bool loaded at cR.mem (survive the RIGHT sub-call:
  -- code region disjoint from sub-stack ∪ arena; via cR's memFrame against m3).
  have hVtruthyLoaded_cR : Value_truthyLoaded cR.σ.mem := by
    refine loaded_truthy_agreeP m3 cR.σ.mem (fun a ha => ?_) hVtruthy_m3
    rcases hmemFrameR a (by rw [hspsub] at *; rcases hTruthyStk with h | h <;> omega)
      (by rcases hTruthyArena with h | h <;> omega) with hin | heq
    · exact absurd hin (by rw [hsub848R] at *; rcases hTruthyStk with h | h <;> omega)
    · exact heq.symm
  have hVbool_m3 : Value_boolLoaded m3 :=
    loaded_bool_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV) (by rcases hBoolStk with h | h <;> omega)
      (loaded_bool_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV) (by rcases hBoolStk with h | h <;> omega)
        (loaded_bool_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13) (by rcases hBoolStk with h | h <;> omega) hVbool_c))
  have hVboolLoaded_cR : Value_boolLoaded cR.σ.mem := by
    refine loaded_bool_agreeP m3 cR.σ.mem (fun a ha => ?_) hVbool_m3
    rcases hmemFrameR a (by rw [hspsub] at *; rcases hBoolStk with h | h <;> omega)
      (by rcases hBoolArena with h | h <;> omega) with hin | heq
    · exact absurd hin (by rw [hsub848R] at *; rcases hBoolStk with h | h <;> omega)
    · exact heq.symm
  -- MemExtends m0 cR.mem (chain: m0 → mcall → c.σ.mem → m3 → cR.mem)
  have hMemExtm0cR : MemExtends m0 cR.σ.mem := by
    have hm0mcall : MemExtends m0 mcall := by
      intro a b hb
      -- m0 present ⇒ mcall present (mcall fully populated via hStackPop over agreement)
      obtain ⟨bm, hbm⟩ := hStackPop a; exact ⟨bm, hbm⟩
    have hmcall_c : MemExtends mcall c.σ.mem := hMemExt
    have hc_m3 : MemExtends c.σ.mem m3 :=
      (MemExtends.refl c.σ.mem).trans
        ((memExtends_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13)).trans
          ((memExtends_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)).trans
            (memExtends_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV))))
    exact ((hm0mcall.trans hmcall_c).trans hc_m3).trans hMemExtR
  ------------------------------------------------------------------------
  -- 0x800035b0 / b4 / b8: the three post-call loads of the rv buffer (sp-848).
  -- present bytes in cR.mem via MemExtends m3 cR.mem + m3-stackpop.
  ------------------------------------------------------------------------
  have hPopCR : ∀ a : Nat, (∃ b, cR.σ.mem[a]? = some b) := by
    intro a
    obtain ⟨b, hb⟩ := hStackPopM3 a
    exact hMemExtR a b hb
  obtain ⟨rb0, hrb0⟩ := hPopCR (sp.toNat - 944)
  obtain ⟨rb1, hrb1⟩ := hPopCR (sp.toNat - 944 + 1)
  obtain ⟨rb2, hrb2⟩ := hPopCR (sp.toNat - 944 + 2)
  obtain ⟨rb3, hrb3⟩ := hPopCR (sp.toNat - 944 + 3)
  obtain ⟨rb4, hrb4⟩ := hPopCR (sp.toNat - 944 + 4)
  obtain ⟨rb5, hrb5⟩ := hPopCR (sp.toNat - 944 + 5)
  obtain ⟨rb6, hrb6⟩ := hPopCR (sp.toNat - 944 + 6)
  obtain ⟨rb7, hrb7⟩ := hPopCR (sp.toNat - 944 + 7)
  obtain ⟨sb0, hsb0⟩ := hPopCR (sp.toNat - 936)
  obtain ⟨sb1, hsb1⟩ := hPopCR (sp.toNat - 936 + 1)
  obtain ⟨sb2, hsb2⟩ := hPopCR (sp.toNat - 936 + 2)
  obtain ⟨sb3, hsb3⟩ := hPopCR (sp.toNat - 936 + 3)
  obtain ⟨sb4, hsb4⟩ := hPopCR (sp.toNat - 936 + 4)
  obtain ⟨sb5, hsb5⟩ := hPopCR (sp.toNat - 936 + 5)
  obtain ⟨sb6, hsb6⟩ := hPopCR (sp.toNat - 936 + 6)
  obtain ⟨sb7, hsb7⟩ := hPopCR (sp.toNat - 936 + 7)
  obtain ⟨tb0, htb0⟩ := hPopCR (sp.toNat - 928)
  obtain ⟨tb1, htb1⟩ := hPopCR (sp.toNat - 928 + 1)
  obtain ⟨tb2, htb2⟩ := hPopCR (sp.toNat - 928 + 2)
  obtain ⟨tb3, htb3⟩ := hPopCR (sp.toNat - 928 + 3)
  obtain ⟨tb4, htb4⟩ := hPopCR (sp.toNat - 928 + 4)
  obtain ⟨tb5, htb5⟩ := hPopCR (sp.toNat - 928 + 5)
  obtain ⟨tb6, htb6⟩ := hPopCR (sp.toNat - 928 + 6)
  obtain ⟨tb7, htb7⟩ := hPopCR (sp.toNat - 928 + 7)
  have haddr240' : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 := haddr240
  have haddr248 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by omega) hsp1088
  have haddr256 : ((sp - 1088#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 928 :=
    spill_addr sp (0x0a0#12) 928 (by decide) (by omega) hsp1088
  -- 0x80003a10: ld x13,0x90(x2) → x13 := rv kind word
  obtain ⟨ρ1, k1, hρ1', hk1, hGρ1, hmemρ1, hoρ1⟩ :=
    site_80003a10_lg cR.σ cR.tick cR.steps (0x80003a10#64) vmiR (sp - 1088#64)
      rb0 rb1 rb2 rb3 rb4 rb5 rb6 rb7 hGR hpcR hmiR hspR hcodeR rfl
      (by rw [haddr240']; omega) (by rw [haddr240']; omega)
      (by rw [haddr240', htoh]; right; omega) (by rw [haddr240']; omega)
      (by rw [haddr240']; exact hrb0) (by rw [haddr240']; exact hrb1)
      (by rw [haddr240']; exact hrb2) (by rw [haddr240']; exact hrb3)
      (by rw [haddr240']; exact hrb4) (by rw [haddr240']; exact hrb5)
      (by rw [haddr240']; exact hrb6) (by rw [haddr240']; exact hrb7) htickR
  have hstepρ1 : Step cR ⟨ρ1, k1, cR.steps + 1⟩ := by cases cR; exact hρ1'
  have hmemρ1e : ρ1.mem = cR.σ.mem := hmemρ1
  have hpcρ1 : ρ1.regs.get? Register.PC = some (0x80003a14#64) := by
    have := obs_alu_pc hoρ1
    rwa [show BitVec.addInt (0x80003a10#64) 4 = (0x80003a14#64 : BitVec 64) from by decide] at this
  have ha3ρ1 : ρ1.regs.get? Register.x13 = some (sign_extend (m := 64)
      ((((((((rb7.append rb6).append rb5).append rb4).append rb3).append rb2).append rb1).append rb0) : BitVec (8*8))) :=
    obs_alu_rd hoρ1 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1ρ1 : ρ1.regs.get? Register.x9 = some sret := obs_alu_other hoρ1 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1R
  have hspρ1 : ρ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoρ1 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspR
  obtain ⟨vmiρ1, hmiρ1⟩ := obs_alu_minstret hoρ1
  have houtρ1 : ρ1.sailOutput = cR.σ.sailOutput := by rw [hoρ1.out, sailOutput_sigmaPost_alu]
  have hcodeρ1 : Eval_exprLoaded ρ1.mem := by rw [hmemρ1e]; exact hcodeR
  -- 0x80003a14: ld x14,0x98(x2) → x14 := rv payload word
  obtain ⟨ρ2, k2, hρ2', hk2, hGρ2, hmemρ2, hoρ2⟩ :=
    site_80003a14_lg ρ1 k1 (cR.steps + 1) (0x80003a14#64) vmiρ1 (sp - 1088#64)
      sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7 hGρ1 hpcρ1 hmiρ1 hspρ1 hcodeρ1 rfl
      (by rw [haddr248]; omega) (by rw [haddr248]; omega)
      (by rw [haddr248, htoh]; right; omega) (by rw [haddr248]; omega)
      (by rw [haddr248, hmemρ1e]; exact hsb0) (by rw [haddr248, hmemρ1e]; exact hsb1)
      (by rw [haddr248, hmemρ1e]; exact hsb2) (by rw [haddr248, hmemρ1e]; exact hsb3)
      (by rw [haddr248, hmemρ1e]; exact hsb4) (by rw [haddr248, hmemρ1e]; exact hsb5)
      (by rw [haddr248, hmemρ1e]; exact hsb6) (by rw [haddr248, hmemρ1e]; exact hsb7) hk1
  have hstepρ2 : Step ⟨ρ1, k1, cR.steps + 1⟩ ⟨ρ2, k2, cR.steps + 1 + 1⟩ := hρ2'
  have hmemρ2e : ρ2.mem = cR.σ.mem := by rw [hmemρ2]; exact hmemρ1e
  have hpcρ2 : ρ2.regs.get? Register.PC = some (0x80003a18#64) := by
    have := obs_alu_pc hoρ2
    rwa [show BitVec.addInt (0x80003a14#64) 4 = (0x80003a18#64 : BitVec 64) from by decide] at this
  have ha4ρ2 : ρ2.regs.get? Register.x14 = some (sign_extend (m := 64)
      ((((((((sb7.append sb6).append sb5).append sb4).append sb3).append sb2).append sb1).append sb0) : BitVec (8*8))) :=
    obs_alu_rd hoρ2 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha3ρ2 : ρ2.regs.get? Register.x13 = some (sign_extend (m := 64)
      ((((((((rb7.append rb6).append rb5).append rb4).append rb3).append rb2).append rb1).append rb0) : BitVec (8*8))) :=
    obs_alu_other hoρ2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3ρ1
  have hs1ρ2 : ρ2.regs.get? Register.x9 = some sret := obs_alu_other hoρ2 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1ρ1
  have hspρ2 : ρ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoρ2 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspρ1
  obtain ⟨vmiρ2, hmiρ2⟩ := obs_alu_minstret hoρ2
  have houtρ2 : ρ2.sailOutput = cR.σ.sailOutput := by rw [hoρ2.out, sailOutput_sigmaPost_alu]; exact houtρ1
  have hcodeρ2 : Eval_exprLoaded ρ2.mem := by rw [hmemρ2e]; exact hcodeR
  -- 0x80003a18: ld x15,0xa0(x2) → x15 := rv[16..24) word
  obtain ⟨ρ3, k3, hρ3', hk3, hGρ3, hmemρ3, hoρ3⟩ :=
    site_80003a18_lg ρ2 k2 (cR.steps + 1 + 1) (0x80003a18#64) vmiρ2 (sp - 1088#64)
      tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 hGρ2 hpcρ2 hmiρ2 hspρ2 hcodeρ2 rfl
      (by rw [haddr256]; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, htoh]; right; omega) (by rw [haddr256]; omega)
      (by rw [haddr256, hmemρ2e]; exact htb0) (by rw [haddr256, hmemρ2e]; exact htb1)
      (by rw [haddr256, hmemρ2e]; exact htb2) (by rw [haddr256, hmemρ2e]; exact htb3)
      (by rw [haddr256, hmemρ2e]; exact htb4) (by rw [haddr256, hmemρ2e]; exact htb5)
      (by rw [haddr256, hmemρ2e]; exact htb6) (by rw [haddr256, hmemρ2e]; exact htb7) hk2
  have hstepρ3 : Step ⟨ρ2, k2, cR.steps + 1 + 1⟩ ⟨ρ3, k3, cR.steps + 1 + 1 + 1⟩ := hρ3'
  have hmemρ3e : ρ3.mem = cR.σ.mem := by rw [hmemρ3]; exact hmemρ2e
  have hpcρ3 : ρ3.regs.get? Register.PC = some (0x80003a1c#64) := by
    have := obs_alu_pc hoρ3
    rwa [show BitVec.addInt (0x80003a18#64) 4 = (0x80003a1c#64 : BitVec 64) from by decide] at this
  have ha5ρ3 : ρ3.regs.get? Register.x15 = some (sign_extend (m := 64)
      ((((((((tb7.append tb6).append tb5).append tb4).append tb3).append tb2).append tb1).append tb0) : BitVec (8*8))) :=
    obs_alu_rd hoρ3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have ha3ρ3 : ρ3.regs.get? Register.x13 = some (sign_extend (m := 64)
      ((((((((rb7.append rb6).append rb5).append rb4).append rb3).append rb2).append rb1).append rb0) : BitVec (8*8))) :=
    obs_alu_other hoρ3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3ρ2
  have ha4ρ3 : ρ3.regs.get? Register.x14 = some (sign_extend (m := 64)
      ((((((((sb7.append sb6).append sb5).append sb4).append sb3).append sb2).append sb1).append sb0) : BitVec (8*8))) :=
    obs_alu_other hoρ3 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4ρ2
  have hs1ρ3 : ρ3.regs.get? Register.x9 = some sret := obs_alu_other hoρ3 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1ρ2
  have hspρ3 : ρ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other hoρ3 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspρ2
  obtain ⟨vmiρ3, hmiρ3⟩ := obs_alu_minstret hoρ3
  have houtρ3 : ρ3.sailOutput = cR.σ.sailOutput := by rw [hoρ3.out, sailOutput_sigmaPost_alu]; exact houtρ2
  have hcodeρ3 : Eval_exprLoaded ρ3.mem := by rw [hmemρ3e]; exact hcodeR
  ------------------------------------------------------------------------
  -- 0x80003a1c: j 0x800035bc → join the shared tail (ρ4, jump_x0; regs preserved).
  ------------------------------------------------------------------------
  obtain ⟨ρ4, k4, hρ4', hk4, hGρ4, hmemρ4, hoρ4⟩ :=
    site_80003a1c_lg ρ3 k3 (cR.steps + 1 + 1 + 1) (0x80003a1c#64) vmiρ3
      hGρ3 hpcρ3 hmiρ3 hcodeρ3 rfl
      (by rw [show ((0x80003a1c#64:BitVec 64) + sign_extend (m := 64) (0x1ffba0#21)) = 0x800035bc#64 from by
            apply BitVec.eq_of_toNat_eq; decide]; decide) hk3
  have hstepρ4 : Step ⟨ρ3, k3, cR.steps + 1 + 1 + 1⟩ ⟨ρ4, k4, cR.steps + 1 + 1 + 1 + 1⟩ := hρ4'
  have hmemρ4e : ρ4.mem = cR.σ.mem := by rw [hmemρ4]; exact hmemρ3e
  have hpcρ4 : ρ4.regs.get? Register.PC = some (0x800035bc#64) := by
    have := obs_jr_pc hoρ4
    rwa [show ((0x80003a1c#64:BitVec 64) + sign_extend (m := 64) (0x1ffba0#21)) = 0x800035bc#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have ha3ρ4 : ρ4.regs.get? Register.x13 = some (sign_extend (m := 64)
      ((((((((rb7.append rb6).append rb5).append rb4).append rb3).append rb2).append rb1).append rb0) : BitVec (8*8))) :=
    obs_jr_other hoρ4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3ρ3
  have ha4ρ4 : ρ4.regs.get? Register.x14 = some (sign_extend (m := 64)
      ((((((((sb7.append sb6).append sb5).append sb4).append sb3).append sb2).append sb1).append sb0) : BitVec (8*8))) :=
    obs_jr_other hoρ4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4ρ3
  have ha5ρ4 : ρ4.regs.get? Register.x15 = some (sign_extend (m := 64)
      ((((((((tb7.append tb6).append tb5).append tb4).append tb3).append tb2).append tb1).append tb0) : BitVec (8*8))) :=
    obs_jr_other hoρ4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5ρ3
  have hs1ρ4 : ρ4.regs.get? Register.x9 = some sret := obs_jr_other hoρ4 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1ρ3
  have hspρ4 : ρ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other hoρ4 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hspρ3
  obtain ⟨vmiρ4, hmiρ4⟩ := obs_jr_minstret hoρ4
  have houtρ4 : ρ4.sailOutput = cR.σ.sailOutput := by rw [hoρ4.out, sailOutput_sigmaPost_jump_x0]; exact houtρ3
  have hcodeρ4 : Eval_exprLoaded ρ4.mem := by rw [hmemρ4e]; exact hcodeR
  ------------------------------------------------------------------------
  -- package `LogTailPre` at ρ4 (PC 0x800035bc, rv at sretR = sp-944, words
  -- in a3/a4/a5) and apply `blockC_logTail`.
  ------------------------------------------------------------------------
  -- the sretR buffer bytes at ρ4.mem = cR.mem (the a3/a4/a5 words sign-extend them)
  have hsretRnat : (sp - 944#64 : BitVec 64).toNat = sp.toNat - 944 := by
    rw [BitVec.toNat_sub]; have h944 : (944#64 : BitVec 64).toNat = 944 := by decide
    rw [h944]; have := sp.isLt; omega
  -- The rv value at sp-944 = (sp-944#64).toNat
  -- transport the RIGHT value to the STORE map φc2 (agree with φcvR on closures.size)
  -- both φcvR and φc2 extend the RIGHT-call entry map φc' over st''.closures.size.
  have hφagree : ∀ i, i < st''.store.closures.size → φcvR i = φc2 i := by
    intro i hi; rw [hpcvR i hi, hpc2'' i hi]
  have hvalRφc2 : ValueRepr cR.σ.mem N φc2 (sp.toNat - 944) vr :=
    hVrMapCoh cR.σ.mem φcvR φc2 hφagree hvalR848
  have hvalRbuf : ValueRepr cR.σ.mem N φc2 (sp - 944#64).toNat vr := by rw [hsretRnat]; exact hvalRφc2
  -- payload-disjointness for the copy at logTail: rv's payload at sretR+8 vs sp-1024 buffer
  have hpayDisjR : ∀ (p : Nat) (s : String),
      read64 cR.σ.mem ((sp - 944#64).toNat + 8) = some p →
      ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k) := by
    intro p s hp k hk
    rw [hsretRnat] at hp
    exact hPayDisjRight cR.σ.mem φc2 p s hvalRφc2 hp k hk
  ------------------------------------------------------------------------
  -- callee-saved frame from ρ4 back to `g`: ρ4 → gpre (via τ3 = gpre through the
  -- RIGHT sub-call's frame, then the ρ-loads + join `j`), then gpre → g (the bridge).
  ------------------------------------------------------------------------
  have abi_ne2 : ∀ {X : Register}, AbiPreserved X = false → ∀ {R : Register},
      AbiPreservedNoise R → (X == R) = false := by
    intro X hX R hR
    obtain ⟨hab, _, _, _, _, _, _, _⟩ := hR
    rcases hXR : (X == R) with _ | _
    · rfl
    · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
  have hframeρ4 : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      ρ4.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpcR, hnpcR, hmiR, hmiiR, hmcR, hmtR, hmipR⟩
    have hx13R : (Register.x13 == R) = false := abi_ne2 (by decide) hR'
    have hx14R : (Register.x14 == R) = false := abi_ne2 (by decide) hR'
    have hx15R : (Register.x15 == R) = false := abi_ne2 (by decide) hR'
    -- ρ1/ρ2/ρ3: ld a3/a4/a5 (write x13/x14/x15); ρ4: j (jump_x0, no write)
    have fρ1 : ρ1.regs.get? R = cR.σ.regs.get? R :=
      (hoρ1.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx13R hnpcR hmiiR)
    have fρ2 : ρ2.regs.get? R = ρ1.regs.get? R :=
      (hoρ2.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx14R hnpcR hmiiR)
    have fρ3 : ρ3.regs.get? R = ρ2.regs.get? R :=
      (hoρ3.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_alu _ _ _ _ _ R hmiR hpcR hx15R hnpcR hmiiR)
    have fρ4 : ρ4.regs.get? R = ρ3.regs.get? R :=
      (hoρ4.1 R hmcR hmtR hmipR).trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmiR hpcR hnpcR hmiiR)
    -- cR → τ3 = gpre (the RIGHT sub-call restores AbiPreservedNoise regs to its ghost τ3)
    have fR : cR.σ.regs.get? R = (fun R => τ3.regs.get? R) R := hframeR R hR'
    rw [fρ4, fρ3, fρ2, fρ1, fR]
    -- τ3.regs.get? R = gpre R (hframeτ3), then gpre R = g R (hbridge)
    exact (hframeτ3 R hR').trans (hbridge R hR' he8 he9 he18 he2)
  -- store bundle re-represented for st'' at ρ3.mem = cR.mem (from the RIGHT SubEvalReturn)
  -- spill slots survive into cR.mem (from the RIGHT SubEvalReturn) and ρ-loads (no writes)
  -- Build the LogTailPre and apply blockC_logTail.
  obtain ⟨cFin, hsFin, mpreFin, hPreFin⟩ :=
    blockC_logTail g N A SL φf2 φc2 st'' vr sp r sret (sp - 944#64)
      rb0 rb1 rb2 rb3 rb4 rb5 rb6 rb7 sb0 sb1 sb2 sb3 sb4 sb5 sb6 sb7
      tb0 tb1 tb2 tb3 tb4 tb5 tb6 tb7 v8 v9 v18 cR.σ.sailOutput m0
      ⟨ρ4, k4, cR.steps + 1 + 1 + 1 + 1⟩
      { good := hGρ4
        tick := hk4
        pc := hpcρ4
        s1 := hs1ρ4
        sp2 := hspρ4
        a3 := ha3ρ4
        a4 := ha4ρ4
        a5 := ha5ρ4
        minstret := ⟨vmiρ4, hmiρ4⟩
        out := houtρ4
        outStr := houtR -- OutRepr cR st'' → String.join cR.sailOutput = st''.out
        code := hcodeρ4
        truthyLoaded := by rw [hmemρ4e]; exact hVtruthyLoaded_cR
        boolLoaded := by rw [hmemρ4e]; exact hVboolLoaded_cR
        vrepr := by rw [hmemρ4e, hsretRnat]; exact hvalRφc2
        bK0 := by rw [hmemρ4e, hsretRnat]; exact hrb0
        bK1 := by rw [hmemρ4e, hsretRnat]; exact hrb1
        bK2 := by rw [hmemρ4e, hsretRnat]; exact hrb2
        bK3 := by rw [hmemρ4e, hsretRnat]; exact hrb3
        bK4 := by rw [hmemρ4e, hsretRnat]; exact hrb4
        bK5 := by rw [hmemρ4e, hsretRnat]; exact hrb5
        bK6 := by rw [hmemρ4e, hsretRnat]; exact hrb6
        bK7 := by rw [hmemρ4e, hsretRnat]; exact hrb7
        bP0 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 = sp.toNat - 936 from by omega]; exact hsb0
        bP1 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 1 = sp.toNat - 936 + 1 from by omega]; exact hsb1
        bP2 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 2 = sp.toNat - 936 + 2 from by omega]; exact hsb2
        bP3 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 3 = sp.toNat - 936 + 3 from by omega]; exact hsb3
        bP4 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 4 = sp.toNat - 936 + 4 from by omega]; exact hsb4
        bP5 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 5 = sp.toNat - 936 + 5 from by omega]; exact hsb5
        bP6 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 6 = sp.toNat - 936 + 6 from by omega]; exact hsb6
        bP7 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 8 + 7 = sp.toNat - 936 + 7 from by omega]; exact hsb7
        bQ0 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 = sp.toNat - 928 from by omega]; exact htb0
        bQ1 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 1 = sp.toNat - 928 + 1 from by omega]; exact htb1
        bQ2 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 2 = sp.toNat - 928 + 2 from by omega]; exact htb2
        bQ3 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 3 = sp.toNat - 928 + 3 from by omega]; exact htb3
        bQ4 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 4 = sp.toNat - 928 + 4 from by omega]; exact htb4
        bQ5 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 5 = sp.toNat - 928 + 5 from by omega]; exact htb5
        bQ6 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 6 = sp.toNat - 928 + 6 from by omega]; exact htb6
        bQ7 := by rw [hmemρ4e, hsretRnat, show sp.toNat - 944 + 16 + 7 = sp.toNat - 928 + 7 from by omega]; exact htb7
        payDisj := by
          intro p s hp k hk
          rw [hmemρ4e, hsretRnat] at hp
          exact hpayDisjR p s (by rw [hsretRnat]; exact hp) k hk
        store := by rw [hmemρ4e]; exact hstore2'
        storeSurv := by
          intro m' hag
          rw [hmemρ4e] at hag
          exact hstoreSurv2' m' hag
        slotRa := by rw [hmemρ4e]; exact hslotRaR
        slotS0 := by rw [hmemρ4e]; exact hslotS0R
        slotS1 := by rw [hmemρ4e]; exact hslotS1R
        slotS2 := by rw [hmemρ4e]; exact hslotS2R
        gv8 := hgv8
        gv9 := hgv9
        gv18 := hgv18
        gv2 := hgv2
        frame := hframeρ4
        memFrame := by
          rw [hmemρ4e]
          intro a ha hA
          -- a outside stack ⇒ outside [sp-848,+24) ⊂ stack; take the m0 branch.
          refine Or.inr ?_
          rcases hmemFrameR a (by rw [hspsub] at *; omega) hA with hin | heq
          · exact absurd hin (by rw [hsub848R] at *; omega)
          · rw [heq]
            rw [hAgM3stk a (by omega)]
            rcases hmemFrame a (by omega) hA with hin2 | heq2
            · exact absurd hin2 (by omega)
            · rw [heq2]; exact hMcallM0 a ha hA
        memExt := by rw [hmemρ4e]; exact hMemExtm0cR
        bufLo := by have := hBE.buf_lo; omega
        bufWin := by have := hBE.buf_win; rw [htoh] at this ⊢; omega
        sretAl := hsretAl
        sretLo := hsretLo
        sretHi := hsretHi
        sretWin := hsretWin
        sretStk := hsretStk
        sretBoolCode := hSretBoolCode
        sretInSL := hsretInSL
        sretEvalCode := hsretEvalCode
        raAl := hraAl
        spSLhi := hspSLhi
        spRam := hsphiRam
        sp8 := hsp8
        SLhiRam := hSLhiRam
        SLlo := hSLlo
        SLwin := hSLwin
        spLo := by omega
        SLloSp := by omega
        truthyStk := hTruthyStk
        boolStk := hBoolStk
        codeStk := hcodeStk }
  ------------------------------------------------------------------------
  -- assemble: total Steps chain + PhiExtends witnesses + PreEpilogueVD.
  ------------------------------------------------------------------------
  have hSteps : Steps c cFin := by
    refine (Steps.single hstep1).trans (?_)
    refine (Steps.single hstep2).trans (?_)
    refine (Steps.single hstep3).trans (?_)
    refine (Steps.single hstep4).trans (?_)
    refine (Steps.single hstep5).trans (?_)
    refine (Steps.single hstep6).trans (?_)
    refine (Steps.single hstep7).trans (?_)
    refine (Steps.single hstep8).trans (?_)
    refine (Steps.single hstep9).trans (?_)
    refine (Steps.single hstep10).trans (?_)
    refine (Steps.single hstep11).trans (?_)
    refine hsT.trans (?_)
    refine (Steps.single hstep12).trans (?_)
    refine (Steps.single hstep13).trans (?_)
    refine (Steps.single hstepτ1).trans (?_)
    refine (Steps.single hstepτ2).trans (?_)
    refine (Steps.single hstepτ3).trans (?_)
    refine hsR.trans (?_)
    refine (Steps.single hstepρ1).trans (?_)
    refine (Steps.single hstepρ2).trans (?_)
    refine (Steps.single hstepρ3).trans (?_)
    refine (Steps.single hstepρ4).trans (?_)
    exact hsFin
  -- compose the two-phase φ-chain to the OUTER maps via size stability.
  have hpf'' : PhiExtends φf φf' st''.store.frames.size := hSizeF ▸ hpf'
  have hpc''' : PhiExtends φc φc' st''.store.closures.size := hSizeC ▸ hpc'
  have hpfF : PhiExtends φf φf2 st''.store.frames.size := hpf''.trans hpf2
  have hpcF : PhiExtends φc φc2 st''.store.closures.size := hpc'''.trans hpc2''
  exact ⟨cFin, hSteps, mpreFin, φf2, φc2, cR.σ.sailOutput, hpfF, hpcF, hPreFin⟩

/-! ## `OrFalseExtras` — the two-eval recursive-case facts

Mirrors `OrTrueExtras` (same arm PC, slot, LEFT-operand geometry) plus the
RIGHT-operand fields the second eval needs (offset 24, its `ExprRepr`-survival
and geometry, and the RIGHT-value payload/map residuals for `blockC_logTail`). -/
structure OrFalseExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (st' st'' : Vsa.While.St)
    (el er : Expr) (vl vr : Value)
    (sp sret aExpr aLeft aRight : BitVec 64)
    (m0 : Mem) : Prop where
  slot7 : KindSlotPinned 7 (0x8000355c#64) m0
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.logical .or el er)
  left_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aLeft.toNat el
  right_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) → m0[a]? = m'[a]?) →
    ExprRepr m' aRight.toNat er
  pay : read64 m0 (aExpr.toNat + 16) = some aLeft.toNat
  pay_right : read64 m0 (aExpr.toNat + 24) = some aRight.toNat
  expr24 : aExpr.toNat + 24 ≤ 0x100000000
  expr32 : aExpr.toNat + 32 ≤ 0x100000000
  expr24_stk : aExpr.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  expr32_stk : aExpr.toNat + 32 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  op_align : aLeft.toNat % 8 = 0
  op_lo : 0x80000000 ≤ aLeft.toNat
  op_hi : aLeft.toNat + 16 ≤ 0x100000000
  op_win : tohostAddr + 16 ≤ aLeft.toNat
  op_stk : aLeft.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aLeft.toNat
  rop_align : aRight.toNat % 8 = 0
  rop_lo : 0x80000000 ≤ aRight.toNat
  rop_hi : aRight.toNat + 16 ≤ 0x100000000
  rop_win : tohostAddr + 16 ≤ aRight.toNat
  rop_stk : aRight.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aRight.toNat
  sp_headroom : SL.lo + 3264 ≤ sp.toNat
  sp_SLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhi_ram : SL.hi ≤ 0x100000000
  code_stk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  vicode_stk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c
  table_stk : (0x80019f58 : Nat) + 44 ≤ SL.lo ∨ sp.toNat ≤ (0x80019f58 : Nat)
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  arena_vi : A.hi ≤ 0x8000280c ∨ 0x8000281c ≤ A.lo
  arena_table : A.hi ≤ jumpTableBase ∨ jumpTableBase + 4 ≤ A.lo
  expr_align4 : aExpr.toNat % 8 = 0
  expr_win8 : tohostAddr + 8 ≤ aExpr.toNat
  expr_A : aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  expr_A32 : aExpr.toNat + 32 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  expr_sub : aExpr.toNat + 16 ≤ sp.toNat - 968 ∨ sp.toNat - 968 + 24 ≤ aExpr.toNat
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  truthy_loaded : Value_truthyLoaded m0
  bool_loaded : Value_boolLoaded m0
  int_loaded : Value_intLoaded m0
  intslot : IntSlotPinned m0
  truthy_stk : sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo
  boolcode_stk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo
  sret_boolcode : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat
  truthy_arena : A.hi ≤ 0x8000282c ∨ 0x8000285c ≤ A.lo
  bool_arena : A.hi ≤ 0x800027f8 ∨ 0x8000280c ≤ A.lo
  pay_disj : ∀ (m : Mem) (φc' : Addr → Nat) (p : Nat) (s : String),
    ValueRepr m N φc' (sp.toNat - 968) vl → read64 m (sp.toNat - 968 + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)
  pay_disj_right : ∀ (mR : Mem) (φ : Addr → Nat) (p : Nat) (s : String),
    ValueRepr mR N φ (sp.toNat - 944) vr → read64 mR (sp.toNat - 944 + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)
  vr_map_coh : ∀ (mR : Mem) (φa φb : Addr → Nat),
    (∀ i, i < st''.store.closures.size → φa i = φb i) →
    ValueRepr mR N φa (sp.toNat - 944) vr → ValueRepr mR N φb (sp.toNat - 944) vr
  size_frames : st'.store.frames.size = st''.store.frames.size
  size_closures : st'.store.closures.size = st''.store.closures.size

/-! ## `EvalOrFalseSimGoal` — the `EvalE.orFalse` (two-eval) projection

In the `EvalIH` motive shape with TWO IH premises (LEFT `el`, RIGHT `er`). The
spec's `orFalse` constructor: `l` falsy, then `r` yields `vr`, producing
`.bool vr.truthy`. Conditional ONLY on `OrFalseExtras`, `hMcallPop`, and the
same `x13`-survival residual as `evalOrSim`/`evalAndTrueSim`. -/
def EvalOrFalseSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' st'' : Vsa.While.St) (d : Nat) (env : Addr) (el er : Expr) (vl vr : Value)
    (sp r sret aEnv aExpr aLeft aRight aEnv3 : BitVec 64)
    (m0 : Mem),
    vl.truthy = false →
    EvalIH st d env el st' vl →
    EvalIH st' d env er st'' vr →
    EvalE st d env (.logical .or el er) st'' (.bool vr.truthy) →
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.logical .or el er) sp r sret aEnv aExpr m0 c ∧
        OrFalseExtras N A SL st' st'' el er vl vr sp sret aExpr aLeft aRight m0 ∧
        (∀ cm : Config, Steps c cm →
          cm.σ.regs.get? Register.PC = some (0x8000355c#64) →
          cm.σ.regs.get? Register.x13 = some aEnv3) ∧
        (∀ mcall : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
          ∀ a : Nat, ∃ b, mcall[a]? = some b))
      (EvalExitD g N A SL φf φc st'' (.bool vr.truthy) sp r sret m0)

/-- **`evalOrFalseSim`** — the `EvalE.orFalse` (two-eval) recursive case, in the
`EvalIH` motive shape with TWO IH premises. Composes `blockA_k` (prologue+dispatch
→ widened `ArmEntryK` @0x8000355c), `blockB_logical` (arm head + LEFT recursive
call ⋈ `hIH` → `SubEvalReturn @0x8000356c`), `blockC_orFalse` (post-call two-eval
tail: op-dispatch + value_truthy(vl) + beqz-taken + RIGHT eval ⋈ `hIHr` +
`blockC_logTail` → `PreEpilogueVD .bool vr.truthy`), and `blockD_v_rec` (shared
epilogue → `EvalExitD`). Mirrors `evalAndTrueSim`, with the second IH. -/
theorem evalOrFalseSim : EvalOrFalseSimGoal := by
  intro g N A SL φf φc st st' st'' d env el er vl vr sp r sret aEnv aExpr aLeft aRight aEnv3
    m0 hvlfalse hIH hIHr _hEvalE
  intro c ⟨hc, hx, hx13reach, hMcallPop⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x8000355c ===
  have hkm0 : read32 m0 aExpr.toNat = some 7 := exprRepr_logical_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st (.logical .or el er) 7 (0x8000355c#64) LogicalArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot7
      ⟨hx.int_loaded, hx.intslot, hx.truthy_loaded, hx.bool_loaded⟩
      (fun mem a8 dd hlo hhi hcl =>
        logicalCallee_writeMap8 mem a8 dd
          (by have := hx.vicode_stk; omega)
          (by simp only [jumpTableBase]; have := hx.table_stk; omega)
          (by have := hx.truthy_stk; omega)
          (by have := hx.boolcode_stk; omega) hcl)
      (fun m' hag => hx.expr_survives m' hag)
      (by decide)
      (by have := hx.table_stk; simp only [jumpTableBase]; omega)
      c ⟨⟨hc.good, hc.tick, hc.pc, hc.a0, hc.a1, hc.a2, hc.ra, hc.ra_align, hc.spReg,
        hc.stackOK, hc.minstret, hc.mem, hc.code, hc.expr, hc.store, hc.store_survives, hc.out,
        hc.frame, hc.code_stack_disjoint, hc.expr_stack_disjoint, hc.expr_align, hc.expr_ram,
        hc.expr_win, hc.sret_align, hc.sret_ram, hc.sret_win, hc.sret_vicode_disjoint,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hc.stack_ram, hc.stack_win,
        hc.spill_defined⟩, rfl⟩
  have hArmCopy := hArm
  obtain ⟨_hAG, _hAtick, hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
  have hx13c1 : c1.σ.regs.get? Register.x13 = some aEnv3 := hx13reach c1 hs1 hApc
  have hgpreframe : ∀ R : Register, AbiPreservedNoise R →
      c1.σ.regs.get? R = (fun R => c1.σ.regs.get? R) R := fun R _ => rfl
  have hgpre_x8 : (fun R => c1.σ.regs.get? R) Register.x8 = some aExpr := hAEx8
  have hgpre18 : ∃ w, (fun R => c1.σ.regs.get? R) Register.x18 = some w := ⟨aEnv, hAEx18⟩
  have hbridge : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      (fun R => c1.σ.regs.get? R) R = g R :=
    fun R hR he8 he9 he18 he2 => hArmFrame R hR he8 he9 he18 he2
  have hMentM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ment[a]? = m0[a]? := hArmMemM0
  have hExprMent : ExprRepr ment aExpr.toNat (.logical .or el er) :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨lp, rp, hk7m, hopTok, hlptrM, hlRM, hrptrM, hrRM⟩ : ∃ lp rp,
      read32 ment aExpr.toNat = some 7 ∧
      read32 ment (aExpr.toNat + 8) = some (logOpTok .or) ∧
      read64 ment (aExpr.toNat + 16) = some lp ∧ ExprRepr ment lp el ∧
      read64 ment (aExpr.toNat + 24) = some rp ∧ ExprRepr ment rp er := by
    cases hExprMent with | logical hk htok hl hlp hr hrp => exact ⟨_, _, hk, htok, hl, hlp, hr, hrp⟩
  have hlptrM' : read64 ment (aExpr.toNat + 16) = some aLeft.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aLeft.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  -- === block B: arm head + LEFT recursive call ⋈ IH → SubEvalReturn @0x8000356c ===
  obtain ⟨c2, hs2, hSub⟩ :=
    blockB_logical g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .or el er vl
      sp r sret aExpr aEnv aLeft aEnv3 v8 v9 v18 c.σ.sailOutput m0 hIH
      c1 ⟨ment, hArm, hx11c1, hx13c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hlptrM',
        (fun m' hag => hx.left_survives m' (fun a ha => (hMentM0 a ha).symm.trans (hag a ha))),
        hx.expr24,
        hx.op_align, hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega),
        hx.arena_stk, hx.arena_code⟩
  obtain ⟨mcall, hSubR, hMcallM0stk⟩ := hSub
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  have hVtruthyMcall : Value_truthyLoaded mcall :=
    loaded_truthy_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded
  have hVboolMcall : Value_boolLoaded mcall :=
    loaded_bool_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded
  have hViIntMcall : Value_intLoaded mcall :=
    loaded_value_int_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.vicode_stk; omega)).symm) hx.int_loaded
  have hViSlotMcall : IntSlotPinned mcall := by
    obtain ⟨q0, q1, q2, q3⟩ := hx.intslot
    have ag : ∀ i : Nat, i < 4 → m0[jumpTableBase + i]? = mcall[jumpTableBase + i]? :=
      fun i hi => (hAgM0 (jumpTableBase + i)
        (by simp only [jumpTableBase]; have := hx.table_stk; omega)).symm
    exact ⟨(ag 0 (by omega)).symm.trans q0, (ag 1 (by omega)).symm.trans q1,
      (ag 2 (by omega)).symm.trans q2, (ag 3 (by omega)).symm.trans q3⟩
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hStackPop : ∀ a : Nat, ∃ b, mcall[a]? = some b := hMcallPop mcall hAgM0
  have hExprMcall : ExprRepr mcall aExpr.toNat (.logical .or el er) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  have hPayRightMcall : read64 mcall (aExpr.toNat + 24) = some aRight.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 24) aRight.toNat hx.pay_right
    have hstk := hx.expr32_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [(hAgM0 (aExpr.toNat + 24) (by omega)), (hAgM0 (aExpr.toNat + 24 + 1) (by omega)),
        (hAgM0 (aExpr.toNat + 24 + 2) (by omega)), (hAgM0 (aExpr.toNat + 24 + 3) (by omega)),
        (hAgM0 (aExpr.toNat + 24 + 4) (by omega)), (hAgM0 (aExpr.toNat + 24 + 5) (by omega)),
        (hAgM0 (aExpr.toNat + 24 + 6) (by omega)), (hAgM0 (aExpr.toNat + 24 + 7) (by omega)),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hRightSurvMcall : ∀ m' : Mem,
      (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
        mcall[a]? = m'[a]?) → ExprRepr m' aRight.toNat er :=
    fun m' hag => hx.right_survives m'
      (fun a ha1 ha2 => (hAgM0 a ha1).symm.trans (hag a ha1 ha2))
  have hBufExtras : ∀ φc' : Addr → Nat, ValueRepr c2.σ.mem N φc' (sp.toNat - 968) vl →
      LogicalBufExtras N A SL φc' vl sp sret c2.σ.mem := by
    intro φc' hvr
    exact ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),
      (by have := hx.sp_headroom; omega),
      (fun p s hvr' hp k hk => hx.pay_disj c2.σ.mem φc' p s hvr' hp k hk)⟩
  -- === block C: post-call two-eval tail → PreEpilogueVD .bool vr.truthy @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, outF, hpfe, hpce, hPreD⟩ :=
    blockC_orFalse (fun R => c1.σ.regs.get? R) g N A SL φf φc st' st'' d env vl vr
      sp r sret aExpr aEnv aRight v8 v9 v18 c2.σ.sailOutput el er m0 hvlfalse hIHr
      hx.size_frames hx.size_closures
      c2 ⟨mcall, hSubR, hgpre_x8, hAEx18, hExprMcall, hPayRightMcall, hStackPop,
        hx.expr_align4, hc.expr_ram.1, hc.expr_ram.2, hx.expr32, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr32_stk, hx.expr_A, hx.expr_A32, hx.expr_sub,
        hRightSurvMcall, hx.rop_align, hx.rop_lo, hx.rop_hi, hx.rop_win, hx.rop_stk,
        hx.pay_disj_right, hx.vr_map_coh,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint, hx.sret_boolcode,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVtruthyMcall, hVboolMcall, hViIntMcall, hViSlotMcall, hBufExtras,
        hx.truthy_stk, hx.boolcode_stk, hx.truthy_arena, hx.bool_arena,
        hx.code_stk, (by have := hx.vicode_stk; omega), (by have := hx.table_stk; omega),
        hx.arena_stk, hx.arena_code, hx.arena_vi, hx.arena_table, hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.sp16, hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge⟩
  -- === block D: shared epilogue → EvalExitD .bool vr.truthy (via blockD_v_rec) ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st'' (.bool vr.truthy) sp r sret v8 v9 v18 outF m0
      c3 ⟨mpreC, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hExit : EvalExit g N A SL φf φc st'' (.bool vr.truthy) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE
  exact ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, hExit, hMemExt,
    φf', φc', hpfe.trans hpf', hpce.trans hpc', hSurv⟩

end Vsa.Sim
