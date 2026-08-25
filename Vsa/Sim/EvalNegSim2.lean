import Vsa.Sim.EvalNegSim
import Vsa.Sim.NegTailSites
import Vsa.Sim.NegBlockProto
import Vsa.Sim.BlockAdapter
import Vsa.Sim.ValueSpec
import Vsa.Sim.DivSites2

/-!
# Layer 4 — M4 pilot RECURSIVE case: the `neg` post-call tail (`blockC_neg`)

Continues `EvalNegSim.lean` (`blockB_unary`, ending in `SubEvalReturn … 0x800035ec`):
the `neg`-op post-call tail of the `EX_UNARY` arm. Machine path
(`experiments/pctrace.md`):

```
800035ec: lw   a4,8(s0)        # op token (s0 = caller Expr node = aExpr)
800035f0: li   a5,12           # T_MINUS = 12 = unOpTok .neg
800035f4: ld   a3,144(sp)      # v[0..8) (kind dword; bytes 4-7 dead)
800035f8: beq  a4,a5,800039ac  # neg vs not — TAKEN (op = 12)
-- neg tail @ 0x800039ac: --
800039ac: ld   a1,152(sp)      # v payload  n  (subsret+8)
800039b0: ld   a4,160(sp)      # v[16..24)  (dead — presence only)
800039b4: lw   a0,144(sp)      # v.kind  = 2
800039b8: sd   a3,240(sp)      # runtime-error arg staging (inside frame)
800039bc: sd   a1,248(sp)
800039c0: sd   a4,256(sp)
800039c4: li   a2,2            # VAL_INT = 2
800039c8: lw   s0,4(s0)        # s0 := e->line (CLOBBERS s0)
800039cc: bne  a0,a2,80003b58  # kind != int — NOT taken (kind = 2)
800039d0: neg  a1,a1           # a1 := 0 - n  (64-bit wrap)
800039d4: mv   a0,s1           # a0 := outer sret
800039d8: jal  value_int       # value_int(sret, -n)
800039dc: j    800033ec        # shared epilogue → blockD_v
```

Output: `PreEpilogueV … (.int (wrap64 (-n))) 0x800033ec` (fed unchanged to
`blockD_v`). The produced value is `.int (wrap64 (-n))` — exactly what the
amended `EvalE.neg` rule derives — via `neg_wrap_bridge` below.

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

/-! ## The wrap64 bridge for the `neg` exit value

`value_int_spec` produces `.int (BitVec.ofNat 64 pay.toNat).toInt` with the
payload `pay = 0#64 - n_bv` (the machine `neg`). Since `n_bv.toInt = n` (the
sub-value's `.int n` `ValueRepr` payload), this equals `.int (wrap64 (-n))`:
`BitVec.ofNat 64 x.toNat = x` (round-trip), `0#64 - n_bv = -n_bv`, and
`(-n_bv).toInt = wrap64 (-(n_bv.toInt))` via `BitVec.ofInt_neg`/`ofInt_toInt`.
At `n = -2^63` this gives `-2^63` (`wrap64_neg_min`), matching the machine. -/
theorem ofNat_toNat_self64 (x : BitVec 64) : (BitVec.ofNat 64 x.toNat) = x := by
  simp [BitVec.setWidth_eq]

theorem neg_wrap_bridge (n_bv : BitVec 64) (n : Int) (hn : n_bv.toInt = n) :
    (BitVec.ofNat 64 (0#64 - n_bv).toNat).toInt = wrap64 (-n) := by
  rw [ofNat_toNat_self64, BitVec.zero_sub, ← hn]
  unfold wrap64
  rw [BitVec.ofInt_neg, BitVec.ofInt_toInt]

/-! ## `readI64` extraction from `ValueRepr … (.int n)` -/
theorem valueRepr_int_pay64 {m : Mem} {N : NativeAddrs} {φc : Addr → Nat}
    {a : Nat} {n : Int} (h : ValueRepr m N φc a (.int n)) :
    read32 m a = some 2 ∧ ∃ p, read64 m (a + 8) = some p ∧ (BitVec.ofNat 64 p).toInt = n := by
  obtain ⟨hk, hp⟩ := h
  simp only [readI64, Option.map_eq_some_iff] at hp
  obtain ⟨p, hp64, hpn⟩ := hp
  exact ⟨hk, p, hp64, hpn⟩

/-! ## Presence lift over `MemExtends`

The tail's `ld a3,144(sp)`/`ld a1,152(sp)`/`ld a4,160(sp)` read the whole
sub-`Value` buffer `[subsret, subsret+24)`; `ValueRepr … (.int n)` pins only
the kind word `[subsret, subsret+4)` and the payload `[subsret+8, subsret+16)`.
The dead bytes (`[subsret+4, subsret+8)`, `[subsret+16, subsret+24)`) must still
be PRESENT for the machine `ld`. They live in the caller's lowered frame
`[SL.lo, sp)` (populated at the pre-call memory `mcall` by the layout), so
`MemExtends mcall c.σ.mem` carries their presence to the post-call memory. The
caller supplies the pre-call stack-populated fact `hStackPop`. -/
theorem stackpop_present {mcall m : Mem} (hExt : MemExtends mcall m)
    (hpop : ∀ a : Nat, (∃ b, mcall[a]? = some b))
    (a : Nat) : ∃ b, m[a]? = some b := by
  obtain ⟨b, hb⟩ := hpop a; exact hExt a b hb

/-! ## `Value_intLoaded` survives agreement on `value_int`'s code region

The `value_int` code lives at `[0x8000280c, 0x8000281c)` (a separate function
from `eval_expr`), so `SubEvalReturn` — which only re-exposes `Eval_exprLoaded`
— does not carry it. The arm entry supplies `Value_intLoaded mcall`; this lemma
transports it to the post-sub-call memory via agreement on that region. -/
theorem loaded_value_int_agreeP (m m' : Mem)
    (ha : ∀ a, (0x8000280c ≤ a ∧ a < 0x8000281c) → m[a]? = m'[a]?)
    (h : Value_intLoaded m) : Value_intLoaded m' := by
  simp only [Value_intLoaded, value_intChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; simp_all only [])

/-! ## `blockC_neg` — the post-call `neg` tail -/
theorem blockC_neg
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st' : Vsa.While.St) (n : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (esub : Expr) (m0 : Mem) :
    Triple
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc st' (.int n) sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) (0x800035ec#64)
          v8 v9 v18 mcall c ∧
        gpre Register.x8 = some aExpr ∧
        ExprRepr mcall aExpr.toNat (.unary .neg esub) ∧
        (∀ a : Nat, (∃ b, mcall[a]? = some b)) ∧
        aExpr.toNat % 4 = 0 ∧
        0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 8 ≤ aExpr.toNat ∧
        -- the caller Expr node is AST memory, disjoint from the sub-call's
        -- lowered frame, the arena, and the sub-result buffer: so `c.σ.mem`
        -- agrees with the pre-call `mcall` there (op token reads value 12).
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ sp.toNat - 944 ∨ sp.toNat - 944 + 24 ≤ aExpr.toNat) ∧
        String.join out0.toList = st'.out ∧
        sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ 0x8000280c ∨ 0x8000281c ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        r.toNat % 4 = 0 ∧
        SL.lo + 1088 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        -- extras added while closing the tail (all discharge-later geometry /
        -- static-code facts the arm entry carries; see EvalNegSim2 handoff):
        c.σ.sailOutput = out0 ∧
        Value_intLoaded mcall ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (sp.toNat ≤ 0x8000280c ∨ 0x8000281c ≤ SL.lo) ∧
        (A.hi ≤ 0x8000280c ∨ 0x8000281c ≤ A.lo) ∧
        -- the outer sret buffer sits inside the whole-stack region (caller frame):
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
          mcall[a]? = m0[a]?) ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        -- entry ghost `g`: its callee-saved s0/s1/s2/sp are the spilled entry
        -- values (restored by the epilogue), and it agrees with the call-point
        -- frame `gpre` off s0/s1/s2/sp (the prologue-established bridge).
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (fun c => ∃ (mpre : Mem) (φfe φce : Addr → Nat),
        PhiExtends φf φfe st'.store.frames.size ∧
        PhiExtends φc φce st'.store.closures.size ∧
        PreEpilogueV g N A SL φfe φce st' (.int (wrap64 (-n))) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨mcall, hSub, hgx8, hexpr, hStackPop, hexprAl, hexprLo, hexprHi, hexprWin,
    hexprSL, hexprA, hexprSub,
    houtStr, hsretAl, hsretLo, hsretHi, hsretWin, hsretVi, hsretStk, hsretEvalCode,
    hraAl, hSLloSp, hSLlo, hSLwin,
    hout0eq, hVint, hcodeStk, hviStk, hviArena, hsretInSL, hMcallM0,
    hsphiRam, hsp8, hSLhiRam, hspSLhi, hgv8, hgv9, hgv18, hgv2, hbridge⟩ := hpre
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
  have hsub944 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    spill_addr sp (0x090#12) 944 (by decide) (by omega) hsp1088
  -- x8 = aExpr (callee-saved survives the sub-call)
  have hx8 : c.σ.regs.get? Register.x8 = some aExpr := (hframe Register.x8 (by decide)).trans hgx8
  -- op-token addr aExpr+8, e->line addr aExpr+4
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  have hline4 : (aExpr + sign_extend (m := 64) (0x004#12)).toNat = aExpr.toNat + 4 := by
    have hs : (sign_extend (m := 64) (0x004#12) : BitVec 64) = 4#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (4#64 : BitVec 64).toNat = 4 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  -- ExprRepr (.unary .neg esub) fields
  obtain ⟨aptr, hk8, hoptok, hpayptr, hsubR⟩ : ∃ p,
      read32 mcall aExpr.toNat = some 8 ∧ read32 mcall (aExpr.toNat + 8) = some (unOpTok .neg) ∧
      read64 mcall (aExpr.toNat + 16) = some p ∧ ExprRepr mcall p esub := by
    cases hexpr with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  have hoptok12 : read32 mcall (aExpr.toNat + 8) = some 12 := by simpa [unOpTok] using hoptok
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes mcall (aExpr.toNat + 8) 12 hoptok12
  -- e->line bytes (aExpr+4): present from MemExtends (whole mcall present)
  obtain ⟨lb0, hlb0⟩ := stackpop_present hMemExt hStackPop (aExpr.toNat + 4)
  obtain ⟨lb1, hlb1⟩ := stackpop_present hMemExt hStackPop (aExpr.toNat + 4 + 1)
  obtain ⟨lb2, hlb2⟩ := stackpop_present hMemExt hStackPop (aExpr.toNat + 4 + 2)
  obtain ⟨lb3, hlb3⟩ := stackpop_present hMemExt hStackPop (aExpr.toNat + 4 + 3)
  -- op-token bytes with VALUE in c.σ.mem: aExpr node is AST memory, agrees with
  -- mcall (disjoint from sub-frame ∪ arena ∪ subsret window) via memFrame.
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
  -- kind + payload of the sub-value
  have hvalSub' : ValueRepr c.σ.mem N φcv (sp.toNat - 944) (.int n) := by
    rwa [hsub944] at hvalSub
  obtain ⟨hkind2, p, hpay64, hpn⟩ := valueRepr_int_pay64 hvalSub'
  obtain ⟨kb0, kb1, kb2, kb3, hkb0, hkb1, hkb2, hkb3, hkbrec⟩ :=
    read32_bytes c.σ.mem (sp.toNat - 944) 2 hkind2
  obtain ⟨pb0, pb1, pb2, pb3, pb4, pb5, pb6, pb7, hpb0, hpb1, hpb2, hpb3, hpb4, hpb5, hpb6, hpb7, hprec⟩ :=
    read64_bytes c.σ.mem (sp.toNat - 944 + 8) p hpay64
  let payV : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  have hpayVnat : payV.toNat = p := by
    show (sign_extend (m := 64)
      ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))).toNat = p
    rw [sext_full, word8_toNat_recon, hprec]
  -- dead bytes present in c.σ.mem (whole mcall present ⇒ MemExtends):
  -- kind dword bytes 4-7 at (sp-944)+4..7, and v[16..24) at (sp-944)+16..23.
  obtain ⟨d4, hd4⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 4)
  obtain ⟨d5, hd5⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 5)
  obtain ⟨d6, hd6⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 6)
  obtain ⟨d7, hd7⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 7)
  obtain ⟨q0, hq0⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16)
  obtain ⟨q1, hq1⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 1)
  obtain ⟨q2, hq2⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 2)
  obtain ⟨q3, hq3⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 3)
  obtain ⟨q4, hq4⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 4)
  obtain ⟨q5, hq5⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 5)
  obtain ⟨q6, hq6⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 6)
  obtain ⟨q7, hq7⟩ := stackpop_present hMemExt hStackPop (sp.toNat - 944 + 16 + 7)
  -- payload-load bytes present in c.σ.mem: read64 already gives them (hpb0..hpb7).
  -- the op-token loaded value = 12#64
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (12#64 : BitVec 64) := by
    rw [sext_word_small _ 12 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  -- the li a5,12 value = 12#64
  have hli12 : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12)) = (12#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  -- the li a2,2 value = 2#64
  have hli2 : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x002#12)) = (2#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  -- the kind loaded value (lw a0,144(sp)) = 2#64
  have hkindVal : (sign_extend (m := 64) ((((kb3.append kb2).append kb1).append kb0) : BitVec (8*4)))
      = (2#64 : BitVec 64) := by
    rw [sext_word_small _ 2 (by decide) (by rw [word_toNat_recon]; exact hkbrec)]
  -- addresses of the three tail loads and stores as sp - k
  have haddr144 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 :=
    hsub944
  have haddr152 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by omega) hsp1088
  have haddr160 : ((sp - 1088#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 928 :=
    spill_addr sp (0x0a0#12) 928 (by decide) (by omega) hsp1088
  have haddr240 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat = sp.toNat - 848 :=
    spill_addr sp (0x0f0#12) 848 (by decide) (by omega) hsp1088
  have haddr248 : ((sp - 1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat = sp.toNat - 840 :=
    spill_addr sp (0x0f8#12) 840 (by decide) (by omega) hsp1088
  have haddr256 : ((sp - 1088#64) + sign_extend (m := 64) (0x100#12)).toNat = sp.toNat - 832 :=
    spill_addr sp (0x100#12) 832 (by decide) (by omega) hsp1088
  ------------------------------------------------------------------------
  -- 0x800035ec → 0x800039ac: the prologue (σ0→σ4, 4 steps: op-token load,
  -- li a5,12, kind-dword load, taken beq a4,a5) via ONE neg_prologue_block —
  -- was ~90 lines of per-step obs_*_other carries.
  ------------------------------------------------------------------------
  obtain ⟨σ4, i4, hstepPro, hi4, hG4, hmem4e, hout4, hpc4, _ha14_4, _ha15_4, hx13_4,
      hs1_4, hsp_4, hx8_4, _hx1_4, ⟨vmi4, hmi4⟩, hframePro⟩ :=
    neg_prologue_block c.σ c.tick c.steps vmi aExpr (sp-1088#64) sret (0x800035ec#64)
      ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
      hG hpc hmi hx8 hsp hs1 hra hcode hopVal
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      ⟨(by rw [hop8]; exact hoc0), (by rw [hop8]; exact hoc1),
       (by rw [hop8]; exact hoc2), (by rw [hop8]; exact hoc3)⟩
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      ⟨(by rw [haddr144]; exact hkb0), (by rw [haddr144]; exact hkb1),
       (by rw [haddr144]; exact hkb2), (by rw [haddr144]; exact hkb3),
       (by rw [haddr144]; exact hd4), (by rw [haddr144]; exact hd5),
       (by rw [haddr144]; exact hd6), (by rw [haddr144]; exact hd7)⟩
      htick
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- normalize the payload / dead-word byte addresses to the site-load offsets
  have e936 : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
  have e928 : sp.toNat - 944 + 16 = sp.toNat - 928 := by omega
  rw [e936] at hpb0 hpb1 hpb2 hpb3 hpb4 hpb5 hpb6 hpb7
  rw [e928] at hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7
  ------------------------------------------------------------------------
  ------------------------------------------------------------------------
  -- 0x800039ac → 0x800039c4: the neg load/store run (σ4→σ10, 6 steps) via ONE
  -- `neg_loadstore_full` block application — was ~190 lines of per-step
  -- `obs_*_other` carries. The three load results, the carried callee-saved,
  -- and the memory (in `writeLog` form, bridged to the `m3` tower below via the
  -- Phase-1 `writeLog`↦`writeMap8` defeq) all come out computed.
  ------------------------------------------------------------------------
  let V14 : BitVec 64 := sign_extend (m := 64)
    ((((((((q7.append q6).append q5).append q4).append q3).append q2).append q1).append q0) : BitVec (8*8))
  let K13 : BitVec 64 := sign_extend (m := 64)
    ((((((((d7.append d6).append d5).append d4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))
  obtain ⟨σ10, i10, hstepBlk, hi10, hG10, hout10', hpc10, hx11_10', _hx14_10, hx10_10',
      hx13_10, hs1_10, hsp_10, hx8_10, ⟨vmi10, hmi10⟩, hmemBlk, hframeBlk⟩ :=
    neg_loadstore_full σ4 i4 (c.steps+1+1+1+1) vmi4 (sp-1088#64) K13 sret aExpr
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7 kb0 kb1 kb2 kb3
      hG4 hpc4 hmi4 hsp_4 hx13_4 hs1_4 hx8_4 hcode4
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      ⟨(by rw [haddr152, hmem4e]; exact hpb0), (by rw [haddr152, hmem4e]; exact hpb1),
       (by rw [haddr152, hmem4e]; exact hpb2), (by rw [haddr152, hmem4e]; exact hpb3),
       (by rw [haddr152, hmem4e]; exact hpb4), (by rw [haddr152, hmem4e]; exact hpb5),
       (by rw [haddr152, hmem4e]; exact hpb6), (by rw [haddr152, hmem4e]; exact hpb7)⟩
      (by rw [haddr160]; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, htoh]; right; omega) (by rw [haddr160]; omega)
      ⟨(by rw [haddr160, hmem4e]; exact hq0), (by rw [haddr160, hmem4e]; exact hq1),
       (by rw [haddr160, hmem4e]; exact hq2), (by rw [haddr160, hmem4e]; exact hq3),
       (by rw [haddr160, hmem4e]; exact hq4), (by rw [haddr160, hmem4e]; exact hq5),
       (by rw [haddr160, hmem4e]; exact hq6), (by rw [haddr160, hmem4e]; exact hq7)⟩
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      ⟨(by rw [haddr144, hmem4e]; exact hkb0), (by rw [haddr144, hmem4e]; exact hkb1),
       (by rw [haddr144, hmem4e]; exact hkb2), (by rw [haddr144, hmem4e]; exact hkb3)⟩
      (by rw [haddr240]; omega) (by rw [haddr240]; omega) (by rw [haddr240, htoh]; omega) (by rw [haddr240]; omega)
      (by rw [haddr248]; omega) (by rw [haddr248]; omega) (by rw [haddr248, htoh]; omega) (by rw [haddr248]; omega)
      (by rw [haddr256]; omega) (by rw [haddr256]; omega) (by rw [haddr256, htoh]; omega) (by rw [haddr256]; omega)
      hi4
  -- bridge block outputs → the domain names the tail consumes
  have hout10 : σ10.sailOutput = c.σ.sailOutput := hout10'.trans hout4
  have hx11_10 : σ10.regs.get? Register.x11 = some payV := hx11_10'
  have hx10_10 : σ10.regs.get? Register.x10 = some (2#64) := by
    rw [show (bytesVal MKind.lw [kb0,kb1,kb2,kb3]) = (2#64 : BitVec 64) from hkindVal] at hx10_10'
    exact hx10_10'
  -- the three error-arg staging stores as the `m1`/`m2`/`m3` tower the tail
  -- consumes (defeq to `neg_loadstore_full`'s `writeLog` memory after the
  -- `haddr*` address normalisations).
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val K13)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 840) (sdData_val payV)
  let m3 : Mem := writeMap8 m2 (sp.toNat - 832) (sdData_val V14)
  have hmem10' : σ10.mem = m3 := by
    rw [hmemBlk, hmem4e]
    show writeMap8 (writeMap8 (writeMap8 c.σ.mem
        ((sp - 1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat (sdData_val K13))
        ((sp - 1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat (sdData_val payV))
        ((sp - 1088#64) + sign_extend (m := 64) (0x100#12)).toNat (sdData_val V14) = m3
    rw [haddr240, haddr248, haddr256]
  have hcode10 : Eval_exprLoaded σ10.mem := by
    rw [hmem10']
    refine loaded_eval_expr_agreeP c.σ.mem m3 (fun a ha => ?_) hcode
    show c.σ.mem[a]? = (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[a]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) a (sdData_val V14) (by rcases hcodeStk with h | h <;> omega)]
    show c.σ.mem[a]? = (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[a]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) a (sdData_val payV) (by rcases hcodeStk with h | h <;> omega)]
    show c.σ.mem[a]? = (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) a (sdData_val K13) (by rcases hcodeStk with h | h <;> omega)]
  -- `value_int`'s code survives from the pre-call memory to the post-call memory
  -- (its region `[0x8000280c,0x8000281c)` is disjoint from the sub-frame/arena/subsret).
  have hVint_c : Value_intLoaded c.σ.mem := by
    refine loaded_value_int_agreeP mcall c.σ.mem (fun a ha => ?_) hVint
    rcases hmemFrame a (by rcases hviStk with h | h <;> omega) (by rcases hviArena with h | h <;> omega)
      with hin | heq
    · exact absurd hin (by rcases hviStk with h | h <;> omega)
    · exact heq.symm
  have hVint10 : Value_intLoaded σ10.mem := by
    rw [hmem10']
    exact loaded_int_writeMap8 m2 (sp.toNat - 832) (sdData_val V14) (by rcases hviStk with h | h <;> omega)
      (loaded_int_writeMap8 m1 (sp.toNat - 840) (sdData_val payV) (by rcases hviStk with h | h <;> omega)
        (loaded_int_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val K13) (by rcases hviStk with h | h <;> omega) hVint_c))
  -- the e->line bytes at `aExpr+4` (AST memory) survive the three error stores
  have hm3_disj : ∀ k, aExpr.toNat + 4 ≤ k → k < aExpr.toNat + 8 → m3[k]? = c.σ.mem[k]? := by
    intro k hk1 hk2
    show (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) k (sdData_val V14) (by rcases hexprSL with h | h <;> omega)]
    show (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) k (sdData_val payV) (by rcases hexprSL with h | h <;> omega)]
    show (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[k]? = c.σ.mem[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val K13) (by rcases hexprSL with h | h <;> omega)]
  have hlbm3_0 : m3[aExpr.toNat + 4]? = some lb0 := (hm3_disj _ (by omega) (by omega)).trans hlb0
  have hlbm3_1 : m3[aExpr.toNat + 4 + 1]? = some lb1 := (hm3_disj _ (by omega) (by omega)).trans hlb1
  have hlbm3_2 : m3[aExpr.toNat + 4 + 2]? = some lb2 := (hm3_disj _ (by omega) (by omega)).trans hlb2
  have hlbm3_3 : m3[aExpr.toNat + 4 + 3]? = some lb3 := (hm3_disj _ (by omega) (by omega)).trans hlb3
  ------------------------------------------------------------------------
  -- 0x800039c4: li a2,2 → x12 := 2#64
  ------------------------------------------------------------------------
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_800039c4_ee σ10 i10 (c.steps+1+1+1+1+1+1+1+1+1+1) (0x800039c4#64) vmi10 hG10 hpc10 hmi10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ11, i11, c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ := hs11'
  have hmem11_3 : σ11.mem = m3 := by rw [hmem11]; exact hmem10'
  have hpc11 : σ11.regs.get? Register.PC = some (0x800039c8#64) := by
    have := obs_alu_pc hobs11
    rwa [show BitVec.addInt (0x800039c4#64) 4 = (0x800039c8#64:BitVec 64) from by decide] at this
  have hx12_11 : σ11.regs.get? Register.x12 = some (2#64) := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hli2] at this
  have hx11_11 : σ11.regs.get? Register.x11 = some payV := obs_alu_other hobs11 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_10
  have hx10_11 : σ11.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_10
  have hs1_11 : σ11.regs.get? Register.x9 = some sret := obs_alu_other hobs11 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other hobs11 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_10
  have hx8_11 : σ11.regs.get? Register.x8 = some aExpr := obs_alu_other hobs11 Register.x8 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx8_10
  obtain ⟨vmi11, hmi11⟩ := obs_alu_minstret hobs11
  have hout11 : σ11.sailOutput = c.σ.sailOutput := by rw [hobs11.out, sailOutput_sigmaPost_alu]; exact hout10
  have hcode11 : Eval_exprLoaded σ11.mem := by rw [hmem11_3]; exact hmem10' ▸ hcode10
  ------------------------------------------------------------------------
  -- 0x800039c8: lw s0,4(s0) → x8 := e->line (CLOBBERS s0; value unused)
  ------------------------------------------------------------------------
  obtain ⟨σ12, i12, hs12', hi12, hG12, hmem12, hobs12⟩ :=
    site_800039c8_ee σ11 i11 (c.steps+1+1+1+1+1+1+1+1+1+1+1) (0x800039c8#64) vmi11 aExpr lb0 lb1 lb2 lb3
      hG11 hpc11 hmi11 hx8_11 hcode11 rfl
      (by rw [hline4]; omega) (by rw [hline4]; omega)
      (by rw [hline4, htoh]; right; omega) (by rw [hline4]; omega)
      (by rw [hline4, hmem11_3]; exact hlbm3_0) (by rw [hline4, hmem11_3]; exact hlbm3_1)
      (by rw [hline4, hmem11_3]; exact hlbm3_2) (by rw [hline4, hmem11_3]; exact hlbm3_3) hi11
  have hstep12 : Step ⟨σ11, i11, c.steps+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ12, i12, c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs12'
  have hmem12_3 : σ12.mem = m3 := by rw [hmem12]; exact hmem11_3
  have hpc12 : σ12.regs.get? Register.PC = some (0x800039cc#64) := by
    have := obs_alu_pc hobs12
    rwa [show BitVec.addInt (0x800039c8#64) 4 = (0x800039cc#64:BitVec 64) from by decide] at this
  have hx11_12 : σ12.regs.get? Register.x11 = some payV := obs_alu_other hobs12 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_11
  have hx10_12 : σ12.regs.get? Register.x10 = some (2#64) := obs_alu_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_11
  have hx12_12 : σ12.regs.get? Register.x12 = some (2#64) := obs_alu_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx12_11
  have hs1_12 : σ12.regs.get? Register.x9 = some sret := obs_alu_other hobs12 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_11
  have hsp_12 : σ12.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other hobs12 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_11
  obtain ⟨vmi12, hmi12⟩ := obs_alu_minstret hobs12
  have hout12 : σ12.sailOutput = c.σ.sailOutput := by rw [hobs12.out, sailOutput_sigmaPost_alu]; exact hout11
  have hcode12 : Eval_exprLoaded σ12.mem := by rw [hmem12_3]; exact hmem10' ▸ hcode10
  have hVint12 : Value_intLoaded σ12.mem := by rw [hmem12_3]; exact hmem10' ▸ hVint10
  ------------------------------------------------------------------------
  -- 0x800039cc: bne a0,a2 (NOT taken: kind = 2 = VAL_INT)
  ------------------------------------------------------------------------
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_800039cc_nottaken_ee σ12 i12 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1) (0x800039cc#64) vmi12 (2#64) (2#64)
      hG12 hpc12 hmi12 hx10_12 hx12_12 hcode12 rfl (by decide) hi12
  have hstep13 : Step ⟨σ12, i12, c.steps+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ13, i13, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs13'
  have hmem13_3 : σ13.mem = m3 := by rw [hmem13]; exact hmem12_3
  have hpc13 : σ13.regs.get? Register.PC = some (0x800039d0#64) := by
    have := obs_branch_nottaken_pc hobs13
    rwa [show BitVec.addInt (0x800039cc#64) 4 = (0x800039d0#64:BitVec 64) from by decide] at this
  have hx11_13 : σ13.regs.get? Register.x11 = some payV := obs_branch_nottaken_other hobs13 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_12
  have hs1_13 : σ13.regs.get? Register.x9 = some sret := obs_branch_nottaken_other hobs13 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_12
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp-1088#64) := obs_branch_nottaken_other hobs13 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_12
  obtain ⟨vmi13, hmi13⟩ := obs_branch_nottaken_minstret hobs13
  have hout13 : σ13.sailOutput = c.σ.sailOutput := by rw [hobs13.out, sailOutput_sigmaPost_branch_nottaken]; exact hout12
  have hcode13 : Eval_exprLoaded σ13.mem := by rw [hmem13_3]; exact hmem10' ▸ hcode10
  have hVint13 : Value_intLoaded σ13.mem := by rw [hmem13_3]; exact hmem10' ▸ hVint10
  ------------------------------------------------------------------------
  -- 0x800039d0: neg a1,a1 → x11 := 0 - payV
  ------------------------------------------------------------------------
  obtain ⟨σ14, i14, hs14', hi14, hG14, hmem14, hobs14⟩ :=
    site_800039d0_ee σ13 i13 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800039d0#64) vmi13 payV
      hG13 hpc13 hmi13 hx11_13 hcode13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ14, i14, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs14'
  have hmem14_3 : σ14.mem = m3 := by rw [hmem14]; exact hmem13_3
  have hpc14 : σ14.regs.get? Register.PC = some (0x800039d4#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x800039d0#64) 4 = (0x800039d4#64:BitVec 64) from by decide] at this
  have hx11_14 : σ14.regs.get? Register.x11 = some ((0#64) - payV) :=
    obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_14 : σ14.regs.get? Register.x9 = some sret := obs_alu_other hobs14 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other hobs14 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hout14 : σ14.sailOutput = c.σ.sailOutput := by rw [hobs14.out, sailOutput_sigmaPost_alu]; exact hout13
  have hcode14 : Eval_exprLoaded σ14.mem := by rw [hmem14_3]; exact hmem10' ▸ hcode10
  have hVint14 : Value_intLoaded σ14.mem := by rw [hmem14_3]; exact hmem10' ▸ hVint10
  ------------------------------------------------------------------------
  -- 0x800039d4: mv a0,s1 → x10 := sret
  ------------------------------------------------------------------------
  have hmv : (sret + sign_extend (m := 64) (0x000#12)) = sret := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero]
  obtain ⟨σ15, i15, hs15', hi15, hG15, hmem15, hobs15⟩ :=
    site_800039d4_ee σ14 i14 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800039d4#64) vmi14 sret
      hG14 hpc14 hmi14 hs1_14 hcode14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ15, i15, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs15'
  have hmem15_3 : σ15.mem = m3 := by rw [hmem15]; exact hmem14_3
  have hpc15 : σ15.regs.get? Register.PC = some (0x800039d8#64) := by
    have := obs_alu_pc hobs15
    rwa [show BitVec.addInt (0x800039d4#64) 4 = (0x800039d8#64:BitVec 64) from by decide] at this
  have hx10_15 : σ15.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hmv] at this
  have hx11_15 : σ15.regs.get? Register.x11 = some ((0#64) - payV) := obs_alu_other hobs15 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_14
  have hs1_15 : σ15.regs.get? Register.x9 = some sret := obs_alu_other hobs15 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp-1088#64) := obs_alu_other hobs15 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_14
  obtain ⟨vmi15, hmi15⟩ := obs_alu_minstret hobs15
  have hout15 : σ15.sailOutput = c.σ.sailOutput := by rw [hobs15.out, sailOutput_sigmaPost_alu]; exact hout14
  have hcode15 : Eval_exprLoaded σ15.mem := by rw [hmem15_3]; exact hmem10' ▸ hcode10
  have hVint15 : Value_intLoaded σ15.mem := by rw [hmem15_3]; exact hmem10' ▸ hVint10
  ------------------------------------------------------------------------
  -- 0x800039d8: jal value_int → PC := 0x8000280c, x1 := 0x800039dc
  ------------------------------------------------------------------------
  obtain ⟨σ16, i16, hs16', hi16, hG16, hmem16, hobs16⟩ :=
    site_800039d8_ee σ15 i15 (c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1) (0x800039d8#64) vmi15
      hG15 hpc15 hmi15 hcode15 rfl hi15
  have hstep16 : Step ⟨σ15, i15, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ ⟨σ16, i16, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := hs16'
  have hmem16_3 : σ16.mem = m3 := by rw [hmem16]; exact hmem15_3
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000280c#64) := by
    have := obs_jal_pc hobs16
    rwa [show ((0x800039d8#64 : BitVec 64) + sign_extend (m := 64) (0x1fee34#21)) = 0x8000280c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink16 : σ16.regs.get? Register.x1 = some (0x800039dc#64) := by
    have := obs_jal_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800039d8#64 : BitVec 64) 4 = (0x800039dc#64:BitVec 64) from by decide] at this
  have hx10_16 : σ16.regs.get? Register.x10 = some sret := obs_jal_other hobs16 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx10_15
  have hx11_16 : σ16.regs.get? Register.x11 = some ((0#64) - payV) := obs_jal_other hobs16 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hx11_15
  have hs1_16 : σ16.regs.get? Register.x9 = some sret := obs_jal_other hobs16 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp-1088#64) := obs_jal_other hobs16 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_15
  obtain ⟨vmi16, hmi16⟩ := obs_jal_minstret hobs16
  have hout16 : σ16.sailOutput = c.σ.sailOutput := by rw [hobs16.out, sailOutput_sigmaPost_jal]; exact hout15
  have hVint16 : Value_intLoaded σ16.mem := by rw [hmem16_3]; exact hmem10' ▸ hVint10
  have hcode16 : Eval_exprLoaded σ16.mem := by rw [hmem16_3]; exact hmem10' ▸ hcode10
  ------------------------------------------------------------------------
  -- the value_int callee (via value_int_spec), buf = sret, pay = 0 - payV
  ------------------------------------------------------------------------
  have hIntRegion : IntRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  have hcallpre : int_pre (fun R => σ16.regs.get? R) sret ((0#64) - payV) (0x800039dc#64) σ16.mem c.σ.sailOutput
      ⟨σ16, i16, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ := by
    refine ⟨hG16, hVint16, rfl, hpc16, hx10_16, hx11_16, hlink16, ⟨vmi16, hmi16⟩, hi16, hIntRegion,
      (by decide), hout16, fun R _ => rfl⟩
  obtain ⟨cvi, hsvi, hGvi, hpcvi, hx10vi, hravi, ⟨vmivi, hmivi⟩, htickvi, hvalvi, houtvi,
      hmemframevi, hframevi⟩ :=
    value_int_spec (fun R => σ16.regs.get? R) sret ((0#64) - payV) (0x800039dc#64) N φc' σ16.mem c.σ.sailOutput
      ⟨σ16, i16, c.steps+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1+1⟩ hcallpre
  -- the produced value is `.int (wrap64 (-n))`
  have hpayV_toInt : payV.toInt = n := by
    have hpe : payV = BitVec.ofNat 64 p := by rw [← hpayVnat]; exact (ofNat_toNat_self64 payV).symm
    rw [hpe]; exact hpn
  have hval_bridge : (BitVec.ofNat 64 ((0#64) - payV).toNat).toInt = wrap64 (-n) :=
    neg_wrap_bridge payV n hpayV_toInt
  have hvalfinal : ValueRepr cvi.σ.mem N φc' sret.toNat (.int (wrap64 (-n))) := by
    rw [← hval_bridge]; exact hvalvi
  -- survive code across value_int's sret write
  have hpcvi' : cvi.σ.regs.get? Register.PC = some (0x800039dc#64) := by
    rw [hpcvi, show (BitVec.update ((0x800039dc#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x800039dc#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hcode_vi : Eval_exprLoaded cvi.σ.mem :=
    loaded_eval_expr_agreeP σ16.mem cvi.σ.mem
      (fun k hk => hmemframevi k (by rcases hsretEvalCode with h | h <;> omega)) hcode16
  -- callee-preserved s1(x9)/sp(x2)
  have hs1_vi : cvi.σ.regs.get? Register.x9 = some sret := by
    rw [hframevi Register.x9 (by decide)]; exact hs1_16
  have hsp_vi : cvi.σ.regs.get? Register.x2 = some (sp-1088#64) := by
    rw [hframevi Register.x2 (by decide)]; exact hsp_16
  ------------------------------------------------------------------------
  -- 0x800039dc: j 0x800033ec → shared epilogue entry
  ------------------------------------------------------------------------
  obtain ⟨σ17, i17, hs17', hi17, hG17, hmem17, hobs17⟩ :=
    site_800039dc_ee cvi.σ cvi.tick cvi.steps (0x800039dc#64) vmivi hGvi hpcvi' hmivi hcode_vi rfl
      (by decide) htickvi
  have hstep17 : Step cvi ⟨σ17, i17, cvi.steps + 1⟩ := by cases cvi; exact hs17'
  have hmem17e : σ17.mem = cvi.σ.mem := hmem17
  have hpc_fin : σ17.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs17
    rwa [show ((0x800039dc#64:BitVec 64) + sign_extend (m := 64) (0x1ffa10#21)) = 0x800033ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_fin : σ17.regs.get? Register.x9 = some sret := obs_jr_other hobs17 Register.x9 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hs1_vi
  have hsp_fin : σ17.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other hobs17 Register.x2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hsp_vi
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hobs17
  have hout_fin : σ17.sailOutput = c.σ.sailOutput := by rw [hobs17.out, sailOutput_sigmaPost_jump_x0]; exact houtvi
  -- spill slots survive (top 32 bytes of frame: disjoint from the 3 error stores
  -- below sp-32 and from value_int's sret write, which is not in [sp-32,sp))
  have hslotAgree : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem σ17.mem := by
    intro k hk
    rw [hmem17e, ← hmemframevi k (by rcases hsretStk with h | h <;> omega), hmem16_3]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) k (sdData_val V14) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) k (sdData_val payV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val K13) (by omega)]
  have hslotRa_f : read64 σ17.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
  have hslotS0_f : read64 σ17.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS0
  have hslotS1_f : read64 σ17.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS1
  have hslotS2_f : read64 σ17.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS2
  -- StoreRepr survives: all writes (3 error stores + sret) land inside [SL.lo, SL.hi)
  have hstore_fin : StoreRepr σ17.mem N A φf' φc' st'.store := by
    apply hstoreSurv'
    intro k hk
    rw [hmem17e, ← hmemframevi k (by rcases hsretInSL with ⟨hl, hr⟩; omega), hmem16_3]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) k (sdData_val V14) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) k (sdData_val payV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val K13) (by omega)]
  -- the callee-saved (noise) frame: threads gpre through the whole tail, then the
  -- prologue bridge gpre → g (the entry ghost the epilogue restores to).
  have hframeG : ∀ R : Register, AbiPreservedNoise R →
      (Register.x8 == R) = false → (Register.x9 == R) = false →
      (Register.x18 == R) = false → (Register.x2 == R) = false →
      σ17.regs.get? R = g R := by
    intro R hR he8 he9 he18 he2
    obtain ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩ := hR
    have hR' : AbiPreservedNoise R := ⟨hab, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have abi_ne' : ∀ {X : Register}, AbiPreserved X = false → (X == R) = false := by
      intro X hX
      rcases hXR : (X == R) with _ | _
      · rfl
      · rw [beq_iff_eq] at hXR; rw [hXR] at hX; rw [hX] at hab; exact absurd hab (by decide)
    -- σ0→σ4 collapsed: the prologue block frame in one application (was f1..f4)
    have f_pro : σ4.regs.get? R = c.σ.regs.get? R :=
      hframePro R
        (by intro rr hrr
            simp only [noiseRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hrr
            rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by intro n hn
            have hn' : n ∈ ([14, 15, 13] : List Nat) := hn
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hn'
            rcases hn' with rfl | rfl | rfl <;> exact abi_ne' (by decide))
    -- σ4→σ10 collapsed: the block frame in one application (was f5..f10)
    have f5 : σ10.regs.get? R = σ4.regs.get? R :=
      hframeBlk R
        (by intro rr hrr
            simp only [noiseRegs, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hrr
            rcases hrr with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption)
        (by intro n hn
            have hn' : n ∈ ([11, 14, 10] : List Nat) := hn
            simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hn'
            rcases hn' with rfl | rfl | rfl <;> exact abi_ne' (by decide))
    have f11 : σ11.regs.get? R = σ10.regs.get? R :=
      (hobs11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (abi_ne' (by decide)) hnpc' hmii')
    have f12 : σ12.regs.get? R = σ11.regs.get? R :=
      (hobs12.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' he8 hnpc' hmii')
    have f13 : σ13.regs.get? R = σ12.regs.get? R :=
      (hobs13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
    have f14 : σ14.regs.get? R = σ13.regs.get? R :=
      (hobs14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (abi_ne' (by decide)) hnpc' hmii')
    have f15 : σ15.regs.get? R = σ14.regs.get? R :=
      (hobs15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' (abi_ne' (by decide)) hnpc' hmii')
    have f16 : σ16.regs.get? R = σ15.regs.get? R :=
      (hobs16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (abi_ne' (X := Register.x1) (by decide)) hnpc' hmii')
    have fvi : cvi.σ.regs.get? R = σ16.regs.get? R :=
      hframevi R ⟨abi_ne' (by decide), abi_ne' (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have f17 : σ17.regs.get? R = cvi.σ.regs.get? R :=
      (hobs17.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f17, fvi, f16, f15, f14, f13, f12, f11, f5, f_pro]
    exact (hframe R hR').trans (hbridge R hR' he8 he9 he18 he2)
  ------------------------------------------------------------------------
  -- assemble the epilogue-entry package `PreEpilogueV` at the extended maps
  ------------------------------------------------------------------------
  refine ⟨⟨σ17, i17, cvi.steps + 1⟩, ?_, σ17.mem, φf', φc', hpf', hpc', ?_⟩
  · exact hstepPro.trans (hstepBlk.trans ((Steps.single hstep11).trans ((Steps.single hstep12).trans ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans ((Steps.single hstep16).trans (hsvi.trans ((Steps.single hstep17))))))))))
  · refine ⟨hG17, hi17, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
      hout_fin.trans hout0eq, houtStr, rfl, (by rw [hmem17e]; exact hcode_vi),
      (by rw [hmem17e]; exact hvalfinal), hstore_fin, hframeG,
      hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, ?_,
      (by omega), hsphiRam, (by omega), (by omega), hsp8, hraAl⟩
    -- memFrame: mpre (= σ17.mem) vs the entry m0
    intro a ha hA
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · refine Or.inr ?_
      rw [hmem17e, ← hmemframevi a hsr, hmem16_3]
      show (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) a (sdData_val V14) (by omega)]
      show (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) a (sdData_val payV) (by omega)]
      show (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) a (sdData_val K13) (by omega)]
      rcases hmemFrame a (by omega) hA with hin | heq
      · exact absurd hin (by omega)
      · rw [heq]; exact hMcallM0 a ha hA

end Vsa.Sim
