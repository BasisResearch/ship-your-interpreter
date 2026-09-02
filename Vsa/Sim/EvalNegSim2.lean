import Vsa.Sim.EvalNegSim
import Vsa.Sim.NegTailSites
import Vsa.Sim.NegBlockProto
import Vsa.Sim.BlockTactics2
import Vsa.Sim.BlockAdapter
import Vsa.Sim.BlockLogic
import Vsa.Sim.ValueSpec
import Vsa.Sim.DivSites2
import Vsa.Sim.ObsAvoid

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
caller supplies the pre-call frame-populated fact `hStackPop`.
**WAVE 47i (`McallPopTotality`) AMENDMENT**: pointwise form — the old
totality-consuming form (`hpop : ∀ a, ∃ b, mcall[a]? = some b`) fed the
refuted `hMcallPop` oracle (`experiments/fleet/obstructions/
McallPopTotality.lean`); callers now hold a WINDOWED presence fact and apply
it at each concrete dead-byte address. -/
theorem stackpop_present {mcall m : Mem} (hExt : MemExtends mcall m)
    {a : Nat} (hpop : ∃ b, mcall[a]? = some b) : ∃ b, m[a]? = some b := by
  obtain ⟨b, hb⟩ := hpop; exact hExt a b hb

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
    (nf nc : Nat)
    (st' : Vsa.While.St) (n : Int)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (esub : Expr) (m0 : Mem) :
    Triple
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc nf nc st' (.int n) sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) (0x800035ec#64)
          v8 v9 v18 mcall c ∧
        gpre Register.x8 = some aExpr ∧
        ExprRepr mcall aExpr.toNat (.unary .neg esub) ∧
        -- WAVE 47i (`McallPopTotality` amendment): presence ONLY on the actual
        -- dead-byte read footprint — the lowered-frame window `[sp-1120, sp)`
        -- (sub-`Value` padding `[subsret+4,+8) ∪ [subsret+16,+24)`,
        -- `subsret = sp-944`) plus the node's line-word bytes
        -- `[aExpr+4, aExpr+8)` — replacing the REFUTED total-population oracle
        -- (`experiments/fleet/obstructions/McallPopTotality.lean`).
        (∀ a : Nat,
          (sp.toNat - 1120 ≤ a ∧ a < sp.toNat) ∨
            (aExpr.toNat + 4 ≤ a ∧ a < aExpr.toNat + 8) →
          (∃ b, mcall[a]? = some b)) ∧
        -- presence-monotonicity of the pre-call memory over the entry `m0`
        -- (writes are inserts; the `mem_ext` residual, `BinArmExtras` shape).
        MemExtends m0 mcall ∧
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
        PhiExtends φf φfe nf ∧
        PhiExtends φc φce nc ∧
        PreEpilogueVD g N A SL φfe φce st' (.int (wrap64 (-n))) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨mcall, hSub, hgx8, hexpr, hStackPop, hMemExtM0, hexprAl, hexprLo, hexprHi, hexprWin,
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
  obtain ⟨lb0, hlb0⟩ := stackpop_present hMemExt (hStackPop (aExpr.toNat + 4) (by omega))
  obtain ⟨lb1, hlb1⟩ := stackpop_present hMemExt (hStackPop (aExpr.toNat + 4 + 1) (by omega))
  obtain ⟨lb2, hlb2⟩ := stackpop_present hMemExt (hStackPop (aExpr.toNat + 4 + 2) (by omega))
  obtain ⟨lb3, hlb3⟩ := stackpop_present hMemExt (hStackPop (aExpr.toNat + 4 + 3) (by omega))
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
  obtain ⟨d4, hd4⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 4) (by omega))
  obtain ⟨d5, hd5⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 5) (by omega))
  obtain ⟨d6, hd6⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 6) (by omega))
  obtain ⟨d7, hd7⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 7) (by omega))
  obtain ⟨q0, hq0⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16) (by omega))
  obtain ⟨q1, hq1⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 1) (by omega))
  obtain ⟨q2, hq2⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 2) (by omega))
  obtain ⟨q3, hq3⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 3) (by omega))
  obtain ⟨q4, hq4⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 4) (by omega))
  obtain ⟨q5, hq5⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 5) (by omega))
  obtain ⟨q6, hq6⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 6) (by omega))
  obtain ⟨q7, hq7⟩ := stackpop_present hMemExt (hStackPop (sp.toNat - 944 + 16 + 7) (by omega))
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
  -- 0x800035ec → 0x800039d8: the ENTIRE neg spine (σ0→σ15, prologue + load/store
  -- + tail, 15 steps) via ONE `neg_blocks_triple` (Stage A2). The three block
  -- lemmas, the two inter-block seams (kind-dword/payload bridges, code/e→line
  -- survival across the three error stores), and the composed σ0-entry frame all
  -- come out of the one composed `Triple`. Was ~135 lines of per-block obtains +
  -- inter-block bridging.
  ------------------------------------------------------------------------
  let V14 : BitVec 64 := sign_extend (m := 64)
    ((((((((q7.append q6).append q5).append q4).append q3).append q2).append q1).append q0) : BitVec (8*8))
  let K13 : BitVec 64 := sign_extend (m := 64)
    ((((((((d7.append d6).append d5).append d4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))
  -- the three error-arg staging stores as the `m1`/`m2`/`m3` tower the downstream
  -- (value_int / epilogue survival) consumes.
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val K13)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 840) (sdData_val payV)
  let m3 : Mem := writeMap8 m2 (sp.toNat - 832) (sdData_val V14)
  -- `payV`/`K13`/`V14` are defeq to `bytesVal .ld` of the loaded byte lists, so
  -- the `neg_blocks_triple` outputs land on the domain `payV`/`K13`/`V14` names.
  -- normalize the payload / dead-word byte addresses to the site-load offsets
  have e936 : sp.toNat - 944 + 8 = sp.toNat - 936 := by omega
  have e928 : sp.toNat - 944 + 16 = sp.toNat - 928 := by omega
  rw [e936] at hpb0 hpb1 hpb2 hpb3 hpb4 hpb5 hpb6 hpb7
  rw [e928] at hq0 hq1 hq2 hq3 hq4 hq5 hq6 hq7
  -- the `wlogM` of the spine reduces to the three error stores at sp-848/840/832
  -- (defeq to the `m3` tower after the address normalisations).
  let W : Mem := writeLog c.σ.mem (wlogM negLoadStoreBlk.body
    [(2, sp-1088#64), (13, K13), (9, sret)]
    [[pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7], [q0,q1,q2,q3,q4,q5,q6,q7], [kb0,kb1,kb2,kb3]])
  have hWm3 : W = m3 := by
    show writeLog c.σ.mem [((( sp-1088#64) + sign_extend (m := 64) (0x0f0#12)).toNat, 8, K13),
        (((sp-1088#64) + sign_extend (m := 64) (0x0f8#12)).toNat, 8, bytesVal MKind.ld [pb0,pb1,pb2,pb3,pb4,pb5,pb6,pb7]),
        (((sp-1088#64) + sign_extend (m := 64) (0x100#12)).toNat, 8, bytesVal MKind.ld [q0,q1,q2,q3,q4,q5,q6,q7])] = m3
    rw [haddr240, haddr248, haddr256]
    show writeMap8 (writeMap8 (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))
        (sp.toNat-840) (sdData_val payV)) (sp.toNat-832) (sdData_val V14) = m3
    rfl
  -- run the whole spine
  obtain ⟨cS, hstepSpine, hG15, hmem15_W, hout15_W, hpc15, hx10_15, hx11_15b, hs1_15, hsp_15,
      ⟨vmi15, hmi15⟩, hi15, hframeSpine⟩ :=
    neg_blocks_triple vmi aExpr (sp-1088#64) sret (0x800035ec#64)
      ob0 ob1 ob2 ob3 kb0 kb1 kb2 kb3 d4 d5 d6 d7
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 q0 q1 q2 q3 q4 q5 q6 q7
      lb0 lb1 lb2 lb3 c.σ.regs.get? c.σ.sailOutput c.σ.mem c
      ⟨⟨⟨hG, rfl, rfl, hpc, hmi, hx8, hsp, hs1, hra, hcode, hopVal,
          (by ld_ok4 hop8 [hoc0, hoc1, hoc2, hoc3]),
          (by ld_ok8 haddr144 [hkb0, hkb1, hkb2, hkb3, hd4, hd5, hd6, hd7]),
          htick, (fun R _ _ => rfl)⟩,
         hcode,
         (by ld_ok8 haddr152 [hpb0, hpb1, hpb2, hpb3, hpb4, hpb5, hpb6, hpb7]),
         (by ld_ok8 haddr160 [hq0, hq1, hq2, hq3, hq4, hq5, hq6, hq7]),
         (by ld_ok4 haddr144 [hkb0, hkb1, hkb2, hkb3]),
         (by st_ok haddr240), (by st_ok haddr248), (by st_ok haddr256)⟩,
       hkindVal,
       (by ld_ok4 hline4 [hlb0, hlb1, hlb2, hlb3]),
       -- e→line window `[aExpr+4, aExpr+8)` disjoint from the three store windows
       (by intro k hk1 hk2
           rw [haddr240, haddr248, haddr256]
           refine ⟨?_, ?_, ?_⟩ <;>
             (rw [hline4] at hk1 hk2; rcases hexprSL with h | h <;> omega)),
       -- eval_expr code region `[0x80003164,0x80003fe0)` disjoint likewise
       (by intro k ⟨hk1, hk2⟩
           rw [haddr240, haddr248, haddr256]
           refine ⟨?_, ?_, ?_⟩ <;> (rcases hcodeStk with h | h <;> omega))⟩
  -- name the spine-exit config's components (the `neg_blocks_triple` exit config
  -- `cS`; its step count is `cS.steps`, threaded into the `jal` site below).
  let σ15 : MState := cS.σ
  let i15 : Nat := cS.tick
  -- bridge spine outputs → the domain names the downstream consumes
  have hmem15_3 : σ15.mem = m3 := by rw [hmem15_W]; exact hWm3
  have hx11_15 : σ15.regs.get? Register.x11 = some ((0#64) - payV) := hx11_15b
  have hout15 : σ15.sailOutput = c.σ.sailOutput := hout15_W
  have hVint_c : Value_intLoaded c.σ.mem := by
    refine loaded_value_int_agreeP mcall c.σ.mem (fun a ha => ?_) hVint
    rcases hmemFrame a (by rcases hviStk with h | h <;> omega) (by rcases hviArena with h | h <;> omega)
      with hin | heq
    · exact absurd hin (by rcases hviStk with h | h <;> omega)
    · exact heq.symm
  have hcode15 : Eval_exprLoaded σ15.mem := by
    rw [hmem15_3]
    refine loaded_eval_expr_agreeP c.σ.mem m3 (fun a ha => ?_) hcode
    show c.σ.mem[a]? = (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[a]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) a (sdData_val V14) (by rcases hcodeStk with h | h <;> omega)]
    show c.σ.mem[a]? = (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[a]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) a (sdData_val payV) (by rcases hcodeStk with h | h <;> omega)]
    show c.σ.mem[a]? = (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[a]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) a (sdData_val K13) (by rcases hcodeStk with h | h <;> omega)]
  have hVint15 : Value_intLoaded σ15.mem := by
    rw [hmem15_3]
    exact loaded_int_writeMap8 m2 (sp.toNat - 832) (sdData_val V14) (by rcases hviStk with h | h <;> omega)
      (loaded_int_writeMap8 m1 (sp.toNat - 840) (sdData_val payV) (by rcases hviStk with h | h <;> omega)
        (loaded_int_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val K13) (by rcases hviStk with h | h <;> omega) hVint_c))
  ------------------------------------------------------------------------
  -- 0x800039d8: jal value_int → PC := 0x8000280c, x1 := 0x800039dc
  ------------------------------------------------------------------------
  obtain ⟨σ16, i16, hs16', hi16, hG16, hmem16, hobs16⟩ :=
    site_800039d8_ee σ15 i15 cS.steps (0x800039d8#64) vmi15
      hG15 hpc15 hmi15 hcode15 rfl hi15
  have hstep16 : Step ⟨σ15, i15, cS.steps⟩ ⟨σ16, i16, cS.steps + 1⟩ := hs16'
  have hmem16_3 : σ16.mem = m3 := by rw [hmem16]; exact hmem15_3
  have hpc16 : σ16.regs.get? Register.PC = some (0x8000280c#64) := by
    have := obs_jal_pc hobs16
    rwa [show ((0x800039d8#64 : BitVec 64) + sign_extend (m := 64) (0x1fee34#21)) = 0x8000280c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink16 : σ16.regs.get? Register.x1 = some (0x800039dc#64) := by
    have := obs_jal_rd hobs16 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x800039d8#64 : BitVec 64) 4 = (0x800039dc#64:BitVec 64) from by decide] at this
  have hx10_16 : σ16.regs.get? Register.x10 = some sret := obs_jal_other' hobs16 Register.x10 (by decide) hx10_15
  have hx11_16 : σ16.regs.get? Register.x11 = some ((0#64) - payV) := obs_jal_other' hobs16 Register.x11 (by decide) hx11_15
  have hs1_16 : σ16.regs.get? Register.x9 = some sret := obs_jal_other' hobs16 Register.x9 (by decide) hs1_15
  have hsp_16 : σ16.regs.get? Register.x2 = some (sp-1088#64) := obs_jal_other' hobs16 Register.x2 (by decide) hsp_15
  obtain ⟨vmi16, hmi16⟩ := obs_jal_minstret hobs16
  have hout16 : σ16.sailOutput = c.σ.sailOutput := by rw [hobs16.out, sailOutput_sigmaPost_jal]; exact hout15
  have hVint16 : Value_intLoaded σ16.mem := by rw [hmem16_3, ← hmem15_3]; exact hVint15
  have hcode16 : Eval_exprLoaded σ16.mem := by rw [hmem16_3, ← hmem15_3]; exact hcode15
  ------------------------------------------------------------------------
  -- the value_int callee (via value_int_spec), buf = sret, pay = 0 - payV
  ------------------------------------------------------------------------
  have hIntRegion : IntRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hsretVi⟩
  have hcallpre : int_pre (fun R => σ16.regs.get? R) sret ((0#64) - payV) (0x800039dc#64) σ16.mem c.σ.sailOutput
      ⟨σ16, i16, cS.steps+1⟩ := by
    refine ⟨hG16, hVint16, rfl, hpc16, hx10_16, hx11_16, hlink16, ⟨vmi16, hmi16⟩, hi16, hIntRegion,
      (by decide), hout16, fun R _ => rfl⟩
  obtain ⟨cvi, hsvi, hGvi, hpcvi, hx10vi, hravi, ⟨vmivi, hmivi⟩, htickvi, hvalvi, houtvi,
      hmemframevi, hpresvi, hframevi⟩ :=
    value_int_spec (fun R => σ16.regs.get? R) sret ((0#64) - payV) (0x800039dc#64) N φc' σ16.mem c.σ.sailOutput
      ⟨σ16, i16, cS.steps+1⟩ hcallpre
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
  have hs1_fin : σ17.regs.get? Register.x9 = some sret := obs_jr_other' hobs17 Register.x9 (by decide) hs1_vi
  have hsp_fin : σ17.regs.get? Register.x2 = some (sp-1088#64) := obs_jr_other' hobs17 Register.x2 (by decide) hsp_vi
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
  -- `c.σ.mem` (the post-call memory) agrees with the epilogue-entry `σ17.mem`
  -- outside the whole-stack region `[SL.lo, SL.hi)`: the neg tail's own writes (the
  -- 3 error stores at `sp-{848,840,832}` and `value_int`'s `sret` write) ALL land
  -- inside `[SL.lo, SL.hi)` (`sp - 848 ≥ SL.lo` from `SL.lo+1088 ≤ sp`, `sret ∈ SL`).
  have hSL17 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = σ17.mem[k]? := by
    intro k hk
    rw [hmem17e, ← hmemframevi k (by rcases hsretInSL with ⟨hl, hr⟩; omega), hmem16_3]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-832) (sdData_val V14))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-832) k (sdData_val V14) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-840) (sdData_val payV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-840) k (sdData_val payV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-848) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-848) k (sdData_val K13) (by omega)]
  have hstore_fin : StoreRepr σ17.mem N A φf' φc' st'.store :=
    hstoreSurv' σ17.mem (fun k hk => hSL17 k hk)
  -- the `EvalExitD` upgrade clause (b): `[SL.lo,SL.hi)`-survival of `st'.store` at
  -- the exit memory `σ17.mem` — any `m'` agreeing with `σ17.mem` outside `SL` also
  -- agrees with `c.σ.mem` there (via `hSL17`), so `hstoreSurv'` applies.
  have hSurvSL_fin : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → σ17.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => (hSL17 k hk).trans (hm' k hk))
  -- the `EvalExitD` upgrade clause (a): `MemExtends m0 σ17.mem`. `m0 → mcall`
  -- is the threaded `mem_ext` residual (`hMemExtM0`, wave 47i — the totality
  -- oracle that used to make this trivial is REFUTED); every subsequent
  -- write only ADDS: `MemExtends mcall c.σ.mem` (`hMemExt`), the 3 error stores
  -- (`memExtends_writeMap8`), and `value_int`'s `sret` write (`hpresvi`).
  have hMemExt_m0_c : MemExtends m0 c.σ.mem := hMemExtM0.trans hMemExt
  have hMemExt_c_16 : MemExtends c.σ.mem σ16.mem := by
    rw [hmem16_3]
    exact ((MemExtends.refl c.σ.mem).trans
      (memExtends_writeMap8 c.σ.mem (sp.toNat - 848) (sdData_val K13))).trans
      ((memExtends_writeMap8 m1 (sp.toNat - 840) (sdData_val payV)).trans
        (memExtends_writeMap8 m2 (sp.toNat - 832) (sdData_val V14)))
  have hMemExt_16_17 : MemExtends σ16.mem σ17.mem := by
    intro a b hb; rw [hmem17e]; exact hpresvi a b hb
  have hMemExt_fin : MemExtends m0 σ17.mem :=
    (hMemExt_m0_c.trans hMemExt_c_16).trans hMemExt_16_17
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
    -- σ0→σ15 collapsed: the WHOLE spine frame in ONE application (Stage A2).
    -- The composed `neg_blocks_triple` frame relates σ15 to the σ0 entry map
    -- `c.σ.regs.get?` under the union of the three blocks' wrRegs guards, each
    -- discharged by `block_frame_wr` (the callee-saved `x8` disjunct in the tail
    -- guard closed by `he8` via the `assumption` fallback).  Was f_pro/f5/f_tail.
    have f_spine : σ15.regs.get? R = c.σ.regs.get? R :=
      hframeSpine R (abiNoise_noiseRegs hR') (by block_frame_wr [14, 15, 13])
        (by block_frame_wr [11, 14, 10]) (by block_frame_wr [12, 8, 11, 10])
    have f16 : σ16.regs.get? R = σ15.regs.get? R :=
      (hobs16.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' (abi_ne' (X := Register.x1) (by decide)) hnpc' hmii')
    have fvi : cvi.σ.regs.get? R = σ16.regs.get? R :=
      hframevi R ⟨abi_ne' (by decide), abi_ne' (by decide), hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have f17 : σ17.regs.get? R = cvi.σ.regs.get? R :=
      (hobs17.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f17, fvi, f16, f_spine]
    exact (hframe R hR').trans (hbridge R hR' he8 he9 he18 he2)
  ------------------------------------------------------------------------
  -- assemble the epilogue-entry package `PreEpilogueV` at the extended maps
  ------------------------------------------------------------------------
  refine ⟨⟨σ17, i17, cvi.steps + 1⟩, ?_, σ17.mem, φf', φc', hpf', hpc',
    ⟨?_, hMemExt_fin, hSurvSL_fin⟩⟩
  · exact hstepSpine.trans ((Steps.single hstep16).trans (hsvi.trans ((Steps.single hstep17))))
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
