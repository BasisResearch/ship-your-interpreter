import Vsa.Sim.EvalNegSim
import Vsa.Sim.EvalNegSim2
import Vsa.Sim.EvalNegSim3
import Vsa.Sim.EvalIntSim2
import Vsa.Sim.PinW
import Vsa.Sim.NotTailSites
import Vsa.Sim.NegBlockProto
import Vsa.Sim.BlockTactics2
import Vsa.Sim.BlockAdapter
import Vsa.Sim.BlockLogic
import Vsa.Sim.ValueSpec
import Vsa.Sim.ValueTruthySpec
import Vsa.Sim.EvalBoolSim
import Vsa.Sim.ReprCopy
import Vsa.Sim.DivSites2
import Vsa.Sim.ObsAvoid

/-!
# Layer 4 — M4 RECURSIVE case: `evalNotSim` (the `EvalE.not` case)

The fallthrough sibling of `neg` in the `EX_UNARY` arm. Both `.neg` and `.not`
share the arm head (`blockB_unary`, `EvalNegSim.lean`) that evaluates the operand
via the recursive `jal eval_expr`. They diverge at the post-call op-check
(`0x800035f8: beq a4,a5,0x800039ac` — TAKEN = neg; FALLTHROUGH = not).

Machine path for `.not` (`experiments/pctrace.md` + objdump):

```
800035ec: lw   a4,8(s0)        # op token
800035f0: li   a5,12           # T_MINUS = 12
800035f4: ld   a3,144(sp)      # sub-value v[0..8)  (kind dword)
800035f8: beq  a4,a5,800039ac  # NOT taken (op != 12) → fallthrough
800035fc: ld   a4,152(sp)      # v[8..16)   (payload)
80003600: ld   a5,160(sp)      # v[16..24)
80003604: addi a0,sp,64        # a0 := sp'+64 = sp-1024 (truthy arg buffer)
80003608: sd   a3,64(sp)       # copy v[0..8)  → buf
8000360c: sd   a4,72(sp)       # copy v[8..16) → buf+8
80003610: sd   a5,80(sp)       # copy v[16..24)→ buf+16
80003614: jal  value_truthy    # value_truthy(buf); ra = 0x80003618
80003618: seqz a1,a0           # a1 := (a0 == 0) = !v.truthy
8000361c: mv   a0,s1           # a0 := outer sret
80003620: jal  value_bool      # value_bool(sret, !v.truthy); ra = 0x80003624
80003624: j    800033ec        # shared epilogue → blockD_v_rec
```

`blockC_not` reproduces the whole tail (`SubEvalReturn @0x800035ec` with the
`beq` NOT taken → `PreEpilogueVD` at value `.bool (!vsub.truthy)`), threading the
24-byte `Value` copy into the truthy arg buffer (`valueRepr_copy_of_writeWindow`),
`value_truthy_spec` (strengthened with output invariance), the `seqz` bridge, and
`value_bool_spec_full`. `evalNotSim` then composes `blockA_k ≫ blockB_unary ≫
blockC_not ≫ blockD_v_rec` in the `EvalIH` motive shape, mirroring `evalNegSim`.

Conditional (like `evalNegSim`) ONLY on the `NegExtras` geometry (reused verbatim
where the fields fit, plus the NOT-tail-specific buffer geometry `NotExtras`) and
`hMcallPop` (M6 Layout).

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

/-! ## `Value_truthyLoaded` survives a disjoint 8-byte store / an agreement -/

/-- `Value_truthyLoaded` (12 code words at `[0x8000282c, 0x8000285c)`) survives a
disjoint 8-byte store. -/
theorem loaded_truthy_writeMap8 (mem : Mem) (a8 : Nat) (d : BitVec (8 * 8))
    (hdis : a8 + 8 ≤ 0x8000282c ∨ 0x8000285c ≤ a8) (h : Value_truthyLoaded mem) :
    Value_truthyLoaded (writeMap8 mem a8 d) := by
  simp only [Value_truthyLoaded, value_truthyChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [getElem_writeMap8_disjoint mem a8 _ d (by omega)]; simp_all only [])

/-- `Value_truthyLoaded` survives an agreement on `value_truthy`'s code region. -/
theorem loaded_truthy_agreeP (m m' : Mem)
    (ha : ∀ a, (0x8000282c ≤ a ∧ a < 0x8000285c) → m[a]? = m'[a]?)
    (h : Value_truthyLoaded m) : Value_truthyLoaded m' := by
  simp only [Value_truthyLoaded, value_truthyChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; simp_all only [])

/-- `Value_boolLoaded` survives an agreement on `value_bool`'s code region
`[0x800027f8, 0x8000280c)`. -/
theorem loaded_bool_agreeP (m m' : Mem)
    (ha : ∀ a, (0x800027f8 ≤ a ∧ a < 0x8000280c) → m[a]? = m'[a]?)
    (h : Value_boolLoaded m) : Value_boolLoaded m' := by
  simp only [Value_boolLoaded, value_boolChunk0] at h ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (rw [← ha _ (by omega)]; simp_all only [])

/-! ## The `seqz` bridge: `!v.truthy` as a `.bool` payload

`value_truthy` returns `a0 = cond v.truthy 1 0`. `seqz a1,a0` computes
`a1 = zext (bool_to_bit (a0 <u 1)) = (a0 == 0)`. `value_bool` produces
`.bool (a1 != 0)`. We show `.bool (a1 != 0) = .bool (!v.truthy)`. -/
theorem seqz_truthy_bridge (v : Value) :
    (zero_extend (m := 64)
        (bool_to_bit (zopz0zI_u (cond (Value.truthy v) (1#64) (0#64)) (sign_extend (m := 64) (0x001#12))))
      != 0#64) = (!Value.truthy v) := by
  have h1 : (sign_extend (m := 64) (0x001#12) : BitVec 64) = 1#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  rw [h1]
  by_cases h : Value.truthy v
  · -- truthy: a0 = 1, (1 <u 1) = false, seqz = 0, so (0 != 0) = false = !true
    rw [h]; decide
  · -- falsy: a0 = 0, (0 <u 1) = true, seqz = 1, so (1 != 0) = true = !false
    simp only [Bool.not_eq_true] at h
    rw [h]; decide

/-! ## Store-byte extraction for the 24-byte copy

Each of the three copy stores writes `sdData_val (sign_extend (m:=64) (b7++…++b0))`
into an 8-byte window; byte `k` of that window reads back exactly `bk` (the byte
that was loaded from the source). `sdData_val` is the identity and the `sign_extend`
of a width-64 word is the identity, so `extractLsb' (8k) 8` of the appended bytes
selects `bk`. -/
theorem sdData_sext_bytes (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) :
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 0 8 = b0 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 8 8 = b1 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 16 8 = b2 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 24 8 = b3 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 32 8 = b4 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 40 8 = b5 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 48 8 = b6 ∧
    (sdData_val (sign_extend (m := 64)
        ((((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0)
          : BitVec (8*8)))).extractLsb' 56 8 = b7 := by
  rw [sdData_val_id, sext_full]
  have h0 := b0.isLt; have h1 := b1.isLt; have h2 := b2.isLt; have h3 := b3.isLt
  have h4 := b4.isLt; have h5 := b5.isLt; have h6 := b6.isLt; have h7 := b7.isLt
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (apply BitVec.eq_of_toNat_eq
     simp only [BitVec.extractLsb', BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
     rw [word8_toNat_recon]; omega)

/-! ## `NotExtras` — the NOT-tail buffer geometry (beyond `NegExtras`)

The truthy arg buffer lives at `sp - 1024` (`sp'+64`). It must be a valid 24-byte
`Value` region (RAM, 8-aligned, above HTIF), disjoint from the two callees' code,
the arena, and — for the `valueRepr_copy_of_writeWindow` — the operand value's
string/native payload pointer (which lives in the arena, disjoint from the C
stack). These are the NOT-analogue of `blockC_neg`'s error-store geometry. -/
structure NotExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φc' : Addr → Nat)
    (vsub : Value) (sp sret : BitVec 64) (m : Mem) : Prop where
  -- the truthy arg buffer `[sp-1024, sp-1000)` region facts
  buf_lo : 0x80000000 + 1024 ≤ sp.toNat
  buf_win : tohostAddr + 16 + 1024 ≤ sp.toNat
  -- the operand value's string/native payload (pointer read at subsret+8) lives
  -- disjoint from the truthy arg buffer window `[sp-1024, sp-1000)`. Its target is
  -- in the arena (heap), disjoint from the C stack; a full M6 Layout supplies it.
  pay_disj : ∀ (p : Nat) (s : String),
    ValueRepr m N φc' (sp.toNat - 944) vsub → read64 m (sp.toNat - 944 + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)

/-! ## `blockC_not` — the post-call `not` tail -/

theorem blockC_not
    (gpre g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (nf nc : Nat)
    (st' : Vsa.While.St) (vsub : Value)
    (sp r sret aExpr : BitVec 64) (v8 v9 v18 : BitVec 64) (out0 : Array String)
    (esub : Expr) (m0 : Mem) :
    Triple
      (fun c => ∃ mcall,
        SubEvalReturn gpre N A SL φf φc nf nc st' vsub sp r sret
          ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)) (0x800035ec#64)
          v8 v9 v18 mcall c ∧
        gpre Register.x8 = some aExpr ∧
        ExprRepr mcall aExpr.toNat (.unary .not esub) ∧
        (∀ a : Nat, (∃ b, mcall[a]? = some b)) ∧
        aExpr.toNat % 4 = 0 ∧
        0x80000000 ≤ aExpr.toNat ∧ aExpr.toNat + 16 ≤ 0x100000000 ∧
        tohostAddr + 8 ≤ aExpr.toNat ∧
        (aExpr.toNat + 16 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat) ∧
        (aExpr.toNat + 16 ≤ sp.toNat - 944 ∨ sp.toNat - 944 + 24 ≤ aExpr.toNat) ∧
        String.join out0.toList = st'.out ∧
        sret.toNat % 8 = 0 ∧ 0x80000000 ≤ sret.toNat ∧ sret.toNat + 24 ≤ 0x100000000 ∧
        tohostAddr + 16 ≤ sret.toNat ∧
        (sret.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ sret.toNat) ∧
        (sret.toNat + 24 ≤ 0x80003164 ∨ 0x80003fe0 ≤ sret.toNat) ∧
        r.toNat % 4 = 0 ∧
        SL.lo + 1088 ≤ sp.toNat ∧ 0x80000000 ≤ SL.lo ∧ tohostAddr + 16 ≤ SL.lo ∧
        c.σ.sailOutput = out0 ∧
        Value_truthyLoaded mcall ∧ Value_boolLoaded mcall ∧
        (∀ φc' : Addr → Nat, ValueRepr c.σ.mem N φc' (sp.toNat - 944) vsub →
          NotExtras N A SL φc' vsub sp sret c.σ.mem) ∧
        -- value_truthy code `[0x8000282c, 0x8000285c)` disjoint from the stack
        (sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo) ∧
        -- value_bool code `[0x800027f8, 0x8000280c)` disjoint from the stack
        (sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo) ∧
        -- the outer sret buffer disjoint from value_bool code (BoolRegion.code_disjoint)
        (sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat) ∧
        -- value_truthy / value_bool code disjoint from the arena
        (A.hi ≤ 0x8000282c ∨ 0x8000285c ≤ A.lo) ∧
        (A.hi ≤ 0x800027f8 ∨ 0x8000280c ≤ A.lo) ∧
        (sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo) ∧
        (SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi) ∧
        (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
          mcall[a]? = m0[a]?) ∧
        sp.toNat ≤ 0x100000000 ∧ sp.toNat % 8 = 0 ∧ SL.hi ≤ 0x100000000 ∧ sp.toNat ≤ SL.hi ∧
        g Register.x8 = some v8 ∧ g Register.x9 = some v9 ∧
        g Register.x18 = some v18 ∧ g Register.x2 = some sp ∧
        (∀ R : Register, AbiPreservedNoise R →
          (Register.x8 == R) = false → (Register.x9 == R) = false →
          (Register.x18 == R) = false → (Register.x2 == R) = false →
          gpre R = g R))
      (fun c => ∃ (mpre : Mem) (φfe φce : Addr → Nat),
        PhiExtends φf φfe nf ∧
        PhiExtends φc φce nc ∧
        PreEpilogueVD g N A SL φfe φce st' (.bool (!vsub.truthy)) sp r sret v8 v9 v18 out0 m0 mpre c) := by
  intro c hpre
  obtain ⟨mcall, hSub, hgx8, hexpr, hStackPop, hexprAl, hexprLo, hexprHi, hexprWin,
    hexprSL, hexprA, hexprSub,
    houtStr, hsretAl, hsretLo, hsretHi, hsretWin, hsretStk, hsretEvalCode,
    hraAl, hSLloSp, hSLlo, hSLwin,
    hout0eq, hVtruthyMcall, hVboolMcall, hNotExtras, hTruthyStk, hBoolStk, hSretBoolCode,
    hTruthyArena, hBoolArena, hcodeStk, hsretInSL, hMcallM0,
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
  -- the sub-value at subsret = sp-944 at c.σ.mem (φcv-extended)
  have hvalSub' : ValueRepr c.σ.mem N φcv (sp.toNat - 944) vsub := by rwa [hsub944] at hvalSub
  -- the NOT-tail buffer geometry, instantiated at φcv
  have hNE : NotExtras N A SL φcv vsub sp sret c.σ.mem := hNotExtras φcv hvalSub'
  -- === derive machine facts ===
  -- x8 = aExpr (callee-saved survives the sub-call)
  have hx8 : c.σ.regs.get? Register.x8 = some aExpr := (hframe Register.x8 (by decide)).trans hgx8
  -- op-token addr aExpr+8
  have hop8 : (aExpr + sign_extend (m := 64) (0x008#12)).toNat = aExpr.toNat + 8 := by
    have hs : (sign_extend (m := 64) (0x008#12) : BitVec 64) = 8#64 := by
      apply BitVec.eq_of_toNat_eq; decide
    rw [hs, BitVec.toNat_add]; have hv : (8#64 : BitVec 64).toNat = 8 := by decide
    rw [hv]; have := aExpr.isLt; rw [Nat.mod_eq_of_lt (by omega)]
  -- ExprRepr (.unary .not esub): kind = 8, op-token = unOpTok .not = 16
  obtain ⟨aptr, hk8, hoptok, hpayptr, hsubR⟩ : ∃ p,
      read32 mcall aExpr.toNat = some 8 ∧ read32 mcall (aExpr.toNat + 8) = some (unOpTok .not) ∧
      read64 mcall (aExpr.toNat + 16) = some p ∧ ExprRepr mcall p esub := by
    cases hexpr with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  have hoptok16 : read32 mcall (aExpr.toNat + 8) = some 16 := by simpa [unOpTok] using hoptok
  obtain ⟨ob0, ob1, ob2, ob3, hob0, hob1, hob2, hob3, hobrec⟩ :=
    read32_bytes mcall (aExpr.toNat + 8) 16 hoptok16
  -- op-token bytes with VALUE in c.σ.mem: aExpr node is AST memory, agrees with mcall.
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
  -- the op-token loaded value = 16#64 (T_NOT), the li a5,12 = 12#64
  have hopVal : (sign_extend (m := 64) ((((ob3.append ob2).append ob1).append ob0) : BitVec (8*4)))
      = (16#64 : BitVec 64) := by
    rw [sext_word_small _ 16 (by decide) (by rw [word_toNat_recon]; exact hobrec)]
  have hli12 : ((0#64 : BitVec 64) + sign_extend (m := 64) (0x00c#12)) = (12#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hne1612 : ((16#64 : BitVec 64) == (12#64 : BitVec 64)) = false := by decide
  -- the whole 24-byte sub-Value buffer bytes at c.σ.mem[sp-944 .. +24) (present).
  -- kind dword (a3, ld 144), payload (a4, ld 152), v[16..24) (a5, ld 160).
  have hStackPopC : ∀ a : Nat, ∃ b, c.σ.mem[a]? = some b :=
    fun a => stackpop_present hMemExt hStackPop a
  obtain ⟨kb0, hkb0⟩ := hStackPopC (sp.toNat - 944)
  obtain ⟨kb1, hkb1⟩ := hStackPopC (sp.toNat - 944 + 1)
  obtain ⟨kb2, hkb2⟩ := hStackPopC (sp.toNat - 944 + 2)
  obtain ⟨kb3, hkb3⟩ := hStackPopC (sp.toNat - 944 + 3)
  obtain ⟨kb4, hkb4⟩ := hStackPopC (sp.toNat - 944 + 4)
  obtain ⟨kb5, hkb5⟩ := hStackPopC (sp.toNat - 944 + 5)
  obtain ⟨kb6, hkb6⟩ := hStackPopC (sp.toNat - 944 + 6)
  obtain ⟨kb7, hkb7⟩ := hStackPopC (sp.toNat - 944 + 7)
  obtain ⟨pb0, hpb0⟩ := hStackPopC (sp.toNat - 936)
  obtain ⟨pb1, hpb1⟩ := hStackPopC (sp.toNat - 936 + 1)
  obtain ⟨pb2, hpb2⟩ := hStackPopC (sp.toNat - 936 + 2)
  obtain ⟨pb3, hpb3⟩ := hStackPopC (sp.toNat - 936 + 3)
  obtain ⟨pb4, hpb4⟩ := hStackPopC (sp.toNat - 936 + 4)
  obtain ⟨pb5, hpb5⟩ := hStackPopC (sp.toNat - 936 + 5)
  obtain ⟨pb6, hpb6⟩ := hStackPopC (sp.toNat - 936 + 6)
  obtain ⟨pb7, hpb7⟩ := hStackPopC (sp.toNat - 936 + 7)
  obtain ⟨qb0, hqb0⟩ := hStackPopC (sp.toNat - 928)
  obtain ⟨qb1, hqb1⟩ := hStackPopC (sp.toNat - 928 + 1)
  obtain ⟨qb2, hqb2⟩ := hStackPopC (sp.toNat - 928 + 2)
  obtain ⟨qb3, hqb3⟩ := hStackPopC (sp.toNat - 928 + 3)
  obtain ⟨qb4, hqb4⟩ := hStackPopC (sp.toNat - 928 + 4)
  obtain ⟨qb5, hqb5⟩ := hStackPopC (sp.toNat - 928 + 5)
  obtain ⟨qb6, hqb6⟩ := hStackPopC (sp.toNat - 928 + 6)
  obtain ⟨qb7, hqb7⟩ := hStackPopC (sp.toNat - 928 + 7)
  -- the three load values reassembled
  let K13 : BitVec 64 := sign_extend (m := 64)
    ((((((((kb7.append kb6).append kb5).append kb4).append kb3).append kb2).append kb1).append kb0) : BitVec (8*8))
  let PV : BitVec 64 := sign_extend (m := 64)
    ((((((((pb7.append pb6).append pb5).append pb4).append pb3).append pb2).append pb1).append pb0) : BitVec (8*8))
  let QV : BitVec 64 := sign_extend (m := 64)
    ((((((((qb7.append qb6).append qb5).append qb4).append qb3).append qb2).append qb1).append qb0) : BitVec (8*8))
  -- addresses of the tail loads (144/152/160) and stores (64/72/80) as sp - k
  have haddr144 : ((sp - 1088#64) + sign_extend (m := 64) (0x090#12)).toNat = sp.toNat - 944 := hsub944
  have haddr152 : ((sp - 1088#64) + sign_extend (m := 64) (0x098#12)).toNat = sp.toNat - 936 :=
    spill_addr sp (0x098#12) 936 (by decide) (by omega) hsp1088
  have haddr160 : ((sp - 1088#64) + sign_extend (m := 64) (0x0a0#12)).toNat = sp.toNat - 928 :=
    spill_addr sp (0x0a0#12) 928 (by decide) (by omega) hsp1088
  have haddr64 : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 :=
    spill_addr sp (0x040#12) 1024 (by decide) (by omega) hsp1088
  have haddr72 : ((sp - 1088#64) + sign_extend (m := 64) (0x048#12)).toNat = sp.toNat - 1016 :=
    spill_addr sp (0x048#12) 1016 (by decide) (by omega) hsp1088
  have haddr80 : ((sp - 1088#64) + sign_extend (m := 64) (0x050#12)).toNat = sp.toNat - 1008 :=
    spill_addr sp (0x050#12) 1008 (by decide) (by omega) hsp1088
  ------------------------------------------------------------------------
  -- 0x800035ec → 0x80003614: op check (beq NOT taken), 3 loads, addi, 3 stores.
  ------------------------------------------------------------------------
  -- 0x800035ec: lw a4,8(s0) → x14 := 13 (op token)
  obtain ⟨σ1, i1, hs1', hi1, hG1, hmem1, hobs1⟩ :=
    site_800035ec_ee c.σ c.tick c.steps (0x800035ec#64) vmi aExpr
      ob0 ob1 ob2 ob3 hG hpc hmi hx8 hcode rfl
      (by rw [hop8]; omega) (by rw [hop8]; omega)
      (by rw [hop8, htoh]; right; omega) (by rw [hop8]; omega)
      (by rw [hop8]; exact hoc0) (by rw [hop8]; exact hoc1)
      (by rw [hop8]; exact hoc2) (by rw [hop8]; exact hoc3) htick
  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1'
  have hmem1e : σ1.mem = c.σ.mem := hmem1
  have hpc1 : σ1.regs.get? Register.PC = some (0x800035f0#64) := by
    have := obs_alu_pc hobs1
    rwa [show BitVec.addInt (0x800035ec#64) 4 = (0x800035f0#64 : BitVec 64) from by decide] at this
  have hx14_1 : σ1.regs.get? Register.x14 = some (16#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hopVal] at this
  have hs1_1 : σ1.regs.get? Register.x9 = some sret := obs_alu_other' hobs1 Register.x9 (by decide) hs1
  have hsp_1 : σ1.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs1 Register.x2 (by decide) hsp
  have hx8_1 : σ1.regs.get? Register.x8 = some aExpr := obs_alu_other' hobs1 Register.x8 (by decide) hx8
  obtain ⟨vmi1, hmi1⟩ := obs_alu_minstret hobs1
  have hout1 : σ1.sailOutput = out0 := by rw [hobs1.out, sailOutput_sigmaPost_alu]; exact hout0eq
  have hcode1 : Eval_exprLoaded σ1.mem := by rw [hmem1e]; exact hcode
  -- 0x800035f0: li a5,12 → x15 := 12
  obtain ⟨σ2, i2, hs2', hi2, hG2, hmem2, hobs2⟩ :=
    site_800035f0_ee σ1 i1 (c.steps + 1) (0x800035f0#64) vmi1 hG1 hpc1 hmi1 hcode1 rfl hi1
  have hstep2 : Step ⟨σ1, i1, c.steps + 1⟩ ⟨σ2, i2, c.steps + 1 + 1⟩ := hs2'
  have hmem2e : σ2.mem = c.σ.mem := by rw [hmem2]; exact hmem1e
  have hpc2 : σ2.regs.get? Register.PC = some (0x800035f4#64) := by
    have := obs_alu_pc hobs2
    rwa [show BitVec.addInt (0x800035f0#64) 4 = (0x800035f4#64 : BitVec 64) from by decide] at this
  have hx15_2 : σ2.regs.get? Register.x15 = some (12#64) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hli12] at this
  have hx14_2 : σ2.regs.get? Register.x14 = some (16#64) := obs_alu_other' hobs2 Register.x14 (by decide) hx14_1
  have hs1_2 : σ2.regs.get? Register.x9 = some sret := obs_alu_other' hobs2 Register.x9 (by decide) hs1_1
  have hsp_2 : σ2.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs2 Register.x2 (by decide) hsp_1
  obtain ⟨vmi2, hmi2⟩ := obs_alu_minstret hobs2
  have hout2 : σ2.sailOutput = out0 := by rw [hobs2.out, sailOutput_sigmaPost_alu]; exact hout1
  have hcode2 : Eval_exprLoaded σ2.mem := by rw [hmem2e]; exact hcode
  -- 0x800035f4: ld a3,144(sp) → x13 := K13 (kind dword)
  obtain ⟨σ3, i3, hs3', hi3, hG3, hmem3, hobs3⟩ :=
    site_800035f4_ee σ2 i2 (c.steps + 1 + 1) (0x800035f4#64) vmi2 (sp - 1088#64)
      kb0 kb1 kb2 kb3 kb4 kb5 kb6 kb7 hG2 hpc2 hmi2 hsp_2 hcode2 rfl
      (by rw [haddr144]; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, htoh]; right; omega) (by rw [haddr144]; omega)
      (by rw [haddr144, hmem2e]; exact hkb0) (by rw [haddr144, hmem2e]; exact hkb1)
      (by rw [haddr144, hmem2e]; exact hkb2) (by rw [haddr144, hmem2e]; exact hkb3)
      (by rw [haddr144, hmem2e]; exact hkb4) (by rw [haddr144, hmem2e]; exact hkb5)
      (by rw [haddr144, hmem2e]; exact hkb6) (by rw [haddr144, hmem2e]; exact hkb7) hi2
  have hstep3 : Step ⟨σ2, i2, c.steps + 1 + 1⟩ ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ := hs3'
  have hmem3e : σ3.mem = c.σ.mem := by rw [hmem3]; exact hmem2e
  have hpc3 : σ3.regs.get? Register.PC = some (0x800035f8#64) := by
    have := obs_alu_pc hobs3
    rwa [show BitVec.addInt (0x800035f4#64) 4 = (0x800035f8#64 : BitVec 64) from by decide] at this
  have hx13_3 : σ3.regs.get? Register.x13 = some K13 :=
    obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx14_3 : σ3.regs.get? Register.x14 = some (16#64) := obs_alu_other' hobs3 Register.x14 (by decide) hx14_2
  have hx15_3 : σ3.regs.get? Register.x15 = some (12#64) := obs_alu_other' hobs3 Register.x15 (by decide) hx15_2
  have hs1_3 : σ3.regs.get? Register.x9 = some sret := obs_alu_other' hobs3 Register.x9 (by decide) hs1_2
  have hsp_3 : σ3.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs3 Register.x2 (by decide) hsp_2
  obtain ⟨vmi3, hmi3⟩ := obs_alu_minstret hobs3
  have hout3 : σ3.sailOutput = out0 := by rw [hobs3.out, sailOutput_sigmaPost_alu]; exact hout2
  have hcode3 : Eval_exprLoaded σ3.mem := by rw [hmem3e]; exact hcode
  -- 0x800035f8: beq a4,a5 (NOT taken, 13 != 12) → 0x800035fc
  obtain ⟨σ4, i4, hs4', hi4, hG4, hmem4, hobs4⟩ :=
    site_800035f8_nottaken_ee σ3 i3 (c.steps + 1 + 1 + 1) (0x800035f8#64) vmi3 (16#64) (12#64)
      hG3 hpc3 hmi3 hx14_3 hx15_3 hcode3 rfl hne1612 hi3
  have hstep4 : Step ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ := hs4'
  have hmem4e : σ4.mem = c.σ.mem := by rw [hmem4]; exact hmem3e
  have hpc4 : σ4.regs.get? Register.PC = some (0x800035fc#64) := by
    have := obs_branch_nottaken_pc hobs4
    rwa [show BitVec.addInt (0x800035f8#64) 4 = (0x800035fc#64 : BitVec 64) from by decide] at this
  have hx13_4 : σ4.regs.get? Register.x13 = some K13 := obs_branch_nottaken_other' hobs4 Register.x13 (by decide) hx13_3
  have hs1_4 : σ4.regs.get? Register.x9 = some sret := obs_branch_nottaken_other' hobs4 Register.x9 (by decide) hs1_3
  have hsp_4 : σ4.regs.get? Register.x2 = some (sp - 1088#64) := obs_branch_nottaken_other' hobs4 Register.x2 (by decide) hsp_3
  obtain ⟨vmi4, hmi4⟩ := obs_branch_nottaken_minstret hobs4
  have hout4 : σ4.sailOutput = out0 := by rw [hobs4.out, sailOutput_sigmaPost_branch_nottaken]; exact hout3
  have hcode4 : Eval_exprLoaded σ4.mem := by rw [hmem4e]; exact hcode
  -- 0x800035fc: ld a4,152(sp) → x14 := PV
  obtain ⟨σ5, i5, hs5', hi5, hG5, hmem5, hobs5⟩ :=
    site_800035fc_ee σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x800035fc#64) vmi4 (sp - 1088#64)
      pb0 pb1 pb2 pb3 pb4 pb5 pb6 pb7 hG4 hpc4 hmi4 hsp_4 hcode4 rfl
      (by rw [haddr152]; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, htoh]; right; omega) (by rw [haddr152]; omega)
      (by rw [haddr152, hmem4e]; exact hpb0) (by rw [haddr152, hmem4e]; exact hpb1)
      (by rw [haddr152, hmem4e]; exact hpb2) (by rw [haddr152, hmem4e]; exact hpb3)
      (by rw [haddr152, hmem4e]; exact hpb4) (by rw [haddr152, hmem4e]; exact hpb5)
      (by rw [haddr152, hmem4e]; exact hpb6) (by rw [haddr152, hmem4e]; exact hpb7) hi4
  have hstep5 : Step ⟨σ4, i4, c.steps + 1 + 1 + 1 + 1⟩ ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := hs5'
  have hmem5e : σ5.mem = c.σ.mem := by rw [hmem5]; exact hmem4e
  have hpc5 : σ5.regs.get? Register.PC = some (0x80003600#64) := by
    have := obs_alu_pc hobs5
    rwa [show BitVec.addInt (0x800035fc#64) 4 = (0x80003600#64 : BitVec 64) from by decide] at this
  have hx14_5 : σ5.regs.get? Register.x14 = some PV :=
    obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx13_5 : σ5.regs.get? Register.x13 = some K13 := obs_alu_other' hobs5 Register.x13 (by decide) hx13_4
  have hs1_5 : σ5.regs.get? Register.x9 = some sret := obs_alu_other' hobs5 Register.x9 (by decide) hs1_4
  have hsp_5 : σ5.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs5 Register.x2 (by decide) hsp_4
  obtain ⟨vmi5, hmi5⟩ := obs_alu_minstret hobs5
  have hout5 : σ5.sailOutput = out0 := by rw [hobs5.out, sailOutput_sigmaPost_alu]; exact hout4
  have hcode5 : Eval_exprLoaded σ5.mem := by rw [hmem5e]; exact hcode
  -- 0x80003600: ld a5,160(sp) → x15 := QV
  obtain ⟨σ6, i6, hs6', hi6, hG6, hmem6, hobs6⟩ :=
    site_80003600_ee σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80003600#64) vmi5 (sp - 1088#64)
      qb0 qb1 qb2 qb3 qb4 qb5 qb6 qb7 hG5 hpc5 hmi5 hsp_5 hcode5 rfl
      (by rw [haddr160]; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, htoh]; right; omega) (by rw [haddr160]; omega)
      (by rw [haddr160, hmem5e]; exact hqb0) (by rw [haddr160, hmem5e]; exact hqb1)
      (by rw [haddr160, hmem5e]; exact hqb2) (by rw [haddr160, hmem5e]; exact hqb3)
      (by rw [haddr160, hmem5e]; exact hqb4) (by rw [haddr160, hmem5e]; exact hqb5)
      (by rw [haddr160, hmem5e]; exact hqb6) (by rw [haddr160, hmem5e]; exact hqb7) hi5
  have hstep6 : Step ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs6'
  have hmem6e : σ6.mem = c.σ.mem := by rw [hmem6]; exact hmem5e
  have hpc6 : σ6.regs.get? Register.PC = some (0x80003604#64) := by
    have := obs_alu_pc hobs6
    rwa [show BitVec.addInt (0x80003600#64) 4 = (0x80003604#64 : BitVec 64) from by decide] at this
  have hx15_6 : σ6.regs.get? Register.x15 = some QV :=
    obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx13_6 : σ6.regs.get? Register.x13 = some K13 := obs_alu_other' hobs6 Register.x13 (by decide) hx13_5
  have hx14_6 : σ6.regs.get? Register.x14 = some PV := obs_alu_other' hobs6 Register.x14 (by decide) hx14_5
  have hs1_6 : σ6.regs.get? Register.x9 = some sret := obs_alu_other' hobs6 Register.x9 (by decide) hs1_5
  have hsp_6 : σ6.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs6 Register.x2 (by decide) hsp_5
  obtain ⟨vmi6, hmi6⟩ := obs_alu_minstret hobs6
  have hout6 : σ6.sailOutput = out0 := by rw [hobs6.out, sailOutput_sigmaPost_alu]; exact hout5
  have hcode6 : Eval_exprLoaded σ6.mem := by rw [hmem6e]; exact hcode
  -- 0x80003604: addi a0,sp,64 → x10 := (sp-1088)+64 = sp-1024 (buf)
  obtain ⟨σ7, i7, hs7', hi7, hG7, hmem7, hobs7⟩ :=
    site_80003604_ee σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80003604#64) vmi6 (sp - 1088#64)
      hG6 hpc6 hmi6 hsp_6 hcode6 rfl hi6
  have hstep7 : Step ⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs7'
  have hmem7e : σ7.mem = c.σ.mem := by rw [hmem7]; exact hmem6e
  have hpc7 : σ7.regs.get? Register.PC = some (0x80003608#64) := by
    have := obs_alu_pc hobs7
    rwa [show BitVec.addInt (0x80003604#64) 4 = (0x80003608#64 : BitVec 64) from by decide] at this
  have hx10_7 : σ7.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hx13_7 : σ7.regs.get? Register.x13 = some K13 := obs_alu_other' hobs7 Register.x13 (by decide) hx13_6
  have hx14_7 : σ7.regs.get? Register.x14 = some PV := obs_alu_other' hobs7 Register.x14 (by decide) hx14_6
  have hx15_7 : σ7.regs.get? Register.x15 = some QV := obs_alu_other' hobs7 Register.x15 (by decide) hx15_6
  have hs1_7 : σ7.regs.get? Register.x9 = some sret := obs_alu_other' hobs7 Register.x9 (by decide) hs1_6
  have hsp_7 : σ7.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs7 Register.x2 (by decide) hsp_6
  obtain ⟨vmi7, hmi7⟩ := obs_alu_minstret hobs7
  have hout7 : σ7.sailOutput = out0 := by rw [hobs7.out, sailOutput_sigmaPost_alu]; exact hout6
  have hcode7 : Eval_exprLoaded σ7.mem := by rw [hmem7e]; exact hcode
  -- the buffer address value
  have hbufaddr : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)).toNat = sp.toNat - 1024 := haddr64
  ------------------------------------------------------------------------
  -- 0x80003608 / 360c / 3610: the three copy stores. Memory towers m1/m2/m3.
  ------------------------------------------------------------------------
  let m1 : Mem := writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13)
  let m2 : Mem := writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)
  let m3 : Mem := writeMap8 m2 (sp.toNat - 1008) (sdData_val QV)
  -- 0x80003608: sd a3,64(sp) → m1
  obtain ⟨σ8, i8, hs8', hi8, hG8, hmem8, hobs8⟩ :=
    site_80003608_ee σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003608#64) vmi7 (sp - 1088#64) K13
      hG7 hpc7 hmi7 hsp_7 hx13_7 hcode7 rfl
      (by rw [haddr64]; omega) (by rw [haddr64]; omega) (by rw [haddr64, htoh]; omega) (by rw [haddr64]; omega) hi7
  have hstep8 : Step ⟨σ7, i7, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs8'
  have hmem8e : σ8.mem = m1 := by
    rw [hmem8, mem_afterNextPC, haddr64, hmem7e]
  have hpc8 : σ8.regs.get? Register.PC = some (0x8000360c#64) := by
    have := obs_store_pc_val hobs8
    rwa [show BitVec.addInt (0x80003608#64) 4 = (0x8000360c#64 : BitVec 64) from by decide] at this
  have hx10_8 := obs_store_other_val' hobs8 Register.x10 (by decide) hx10_7
  have hx14_8 := obs_store_other_val' hobs8 Register.x14 (by decide) hx14_7
  have hx15_8 := obs_store_other_val' hobs8 Register.x15 (by decide) hx15_7
  have hs1_8 := obs_store_other_val' hobs8 Register.x9 (by decide) hs1_7
  have hsp_8 := obs_store_other_val' hobs8 Register.x2 (by decide) hsp_7
  obtain ⟨vmi8, hmi8⟩ := obs_store_minstret_val hobs8
  have hout8 : σ8.sailOutput = out0 := by rw [hobs8.out, sailOutput_sigmaPost_store]; exact hout7
  have hcode8 : Eval_exprLoaded σ8.mem := by
    rw [hmem8e]
    exact loaded_eval_expr_agreeP c.σ.mem m1
      (fun k hk => (getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13)
        (by rcases hcodeStk with h | h <;> omega)).symm) hcode
  -- 0x8000360c: sd a4,72(sp) → m2
  obtain ⟨σ9, i9, hs9', hi9, hG9, hmem9, hobs9⟩ :=
    site_8000360c_ee σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x8000360c#64) vmi8 (sp - 1088#64) PV
      hG8 hpc8 hmi8 hsp_8 hx14_8 hcode8 rfl
      (by rw [haddr72]; omega) (by rw [haddr72]; omega) (by rw [haddr72, htoh]; omega) (by rw [haddr72]; omega) hi8
  have hstep9 : Step ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs9'
  have hmem9e : σ9.mem = m2 := by
    rw [hmem9, mem_afterNextPC, haddr72, hmem8e]
  have hpc9 : σ9.regs.get? Register.PC = some (0x80003610#64) := by
    have := obs_store_pc_val hobs9
    rwa [show BitVec.addInt (0x8000360c#64) 4 = (0x80003610#64 : BitVec 64) from by decide] at this
  have hx10_9 := obs_store_other_val' hobs9 Register.x10 (by decide) hx10_8
  have hx15_9 := obs_store_other_val' hobs9 Register.x15 (by decide) hx15_8
  have hs1_9 := obs_store_other_val' hobs9 Register.x9 (by decide) hs1_8
  have hsp_9 := obs_store_other_val' hobs9 Register.x2 (by decide) hsp_8
  obtain ⟨vmi9, hmi9⟩ := obs_store_minstret_val hobs9
  have hout9 : σ9.sailOutput = out0 := by rw [hobs9.out, sailOutput_sigmaPost_store]; exact hout8
  have hcode9 : Eval_exprLoaded σ9.mem := by
    rw [hmem9e]
    exact loaded_eval_expr_agreeP m1 m2
      (fun k hk => (getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem8e ▸ hcode8)
  -- 0x80003610: sd a5,80(sp) → m3
  obtain ⟨σ10, i10, hs10', hi10, hG10, hmem10, hobs10⟩ :=
    site_80003610_ee σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003610#64) vmi9 (sp - 1088#64) QV
      hG9 hpc9 hmi9 hsp_9 hx15_9 hcode9 rfl
      (by rw [haddr80]; omega) (by rw [haddr80]; omega) (by rw [haddr80, htoh]; omega) (by rw [haddr80]; omega) hi9
  have hstep10 : Step ⟨σ9, i9, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs10'
  have hmem10e : σ10.mem = m3 := by
    rw [hmem10, mem_afterNextPC, haddr80, hmem9e]
  have hpc10 : σ10.regs.get? Register.PC = some (0x80003614#64) := by
    have := obs_store_pc_val hobs10
    rwa [show BitVec.addInt (0x80003610#64) 4 = (0x80003614#64 : BitVec 64) from by decide] at this
  have hx10_10 := obs_store_other_val' hobs10 Register.x10 (by decide) hx10_9
  have hs1_10 := obs_store_other_val' hobs10 Register.x9 (by decide) hs1_9
  have hsp_10 := obs_store_other_val' hobs10 Register.x2 (by decide) hsp_9
  obtain ⟨vmi10, hmi10⟩ := obs_store_minstret_val hobs10
  have hout10 : σ10.sailOutput = out0 := by rw [hobs10.out, sailOutput_sigmaPost_store]; exact hout9
  have hcode_m3 : Eval_exprLoaded m3 :=
    loaded_eval_expr_agreeP m2 m3
      (fun k hk => (getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV)
        (by rcases hcodeStk with h | h <;> omega)).symm) (hmem9e ▸ hcode9)
  have hcode10 : Eval_exprLoaded σ10.mem := by rw [hmem10e]; exact hcode_m3
  -- the a0 = buf address = sp-1024
  have hx10_10' : σ10.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) := hx10_10
  ------------------------------------------------------------------------
  -- the copied 24-byte buffer represents `vsub`: ValueRepr m3 (sp-1024) vsub.
  ------------------------------------------------------------------------
  -- m3 byte-copies subsret[0..24) into buf[0..24), disjoint elsewhere.
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
  -- byte facts for the window in m3 (via getElem_writeMap8_k + sdData_sext_bytes)
  -- store 1 (K13) window: [sp-1024, sp-1016); reads-through the two later stores.
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
  -- the 24 window bytes in m3 match subsret's 24 bytes in c.σ.mem.
  have hm3_copy : ∀ j, j < 24 → m3[(sp.toNat - 1024) + j]? = c.σ.mem[(sp.toNat - 944) + j]? := by
    intro j hj
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨
        j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨
        j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 from by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    -- window K13 (bytes 0..7): m3[sp-1024+j] = kbj = c.σ.mem[sp-944+j]
    · rw [hK 0 (by omega), show sp.toNat-1024+0 = sp.toNat-1024 from by omega,
        getElem_writeMap8_0, eK0, show sp.toNat-944+0 = sp.toNat-944 from by omega]; exact hkb0.symm
    · rw [hK 1 (by omega), getElem_writeMap8_1, eK1]; exact hkb1.symm
    · rw [hK 2 (by omega), getElem_writeMap8_2, eK2]; exact hkb2.symm
    · rw [hK 3 (by omega), getElem_writeMap8_3, eK3]; exact hkb3.symm
    · rw [hK 4 (by omega), getElem_writeMap8_4, eK4]; exact hkb4.symm
    · rw [hK 5 (by omega), getElem_writeMap8_5, eK5]; exact hkb5.symm
    · rw [hK 6 (by omega), getElem_writeMap8_6, eK6]; exact hkb6.symm
    · rw [hK 7 (by omega), getElem_writeMap8_7, eK7]; exact hkb7.symm
    -- window PV (bytes 8..15): m3[sp-1016+o] = pbo = c.σ.mem[sp-936+o]
    · rw [show sp.toNat-1024+8 = sp.toNat-1016+0 from by omega, hP 0 (by omega),
        show sp.toNat-1016+0 = sp.toNat-1016 from by omega, getElem_writeMap8_0, eP0,
        show sp.toNat-944+8 = sp.toNat-936 from by omega]; exact hpb0.symm
    · rw [show sp.toNat-1024+9 = sp.toNat-1016+1 from by omega, hP 1 (by omega), getElem_writeMap8_1, eP1,
        show sp.toNat-944+9 = sp.toNat-936+1 from by omega]; exact hpb1.symm
    · rw [show sp.toNat-1024+10 = sp.toNat-1016+2 from by omega, hP 2 (by omega), getElem_writeMap8_2, eP2,
        show sp.toNat-944+10 = sp.toNat-936+2 from by omega]; exact hpb2.symm
    · rw [show sp.toNat-1024+11 = sp.toNat-1016+3 from by omega, hP 3 (by omega), getElem_writeMap8_3, eP3,
        show sp.toNat-944+11 = sp.toNat-936+3 from by omega]; exact hpb3.symm
    · rw [show sp.toNat-1024+12 = sp.toNat-1016+4 from by omega, hP 4 (by omega), getElem_writeMap8_4, eP4,
        show sp.toNat-944+12 = sp.toNat-936+4 from by omega]; exact hpb4.symm
    · rw [show sp.toNat-1024+13 = sp.toNat-1016+5 from by omega, hP 5 (by omega), getElem_writeMap8_5, eP5,
        show sp.toNat-944+13 = sp.toNat-936+5 from by omega]; exact hpb5.symm
    · rw [show sp.toNat-1024+14 = sp.toNat-1016+6 from by omega, hP 6 (by omega), getElem_writeMap8_6, eP6,
        show sp.toNat-944+14 = sp.toNat-936+6 from by omega]; exact hpb6.symm
    · rw [show sp.toNat-1024+15 = sp.toNat-1016+7 from by omega, hP 7 (by omega), getElem_writeMap8_7, eP7,
        show sp.toNat-944+15 = sp.toNat-936+7 from by omega]; exact hpb7.symm
    -- window QV (bytes 16..23): m3[sp-1008+o] = qbo = c.σ.mem[sp-928+o]
    · rw [show sp.toNat-1024+16 = sp.toNat-1008 from by omega, getElem_writeMap8_0, eQ0,
        show sp.toNat-944+16 = sp.toNat-928 from by omega]; exact hqb0.symm
    · rw [show sp.toNat-1024+17 = sp.toNat-1008+1 from by omega, getElem_writeMap8_1, eQ1,
        show sp.toNat-944+17 = sp.toNat-928+1 from by omega]; exact hqb1.symm
    · rw [show sp.toNat-1024+18 = sp.toNat-1008+2 from by omega, getElem_writeMap8_2, eQ2,
        show sp.toNat-944+18 = sp.toNat-928+2 from by omega]; exact hqb2.symm
    · rw [show sp.toNat-1024+19 = sp.toNat-1008+3 from by omega, getElem_writeMap8_3, eQ3,
        show sp.toNat-944+19 = sp.toNat-928+3 from by omega]; exact hqb3.symm
    · rw [show sp.toNat-1024+20 = sp.toNat-1008+4 from by omega, getElem_writeMap8_4, eQ4,
        show sp.toNat-944+20 = sp.toNat-928+4 from by omega]; exact hqb4.symm
    · rw [show sp.toNat-1024+21 = sp.toNat-1008+5 from by omega, getElem_writeMap8_5, eQ5,
        show sp.toNat-944+21 = sp.toNat-928+5 from by omega]; exact hqb5.symm
    · rw [show sp.toNat-1024+22 = sp.toNat-1008+6 from by omega, getElem_writeMap8_6, eQ6,
        show sp.toNat-944+22 = sp.toNat-928+6 from by omega]; exact hqb6.symm
    · rw [show sp.toNat-1024+23 = sp.toNat-1008+7 from by omega, getElem_writeMap8_7, eQ7,
        show sp.toNat-944+23 = sp.toNat-928+7 from by omega]; exact hqb7.symm
  have hbufRepr : ValueRepr m3 N φcv (sp.toNat - 1024) vsub :=
    valueRepr_copy_of_writeWindow (srcAddr := sp.toNat - 944) (dstAddr := sp.toNat - 1024)
      hm3_copy hm3_out
      (fun p s hp k hk => hNE.pay_disj p s hvalSub' hp k hk) hvalSub'
  ------------------------------------------------------------------------
  -- 0x80003614: jal value_truthy → PC := value_truthy entry, ra := 0x80003618
  ------------------------------------------------------------------------
  obtain ⟨σ11, i11, hs11', hi11, hG11, hmem11, hobs11⟩ :=
    site_80003614_ee σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80003614#64) vmi10
      hG10 hpc10 hmi10 hcode10 rfl hi10
  have hstep11 : Step ⟨σ10, i10, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ := hs11'
  have hmem11e : σ11.mem = m3 := by rw [hmem11]; exact hmem10e
  have hpc11 : σ11.regs.get? Register.PC = some (0x8000282c#64) := by
    have := obs_jal_pc hobs11
    rwa [show ((0x80003614#64 : BitVec 64) + sign_extend (m := 64) (0x1ff218#21)) = 0x8000282c#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink11 : σ11.regs.get? Register.x1 = some (0x80003618#64) := by
    have := obs_jal_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003614#64 : BitVec 64) 4 = (0x80003618#64:BitVec 64) from by decide] at this
  have hx10_11 : σ11.regs.get? Register.x10 = some ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) :=
    obs_jal_other' hobs11 Register.x10 (by decide) hx10_10'
  have hs1_11 : σ11.regs.get? Register.x9 = some sret := obs_jal_other' hobs11 Register.x9 (by decide) hs1_10
  have hsp_11 : σ11.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other' hobs11 Register.x2 (by decide) hsp_10
  obtain ⟨vmi11, hmi11⟩ := obs_jal_minstret hobs11
  have hout11 : σ11.sailOutput = out0 := by rw [hobs11.out, sailOutput_sigmaPost_jal]; exact hout10
  -- Value_truthyLoaded c.σ.mem (from mcall, agreement on value_truthy's code region,
  -- which is disjoint from the scribbled sub-stack window ∪ arena ∪ subsret buffer).
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
  -- both survive the 3 buffer stores (disjoint from both code regions)
  have hVtruthy_m3 : Value_truthyLoaded m3 :=
    loaded_truthy_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV) (by rcases hTruthyStk with h | h <;> omega)
      (loaded_truthy_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV) (by rcases hTruthyStk with h | h <;> omega)
        (loaded_truthy_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13) (by rcases hTruthyStk with h | h <;> omega) hVtruthy_c))
  have hVbool_m3 : Value_boolLoaded m3 :=
    loaded_bool_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV) (by rcases hBoolStk with h | h <;> omega)
      (loaded_bool_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV) (by rcases hBoolStk with h | h <;> omega)
        (loaded_bool_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13) (by rcases hBoolStk with h | h <;> omega) hVbool_c))
  -- the buffer region facts (TruthyRegion for the sp-1024 arg buffer)
  have hbuftag : ((sp - 1088#64) + sign_extend (m := 64) (0x040#12)) = (sp - 1024#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq
    rw [haddr64, BitVec.toNat_sub]
    have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    rw [h1024]; have := sp.isLt; omega
  have hbufNat : (sp - 1024#64 : BitVec 64).toNat = sp.toNat - 1024 := by
    rw [BitVec.toNat_sub]; have h1024 : (1024#64 : BitVec 64).toNat = 1024 := by decide
    rw [h1024]; have := sp.isLt; omega
  have hTruthyReg : TruthyRegion (sp - 1024#64) :=
    ⟨by rw [hbufNat]; omega, by rw [hbufNat]; have := hNE.buf_lo; omega,
     by rw [hbufNat]; omega, by rw [hbufNat, htoh]; have := hNE.buf_win; rw [htoh] at this; omega⟩
  -- the return-target alignment `(0x80003618 masked lsb).toNat % 4 = 0`
  have hrettgt_t : (BitVec.update ((0x80003618#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  -- ValueRepr at the buffer (buf address `sp-1024`) — rebase hbufRepr onto (sp-1024#64).toNat
  have hbufRepr' : ValueRepr m3 N φcv (sp - 1024#64).toNat vsub := by rw [hbufNat]; exact hbufRepr
  -- x10 at σ11 = sp-1024#64
  have hx10_11' : σ11.regs.get? Register.x10 = some (sp - 1024#64) := by rw [hx10_11, hbuftag]
  ------------------------------------------------------------------------
  -- the value_truthy callee (via value_truthy_spec), buf = sp-1024, ra = 0x80003618
  ------------------------------------------------------------------------
  obtain ⟨cT, hsT, hGT, hpcT, ha0T, hraT, ⟨vmiT, hmiT⟩, htickT, hmemT, houtT, hframeT⟩ :=
    value_truthy_spec (fun R => σ11.regs.get? R) (sp - 1024#64) (0x80003618#64) N φcv vsub m3 out0
      ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩
      ⟨hG11, hmem11e ▸ hVtruthy_m3, hmem11e, hpc11, hx10_11', hlink11, ⟨vmi11, hmi11⟩, hi11,
        hbufRepr', hTruthyReg, hrettgt_t, hout11, fun R _ => rfl⟩
  -- value_truthy leaves memory = m3, returns a0 = cond v.truthy 1 0, PC = 0x80003618
  have hmemT' : cT.σ.mem = m3 := hmemT
  have hpcT' : cT.σ.regs.get? Register.PC = some (0x80003618#64) := by
    rw [hpcT, show (BitVec.update ((0x80003618#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x80003618#64 from by apply BitVec.eq_of_toNat_eq; decide]
  -- callee-preserved s1(x9)/sp(x2)/x1(ra) via NotWrittenT (= σ11 reads)
  have hs1_T : cT.σ.regs.get? Register.x9 = some sret := by
    rw [hframeT Register.x9 (by decide)]; exact hs1_11
  have hsp_T : cT.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeT Register.x2 (by decide)]; exact hsp_11
  have hVbool_T : Value_boolLoaded cT.σ.mem := by rw [hmemT']; exact hVbool_m3
  have hcode_T : Eval_exprLoaded cT.σ.mem := by rw [hmemT']; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x80003618: seqz a1,a0 → x11 := (a0 == 0) = !v.truthy (as a bit)
  ------------------------------------------------------------------------
  obtain ⟨σ13, i13, hs13', hi13, hG13, hmem13, hobs13⟩ :=
    site_80003618_ee cT.σ cT.tick cT.steps (0x80003618#64) vmiT (cond (Value.truthy vsub) (1#64) (0#64))
      hGT hpcT' hmiT ha0T (hmemT' ▸ hcode_m3) rfl htickT
  have hstep13 : Step cT ⟨σ13, i13, cT.steps + 1⟩ := by cases cT; exact hs13'
  have hmem13e : σ13.mem = m3 := by rw [hmem13]; exact hmemT'
  have hpc13 : σ13.regs.get? Register.PC = some (0x8000361c#64) := by
    have := obs_alu_pc hobs13
    rwa [show BitVec.addInt (0x80003618#64) 4 = (0x8000361c#64 : BitVec 64) from by decide] at this
  have hx11_13 : σ13.regs.get? Register.x11
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (cond (Value.truthy vsub) (1#64) (0#64)) (sign_extend (m := 64) (0x001#12))))) :=
    obs_alu_rd hobs13 (by decide) (by decide) (by decide) (by decide) (by decide)
  have hs1_13 : σ13.regs.get? Register.x9 = some sret := obs_alu_other' hobs13 Register.x9 (by decide) hs1_T
  have hsp_13 : σ13.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs13 Register.x2 (by decide) hsp_T
  obtain ⟨vmi13, hmi13⟩ := obs_alu_minstret hobs13
  have hout13 : σ13.sailOutput = out0 := by rw [hobs13.out, sailOutput_sigmaPost_alu]; exact houtT
  have hVbool_13 : Value_boolLoaded σ13.mem := by rw [hmem13e]; exact hVbool_m3
  have hcode_13 : Eval_exprLoaded σ13.mem := by rw [hmem13e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x8000361c: mv a0,s1 → x10 := sret
  ------------------------------------------------------------------------
  obtain ⟨σ14, i14, hs14', hi14, hG14, hmem14, hobs14⟩ :=
    site_8000361c_ee σ13 i13 (cT.steps + 1) (0x8000361c#64) vmi13 sret hG13 hpc13 hmi13 hs1_13 hcode_13 rfl hi13
  have hstep14 : Step ⟨σ13, i13, cT.steps + 1⟩ ⟨σ14, i14, cT.steps + 1 + 1⟩ := hs14'
  have hmem14e : σ14.mem = m3 := by rw [hmem14]; exact hmem13e
  have hpc14 : σ14.regs.get? Register.PC = some (0x80003620#64) := by
    have := obs_alu_pc hobs14
    rwa [show BitVec.addInt (0x8000361c#64) 4 = (0x80003620#64 : BitVec 64) from by decide] at this
  have hx10_14 : σ14.regs.get? Register.x10 = some sret := by
    have := obs_alu_rd hobs14 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (sret + sign_extend (m := 64) (0x000#12) : BitVec 64) = sret from by
      rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide]
      rw [BitVec.add_zero]] at this
  have hx11_14 : σ14.regs.get? Register.x11
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (cond (Value.truthy vsub) (1#64) (0#64)) (sign_extend (m := 64) (0x001#12))))) :=
    obs_alu_other' hobs14 Register.x11 (by decide) hx11_13
  have hs1_14 : σ14.regs.get? Register.x9 = some sret := obs_alu_other' hobs14 Register.x9 (by decide) hs1_13
  have hsp_14 : σ14.regs.get? Register.x2 = some (sp - 1088#64) := obs_alu_other' hobs14 Register.x2 (by decide) hsp_13
  obtain ⟨vmi14, hmi14⟩ := obs_alu_minstret hobs14
  have hout14 : σ14.sailOutput = out0 := by rw [hobs14.out, sailOutput_sigmaPost_alu]; exact hout13
  have hVbool_14 : Value_boolLoaded σ14.mem := by rw [hmem14e]; exact hVbool_m3
  have hcode_14 : Eval_exprLoaded σ14.mem := by rw [hmem14e]; exact hcode_m3
  ------------------------------------------------------------------------
  -- 0x80003620: jal value_bool → PC := value_bool entry, ra := 0x80003624
  ------------------------------------------------------------------------
  obtain ⟨σ15, i15, hs15', hi15, hG15, hmem15, hobs15⟩ :=
    site_80003620_ee σ14 i14 (cT.steps + 1 + 1) (0x80003620#64) vmi14 hG14 hpc14 hmi14 hcode_14 rfl hi14
  have hstep15 : Step ⟨σ14, i14, cT.steps + 1 + 1⟩ ⟨σ15, i15, cT.steps + 1 + 1 + 1⟩ := hs15'
  have hmem15e : σ15.mem = m3 := by rw [hmem15]; exact hmem14e
  have hpc15 : σ15.regs.get? Register.PC = some (0x800027f8#64) := by
    have := obs_jal_pc hobs15
    rwa [show ((0x80003620#64 : BitVec 64) + sign_extend (m := 64) (0x1ff1d8#21)) = 0x800027f8#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hlink15 : σ15.regs.get? Register.x1 = some (0x80003624#64) := by
    have := obs_jal_rd hobs15 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show BitVec.addInt (0x80003620#64 : BitVec 64) 4 = (0x80003624#64:BitVec 64) from by decide] at this
  have hx10_15 : σ15.regs.get? Register.x10 = some sret := obs_jal_other' hobs15 Register.x10 (by decide) hx10_14
  have hx11_15 : σ15.regs.get? Register.x11
      = some (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (cond (Value.truthy vsub) (1#64) (0#64)) (sign_extend (m := 64) (0x001#12))))) :=
    obs_jal_other' hobs15 Register.x11 (by decide) hx11_14
  have hs1_15 : σ15.regs.get? Register.x9 = some sret := obs_jal_other' hobs15 Register.x9 (by decide) hs1_14
  have hsp_15 : σ15.regs.get? Register.x2 = some (sp - 1088#64) := obs_jal_other' hobs15 Register.x2 (by decide) hsp_14
  obtain ⟨vmi15, hmi15⟩ := obs_jal_minstret hobs15
  have hout15 : σ15.sailOutput = out0 := by rw [hobs15.out, sailOutput_sigmaPost_jal]; exact hout14
  have hVbool_15 : Value_boolLoaded σ15.mem := by rw [hmem15e]; exact hVbool_m3
  -- the BoolRegion for the outer sret buffer
  have hBoolReg : BoolRegion sret := ⟨hsretAl, hsretLo, hsretHi, hsretWin, hSretBoolCode⟩
  have hrettgt_b : (BitVec.update ((0x80003624#64 : BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by decide
  ------------------------------------------------------------------------
  -- the value_bool callee (via value_bool_spec_full), buf = sret, vb = seqz result
  ------------------------------------------------------------------------
  let vbV : BitVec 64 := zero_extend (m := 64) (bool_to_bit (zopz0zI_u (cond (Value.truthy vsub) (1#64) (0#64)) (sign_extend (m := 64) (0x001#12))))
  obtain ⟨cB, hsB, hGB, hpcB, ha0B, hraB, ⟨vmiB, hmiB⟩, htickB, hvalB, houtB, hmemframeB, hMemExtB, hframeB⟩ :=
    value_bool_spec_full (fun R => σ15.regs.get? R) sret vbV (0x80003624#64) N φc' m3 out0
      ⟨σ15, i15, cT.steps + 1 + 1 + 1⟩
      ⟨hG15, hVbool_15, hmem15e, hpc15, hx10_15, hx11_15, hlink15, ⟨vmi15, hmi15⟩, hi15,
        hBoolReg, hrettgt_b, hout15, fun R _ => rfl⟩
  -- the produced value is `.bool (!vsub.truthy)`
  have hvbridge : (vbV != 0#64) = (!Value.truthy vsub) := seqz_truthy_bridge vsub
  have hvalfinal : ValueRepr cB.σ.mem N φc' sret.toNat (.bool (!vsub.truthy)) := by
    rw [show ((.bool (!vsub.truthy)) : Value) = .bool (vbV != 0#64) from by rw [hvbridge]]; exact hvalB
  have hpcB' : cB.σ.regs.get? Register.PC = some (0x80003624#64) := by
    rw [hpcB, show (BitVec.update ((0x80003624#64:BitVec 64) + sign_extend (m := 64) (0x000#12)) 0 0#1)
      = 0x80003624#64 from by apply BitVec.eq_of_toNat_eq; decide]
  have hs1_B : cB.σ.regs.get? Register.x9 = some sret := by
    rw [hframeB Register.x9 (by decide)]; exact hs1_15
  have hsp_B : cB.σ.regs.get? Register.x2 = some (sp - 1088#64) := by
    rw [hframeB Register.x2 (by decide)]; exact hsp_15
  have hcode_B : Eval_exprLoaded cB.σ.mem :=
    loaded_eval_expr_agreeP m3 cB.σ.mem
      (fun k hk => hmemframeB k (by rcases hsretEvalCode with h | h <;> omega)) hcode_m3
  ------------------------------------------------------------------------
  -- 0x80003624: j 0x800033ec → shared epilogue entry
  ------------------------------------------------------------------------
  obtain ⟨σ17, i17, hs17', hi17, hG17, hmem17, hobs17⟩ :=
    site_80003624_ee cB.σ cB.tick cB.steps (0x80003624#64) vmiB hGB hpcB' hmiB hcode_B rfl
      (by rw [show ((0x80003624#64:BitVec 64) + sign_extend (m := 64) (0x1ffdc8#21)) = 0x800033ec#64 from by
            apply BitVec.eq_of_toNat_eq; decide]; decide) htickB
  have hstep17 : Step cB ⟨σ17, i17, cB.steps + 1⟩ := by cases cB; exact hs17'
  have hmem17e : σ17.mem = cB.σ.mem := hmem17
  have hpc_fin : σ17.regs.get? Register.PC = some (0x800033ec#64) := by
    have := obs_jr_pc hobs17
    rwa [show ((0x80003624#64:BitVec 64) + sign_extend (m := 64) (0x1ffdc8#21)) = 0x800033ec#64 from by
      apply BitVec.eq_of_toNat_eq; decide] at this
  have hs1_fin : σ17.regs.get? Register.x9 = some sret := obs_jr_other' hobs17 Register.x9 (by decide) hs1_B
  have hsp_fin : σ17.regs.get? Register.x2 = some (sp - 1088#64) := obs_jr_other' hobs17 Register.x2 (by decide) hsp_B
  obtain ⟨vmifin, hmifin⟩ := obs_jr_minstret hobs17
  have hout_fin : σ17.sailOutput = out0 := by
    rw [hobs17.out, sailOutput_sigmaPost_jump_x0]; exact houtB
  ------------------------------------------------------------------------
  -- spill slots survive: [sp-32,sp) disjoint from the 3 buffer stores (below
  -- sp-1008) and from value_bool's sret write.
  ------------------------------------------------------------------------
  have hslotAgree : AgreeP (fun k => sp.toNat - 32 ≤ k ∧ k < sp.toNat) c.σ.mem σ17.mem := by
    intro k hk
    rw [hmem17e, ← hmemframeB k (by rcases hsretStk with h | h <;> omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13) (by omega)]
  have hslotRa_f : read64 σ17.mem (sp.toNat - 8) = some r.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotRa
  have hslotS0_f : read64 σ17.mem (sp.toNat - 16) = some v8.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS0
  have hslotS1_f : read64 σ17.mem (sp.toNat - 24) = some v9.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS1
  have hslotS2_f : read64 σ17.mem (sp.toNat - 32) = some v18.toNat := by
    rw [← read64_agreeP hslotAgree (fun j hj => ⟨by omega, by omega⟩)]; exact hslotS2
  -- StoreRepr survives: all writes (3 buffer stores + sret) land in [SL.lo, SL.hi).
  have hSL17 : ∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → c.σ.mem[k]? = σ17.mem[k]? := by
    intro k hk
    rw [hmem17e, ← hmemframeB k (by rcases hsretInSL with ⟨hl, hr⟩; omega)]
    show c.σ.mem[k]? = (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[k]?
    rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) k (sdData_val QV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[k]?
    rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) k (sdData_val PV) (by omega)]
    show c.σ.mem[k]? = (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[k]?
    rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) k (sdData_val K13) (by omega)]
  have hstore_fin : StoreRepr σ17.mem N A φf' φc' st'.store :=
    hstoreSurv' σ17.mem (fun k hk => hSL17 k hk)
  have hSurvSL_fin : ∀ m' : Mem,
      (∀ k : Nat, ¬ (SL.lo ≤ k ∧ k < SL.hi) → σ17.mem[k]? = m'[k]?) →
      StoreRepr m' N A φf' φc' st'.store :=
    fun m' hm' => hstoreSurv' m' (fun k hk => (hSL17 k hk).trans (hm' k hk))
  -- the MemExtends m0 σ17.mem (mcall fully populated ⇒ all writes only ADD)
  have hMemExt_m0_c : MemExtends m0 c.σ.mem := by
    intro a b _; obtain ⟨bm, hbm⟩ := hStackPop a; exact hMemExt a bm hbm
  have hMemExt_c_15 : MemExtends c.σ.mem σ15.mem := by
    rw [hmem15e]
    exact ((MemExtends.refl c.σ.mem).trans
      (memExtends_writeMap8 c.σ.mem (sp.toNat - 1024) (sdData_val K13))).trans
      ((memExtends_writeMap8 m1 (sp.toNat - 1016) (sdData_val PV)).trans
        (memExtends_writeMap8 m2 (sp.toNat - 1008) (sdData_val QV)))
  have hMemExt_15_17 : MemExtends σ15.mem σ17.mem := by
    rw [hmem17e, hmem15e]; exact hMemExtB
  have hMemExt_fin : MemExtends m0 σ17.mem :=
    (hMemExt_m0_c.trans hMemExt_c_15).trans hMemExt_15_17
  -- the callee-saved (noise) frame across the whole tail, then the prologue bridge.
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
    have hx11R : (Register.x11 == R) = false := abi_ne' (by decide)
    have hx13R : (Register.x13 == R) = false := abi_ne' (by decide)
    have hx14R : (Register.x14 == R) = false := abi_ne' (by decide)
    have hx15R : (Register.x15 == R) = false := abi_ne' (by decide)
    have hx10R : (Register.x10 == R) = false := abi_ne' (by decide)
    have hx1R : (Register.x1 == R) = false := abi_ne' (by decide)
    -- σ1..σ7: lw/li/ld/beq/ld/ld/addi (write x14/x15/x13/PC/x14/x15/x10)
    have f1 : σ1.regs.get? R = c.σ.regs.get? R :=
      (hobs1.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx14R hnpc' hmii')
    have f2 : σ2.regs.get? R = σ1.regs.get? R :=
      (hobs2.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx15R hnpc' hmii')
    have f3 : σ3.regs.get? R = σ2.regs.get? R :=
      (hobs3.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx13R hnpc' hmii')
    have f4 : σ4.regs.get? R = σ3.regs.get? R :=
      (hobs4.1 R hmc' hmt' hmip').trans (get?_sigmaPost_branch_nottaken _ _ _ R hmi' hpc' hnpc' hmii')
    have f5 : σ5.regs.get? R = σ4.regs.get? R :=
      (hobs5.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx14R hnpc' hmii')
    have f6 : σ6.regs.get? R = σ5.regs.get? R :=
      (hobs6.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx15R hnpc' hmii')
    have f7 : σ7.regs.get? R = σ6.regs.get? R :=
      (hobs7.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx10R hnpc' hmii')
    -- σ8..σ10: sd/sd/sd (write memory, not R)
    have f8 : σ8.regs.get? R = σ7.regs.get? R := frame_store_v hobs8 R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have f9 : σ9.regs.get? R = σ8.regs.get? R := frame_store_v hobs9 R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    have f10 : σ10.regs.get? R = σ9.regs.get? R := frame_store_v hobs10 R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ11: jal value_truthy (writes x1)
    have f11 : σ11.regs.get? R = σ10.regs.get? R :=
      (hobs11.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1R hnpc' hmii')
    -- cT: value_truthy NotWrittenT frame
    have fT : cT.σ.regs.get? R = σ11.regs.get? R :=
      hframeT R ⟨hx10R, hx14R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ13: seqz (writes x11)
    have f13 : σ13.regs.get? R = cT.σ.regs.get? R :=
      (hobs13.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx11R hnpc' hmii')
    -- σ14: mv a0,s1 (writes x10)
    have f14 : σ14.regs.get? R = σ13.regs.get? R :=
      (hobs14.1 R hmc' hmt' hmip').trans (get?_sigmaPost_alu _ _ _ _ _ R hmi' hpc' hx10R hnpc' hmii')
    -- σ15: jal value_bool (writes x1)
    have f15 : σ15.regs.get? R = σ14.regs.get? R :=
      (hobs15.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jal _ _ _ _ _ _ R hmi' hpc' hx1R hnpc' hmii')
    -- cB: value_bool NotWrittenV frame
    have fB : cB.σ.regs.get? R = σ15.regs.get? R :=
      hframeB R ⟨hx11R, hx15R, hpc', hnpc', hmi', hmii', hmc', hmt', hmip'⟩
    -- σ17: j (writes PC)
    have f17 : σ17.regs.get? R = cB.σ.regs.get? R :=
      (hobs17.1 R hmc' hmt' hmip').trans (get?_sigmaPost_jump_x0 _ _ _ _ R hmi' hpc' hnpc' hmii')
    rw [f17, fB, f15, f14, f13, fT, f11, f10, f9, f8, f7, f6, f5, f4, f3, f2, f1]
    exact (hframe R hR').trans (hbridge R hR' he8 he9 he18 he2)
  ------------------------------------------------------------------------
  -- assemble the epilogue-entry package `PreEpilogueVD` at the extended maps
  ------------------------------------------------------------------------
  have hSteps : Steps c ⟨σ17, i17, cB.steps + 1⟩ :=
    (Steps.single hstep1).trans ((Steps.single hstep2).trans ((Steps.single hstep3).trans
      ((Steps.single hstep4).trans ((Steps.single hstep5).trans ((Steps.single hstep6).trans
        ((Steps.single hstep7).trans ((Steps.single hstep8).trans ((Steps.single hstep9).trans
          ((Steps.single hstep10).trans ((Steps.single hstep11).trans (hsT.trans
            ((Steps.single hstep13).trans ((Steps.single hstep14).trans ((Steps.single hstep15).trans
              (hsB.trans (Steps.single hstep17))))))))))))))))
  refine ⟨⟨σ17, i17, cB.steps + 1⟩, hSteps, σ17.mem, φf', φc', hpf', hpc',
    ⟨?_, hMemExt_fin, hSurvSL_fin⟩⟩
  refine ⟨hG17, hi17, hpc_fin, hs1_fin, hsp_fin, ⟨vmifin, hmifin⟩,
    hout_fin, houtStr, ?_,
    (by rw [hmem17e]; exact hcode_B), (by rw [hmem17e]; exact hvalfinal), hstore_fin, hframeG,
    hslotRa_f, hslotS0_f, hslotS1_f, hslotS2_f, hgv8, hgv9, hgv18, hgv2, ?_,
    (by omega), hsphiRam, (by omega), (by omega), hsp8, hraAl⟩
  · -- c.σ.mem = mpre (mpre = σ17.mem): the PreEpilogueV mem field
    rfl
  · -- memFrame: σ17.mem vs the entry m0
    intro a ha hA
    by_cases hsr : sret.toNat ≤ a ∧ a < sret.toNat + 24
    · exact Or.inl hsr
    · refine Or.inr ?_
      rw [hmem17e, ← hmemframeB a hsr]
      show (writeMap8 m2 (sp.toNat-1008) (sdData_val QV))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint m2 (sp.toNat-1008) a (sdData_val QV) (by omega)]
      show (writeMap8 m1 (sp.toNat-1016) (sdData_val PV))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint m1 (sp.toNat-1016) a (sdData_val PV) (by omega)]
      show (writeMap8 c.σ.mem (sp.toNat-1024) (sdData_val K13))[a]? = m0[a]?
      rw [getElem_writeMap8_disjoint c.σ.mem (sp.toNat-1024) a (sdData_val K13) (by omega)]
      rcases hmemFrame a (by omega) hA with hin | heq
      · exact absurd hin (by omega)
      · rw [heq]; exact hMcallM0 a ha hA

/-! ## `NotSimExtras` — the recursive-case facts beyond `EvalEntry` (mirrors `NegExtras`)

The `.not` analogue of `NegExtras` (`EvalNegSim3.lean`): the same operand-node
`ExprRepr`+geometry, the +1088 recursive headroom, the arena/code/table
disjunctions and the `EX_UNARY` slot pin — with `.not` for the AST subtree — PLUS
the two extra callee-code pins (`value_truthy`/`value_bool`) and their
disjunctions and the buffer/payload geometry that `blockC_not` needs. These are
the residual-#1 program-structure facts an `EvalEntry` widening / M6 Layout would
supply; a future `blockA_k` widening + full stack-layout derivation discharges
them (exactly as for `evalNegSim`). -/
structure NotSimExtras
    (N : NativeAddrs) (A : Arena) (SL : StackLayout)
    (esub : Expr) (vsub : Value)
    (sp sret aExpr aOperand : BitVec 64)
    (m0 : Mem) : Prop where
  -- ===== shared with NegExtras (EX_UNARY arm head geometry) =====
  slot8 : KindSlotPinned 8 (0x800035e0#64) m0
  expr_survives : ∀ m' : Mem,
    (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → m0[a]? = m'[a]?) →
    ExprRepr m' aExpr.toNat (.unary .not esub)
  pay : read64 m0 (aExpr.toNat + 16) = some aOperand.toNat
  operand_repr : ExprRepr m0 aOperand.toNat esub
  expr24 : aExpr.toNat + 24 ≤ 0x100000000
  expr24_stk : aExpr.toNat + 24 ≤ SL.lo ∨ sp.toNat ≤ aExpr.toNat
  op_align : aOperand.toNat % 8 = 0
  op_lo : 0x80000000 ≤ aOperand.toNat
  op_hi : aOperand.toNat + 16 ≤ 0x100000000
  op_win : tohostAddr + 16 ≤ aOperand.toNat
  op_stk : aOperand.toNat + 16 ≤ SL.lo ∨ sp.toNat - 1088 ≤ aOperand.toNat
  sp_headroom : SL.lo + 3264 ≤ sp.toNat
  sp_SLhi : sp.toNat ≤ SL.hi
  sp16 : sp.toNat % 16 = 0
  SLhi_ram : SL.hi ≤ 0x100000000
  code_stk : sp.toNat ≤ 0x80003164 ∨ 0x80003fe0 ≤ SL.lo
  vicode_stk : (0x8000281c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x8000280c
  table_stk : (0x80019f7c : Nat) ≤ SL.lo ∨ sp.toNat ≤ 0x80019f58
  arena_stk : A.hi ≤ SL.lo ∨ sp.toNat ≤ A.lo
  arena_code : A.hi ≤ 0x80003164 ∨ 0x80003fe0 ≤ A.lo
  -- ===== blockC_not extras (op-token geometry) =====
  expr_align4 : aExpr.toNat % 4 = 0
  expr_win8 : tohostAddr + 8 ≤ aExpr.toNat
  expr_A : aExpr.toNat + 16 ≤ A.lo ∨ A.hi ≤ aExpr.toNat
  expr_sub : aExpr.toNat + 16 ≤ sp.toNat - 944 ∨ sp.toNat - 944 + 24 ≤ aExpr.toNat
  sret_inSL : SL.lo ≤ sret.toNat ∧ sret.toNat + 24 ≤ SL.hi
  -- ===== NOT-tail: the two extra callee-code pins + their disjunctions =====
  truthy_loaded : Value_truthyLoaded m0
  bool_loaded : Value_boolLoaded m0
  truthy_stk : sp.toNat ≤ 0x8000282c ∨ 0x8000285c ≤ SL.lo
  boolcode_stk : sp.toNat ≤ 0x800027f8 ∨ 0x8000280c ≤ SL.lo
  sret_boolcode : sret.toNat + 24 ≤ 0x800027f8 ∨ 0x8000280c ≤ sret.toNat
  truthy_arena : A.hi ≤ 0x8000282c ∨ 0x8000285c ≤ A.lo
  bool_arena : A.hi ≤ 0x800027f8 ∨ 0x8000280c ≤ A.lo
  -- ===== NOT-tail: the operand-value string payload is disjoint from the buffer =====
  -- The operand value's payload pointer (read at the sub-result buffer `sp-944+8`,
  -- in ANY post-sub-call memory representing `vsub` there) points at a heap string
  -- disjoint from the truthy arg buffer `[sp-1024, sp-1000)` (stack vs heap; M6). -/
  pay_disj : ∀ (m : Mem) (φc' : Addr → Nat) (p : Nat) (s : String),
    ValueRepr m N φc' (sp.toNat - 944) vsub → read64 m (sp.toNat - 944 + 8) = some p →
    ∀ k, k ≤ s.length → (p + k < sp.toNat - 1024 ∨ sp.toNat - 1024 + 24 ≤ p + k)

/-! ## `EvalNotSimGoal` — the `EvalE.not` projection of the simulation

In the `EvalIH` motive shape (`EvalEntry → EvalExitD`), mirroring `EvalNegSimGoal`.
Conditional ONLY on `NotSimExtras` (the recursive-case program-structure facts) and
`hMcallPop` (M6 Layout: the pre-call memory is fully populated). -/
def EvalNotSimGoal : Prop :=
  ∀ (g : (R : Register) → Option (RegisterType R))
    (N : NativeAddrs) (A : Arena) (SL : StackLayout) (φf φc : Addr → Nat)
    (st st' : Vsa.While.St) (d : Nat) (env : Addr) (esub : Expr) (vsub : Value)
    (sp r sret aEnv aExpr aOperand : BitVec 64)
    (m0 : Mem),
    EvalIH st d env esub st' vsub →
    EvalE st d env (.unary .not esub) st' (.bool (!vsub.truthy)) →
    Triple
      (fun c =>
        EvalEntry g N A SL φf φc st d env (.unary .not esub) sp r sret aEnv aExpr m0 c ∧
        NotSimExtras N A SL esub vsub sp sret aExpr aOperand m0 ∧
        (∀ mcall : Mem,
          (∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]?) →
          ∀ a : Nat, ∃ b, mcall[a]? = some b))
      (EvalExitD g N A SL φf φc st.store.frames.size st.store.closures.size
        st' (.bool (!vsub.truthy)) sp r sret m0)

/-- `read32 m aExpr = some 8` from `ExprRepr m aExpr (.unary .not esub)`. -/
theorem exprRepr_not_kind {m : Mem} {a : Nat} {esub : Expr}
    (h : ExprRepr m a (.unary .not esub)) : read32 m a = some 8 := by
  cases h with | unary hk _ _ _ => exact hk

/-- **`evalNotSim`**: the `EvalE.not` (EX_UNARY, logical-not) recursive case of the
simulation, in the `EvalIH` motive shape. Composes `blockA_k` (prologue+dispatch →
widened `ArmEntryK`), `blockB_unary` (arm head + recursive call ⋈ IH →
`SubEvalReturn`), `blockC_not` (post-call not tail → `PreEpilogueVD .bool(!truthy)`),
and `blockD_v_rec` (shared epilogue → `EvalExitD`). Mirrors `evalNegSim` verbatim
except for the block-C call (the `not` tail) and the produced value. -/
theorem evalNotSim : EvalNotSimGoal := by
  intro g N A SL φf φc st st' d env esub vsub sp r sret aEnv aExpr aOperand
    m0 hIH _hEvalE
  intro c ⟨hc, hx, hMcallPop⟩
  have htoh : tohostAddr = 0x8001ad00 := rfl
  -- === block A: prologue + dispatch → widened ArmEntryK @0x800035e0 ===
  have hkm0 : read32 m0 aExpr.toNat = some 8 := exprRepr_not_kind (hc.mem ▸ hc.expr)
  obtain ⟨c1, hs1, ment, v8, v9, v18, hArm⟩ :=
    blockA_k g N A SL φf φc st (.unary .not esub) 8 (0x800035e0#64) UnaryArmCallee
      sp r sret aEnv aExpr m0 c.σ.sailOutput
      (by omega) (by omega)
      hkm0
      hx.slot8
      ⟨hc.mem ▸ hc.value_int_code, hc.mem ▸ hc.int_slot⟩
      (fun mem a8 dd hlo hhi hcl => by
        obtain ⟨hvi, hsl⟩ := hcl
        have hvicodeD := hc.vicode_stack_disjoint
        have htableD := hc.table_stack_disjoint
        refine ⟨loaded_int_writeMap8 mem a8 dd (by omega) hvi, ?_⟩
        exact intSlot_writeMap8 mem a8 dd (by simp only [jumpTableBase]; omega) hsl)
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
  obtain ⟨_hAG, _hAtick, _hApc, _hAa0, _hAs1, _hAa2, _hAsp, _hAra, _hAmi, _hAout,
    _hAmem, _hAcode, _hAvi, _hAexpr, _hAstr, _hAxAl, _hAxLo, _hAxHi, _hAxWin,
    _hAslotRa, _hAslotS0, _hAslotS1, _hAslotS2, hArmMemM0,
    hArmg8, hArmg9, hArmg18, hArmg2, _hAstore, _hAstoreSurv, hArmFrame,
    _hAsretAl, _hAsretLo, _hAsretHi, _hAsretWin, _hAsretVi, _hAsretStk, _hAsretEc,
    _hAsp1088, _hAsphi, _hAsplo, _hAspwin, _hAsp8, _hASLlo, _hASLwin, _hASLloSp, _hAraAl,
    hAEx11, hAEx8, hAEx18⟩ := hArmCopy
  have hx11c1 : c1.σ.regs.get? Register.x11 = some aEnv := hAEx11
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
  have hExprMent : ExprRepr ment aExpr.toNat (.unary .not esub) :=
    hx.expr_survives ment (fun a ha => (hMentM0 a ha).symm)
  obtain ⟨p, hk8m, hopTok, hpayMent, hsubReprMent⟩ : ∃ p,
      read32 ment aExpr.toNat = some 8 ∧
      read32 ment (aExpr.toNat + 8) = some (unOpTok .not) ∧
      read64 ment (aExpr.toNat + 16) = some p ∧ ExprRepr ment p esub := by
    cases hExprMent with | unary hk htok hp hpe => exact ⟨_, hk, htok, hp, hpe⟩
  have hpayMent' : read64 ment (aExpr.toNat + 16) = some aOperand.toNat := by
    obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, e0, e1, e2, e3, e4, e5, e6, e7, hrec⟩ :=
      read64_bytes m0 (aExpr.toNat + 16) aOperand.toNat hx.pay
    have hstk := hx.expr24_stk
    simp only [read64, readLE, bind, Option.bind]
    rw [hMentM0 (aExpr.toNat + 16) (by omega), hMentM0 (aExpr.toNat + 16 + 1) (by omega),
        hMentM0 (aExpr.toNat + 16 + 2) (by omega), hMentM0 (aExpr.toNat + 16 + 3) (by omega),
        hMentM0 (aExpr.toNat + 16 + 4) (by omega), hMentM0 (aExpr.toNat + 16 + 5) (by omega),
        hMentM0 (aExpr.toNat + 16 + 6) (by omega), hMentM0 (aExpr.toNat + 16 + 7) (by omega),
        e0, e1, e2, e3, e4, e5, e6, e7]
    simp only []; apply congrArg some; omega
  have hpeq : p = aOperand.toNat := by
    have := hpayMent.symm.trans hpayMent'; exact Option.some.inj this
  subst hpeq
  have hOperandReprMent : ExprRepr ment aOperand.toNat esub := hsubReprMent
  -- === block B: arm head + recursive call ⋈ IH → SubEvalReturn @0x800035ec ===
  obtain ⟨c2, hs2, hSub⟩ :=
    blockB_unary g (fun R => c1.σ.regs.get? R) N A SL φf φc st st' d env .not esub vsub
      sp r sret aExpr aEnv aOperand v8 v9 v18 c.σ.sailOutput m0 hIH
      c1 ⟨ment, hArm, hx11c1, hgpreframe, ⟨aExpr, hgpre_x8⟩, hgpre18,
        hpayMent', hOperandReprMent, hx.expr24,
        hx.op_align, hx.op_lo, hx.op_hi, hx.op_win, hx.op_stk,
        hx.sp_headroom, hx.sp_SLhi, hx.sp16, hx.SLhi_ram,
        hx.code_stk, hx.vicode_stk, (by have := hx.table_stk; omega), hx.arena_stk, hx.arena_code,
        -- ITEM ZERO B1: the operand's child budget, DERIVED from the entry's
        -- budgeted fields (`StackOK.child` + the `.unary` pass-through).
        hc.stackBudget.child (by decide)
          (by
            have h1 : (Expr.unary UnOp.not esub).stackNeed
                = evalFrame + esub.stackNeed := rfl
            have h2 : ((1088#64 : BitVec 64)).toNat = 1088 := by decide
            simp only [h1, h2, evalFrame]; omega),
        Expr.bodiesBound_unary hc.expr_bodies,
        hc.store_bodies⟩
  obtain ⟨mcall, hSubR, hMcallM0stk⟩ := hSub
  have hAgM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → mcall[a]? = m0[a]? := hMcallM0stk
  have hOutC2 : OutRepr c2.σ st' := hSubR.2.2.2.2.2.2.2.2.1
  have houtStr : String.join c2.σ.sailOutput.toList = st'.out := hOutC2
  -- transport the two callee-code pins from `m0` to `mcall`
  have hVtruthyMcall : Value_truthyLoaded mcall :=
    loaded_truthy_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.truthy_stk; omega)).symm) hx.truthy_loaded
  have hVboolMcall : Value_boolLoaded mcall :=
    loaded_bool_agreeP m0 mcall
      (fun a ha => (hAgM0 a (by have := hx.boolcode_stk; omega)).symm) hx.bool_loaded
  have hMcallM0 : ∀ a : Nat, ¬ (SL.lo ≤ a ∧ a < sp.toNat) → ¬ (A.lo ≤ a ∧ a < A.hi) →
      mcall[a]? = m0[a]? := fun a ha _ => hAgM0 a ha
  have hStackPop : ∀ a : Nat, ∃ b, mcall[a]? = some b := hMcallPop mcall hAgM0
  have hExprMcall : ExprRepr mcall aExpr.toNat (.unary .not esub) :=
    hx.expr_survives mcall (fun a ha => (hAgM0 a ha).symm)
  -- the NotExtras (buffer geometry) at any φc' — payload disjointness transported to c2.σ.mem
  have hNotExtras : ∀ φc' : Addr → Nat, ValueRepr c2.σ.mem N φc' (sp.toNat - 944) vsub →
      NotExtras N A SL φc' vsub sp sret c2.σ.mem := by
    intro φc' hvr
    exact ⟨(by have := hx.op_lo; have := hx.sp_headroom; omega),
      (by have := hx.sp_headroom; omega),
      (fun p s hvr' hp k hk => hx.pay_disj c2.σ.mem φc' p s hvr' hp k hk)⟩
  -- === block C: post-call not tail → PreEpilogueVD .bool(!truthy) @0x800033ec ===
  obtain ⟨c3, hs3, mpreC, φfe, φce, hpfe, hpce, hPreD⟩ :=
    blockC_not (fun R => c1.σ.regs.get? R) g N A SL φf φc st.store.frames.size
      st.store.closures.size st' vsub sp r sret aExpr v8 v9 v18 c2.σ.sailOutput esub m0
      c2 ⟨mcall, hSubR, hgpre_x8, hExprMcall, hStackPop,
        hx.expr_align4, hc.expr_ram.1, hc.expr_ram.2, hx.expr_win8,
        hc.expr_stack_disjoint, hx.expr_A, hx.expr_sub,
        houtStr, hc.sret_align, hc.sret_ram.1, hc.sret_ram.2, hc.sret_win,
        hc.sret_stack_disjoint, hc.sret_evalcode_disjoint,
        hc.ra_align, (by have := hx.sp_headroom; omega), hc.stack_ram.1, hc.stack_win,
        rfl, hVtruthyMcall, hVboolMcall, hNotExtras,
        hx.truthy_stk, hx.boolcode_stk, hx.sret_boolcode, hx.truthy_arena, hx.bool_arena,
        hx.code_stk, hx.sret_inSL, hMcallM0,
        (by have := hx.sp_SLhi; have := hx.SLhi_ram; omega), (by have := hx.sp16; omega),
        hx.SLhi_ram, hx.sp_SLhi,
        hArmg8, hArmg9, hArmg18, hArmg2, hbridge⟩
  -- === block D: shared epilogue → EvalExitD .bool(!truthy) (via blockD_v_rec) ===
  obtain ⟨c4, hs4, hExitDe⟩ :=
    blockD_v_rec g N A SL φfe φce st' (.bool (!vsub.truthy)) sp r sret v8 v9 v18 c2.σ.sailOutput m0
      c3 ⟨mpreC, hPreD⟩
  obtain ⟨hExitE, hMemExt, φf', φc', hpf', hpc', hSurv⟩ := hExitDe
  have hStoreLe := evalE_store_mono _hEvalE
  have hExit : EvalExit g N A SL φf φc st.store.frames.size st.store.closures.size
      st' (.bool (!vsub.truthy)) sp r sret m0 c4 :=
    evalExit_of_phiExtends hpfe hpce hExitE hStoreLe.1 hStoreLe.2
  exact ⟨c4, ((hs1.trans hs2).trans hs3).trans hs4, hExit, hMemExt,
    φf', φc', hpfe.trans (PhiExtends.mono hStoreLe.1 hpf'),
    hpce.trans (PhiExtends.mono hStoreLe.2 hpc'), hSurv⟩

end Vsa.Sim
