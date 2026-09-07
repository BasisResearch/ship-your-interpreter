import Vsa.Sim.RuntimeOwnershipAllocation
import Vsa.Sim.RuntimeOwnershipSeparation
import Vsa.Sim.EnvDefBridges4
import Vsa.Sim.EnvDefBridges3
import Vsa.Sim.rows.EnvDefineEpilogue
import Vsa.Sim.BlockAdapter
import Vsa.Sim.ReprCopy
import Vsa.Sim.EqNeReprReadback
import Vsa.Sim.EnvCallBridge
import Vsa.Sim.HeapOps

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa
open Register
open Vsa.Machine (Config)
open Vsa.MemRepr
open Vsa.RuntimeRepr
open Vsa.Logic (Triple)

namespace Vsa.Sim

/-- The append store block, with the live helper stack pointer retained. -/
theorem appendStoreRowSp (env src copied sp : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem) :
    Triple
      (fun c => SegPre appendStoreSeg (appendStoreL env src copied) lds
          0x80002b44#64 m0 c ∧
        c.σ.regs.get? Register.x2 = some sp)
      (fun c => AppendStorePost env src copied lds m0 c ∧
        c.σ.regs.get? Register.x2 = some sp ∧ c.tick < 2) := by
  intro c ⟨hpre, hsp⟩
  obtain ⟨hG, hmem, hpc, ⟨vm, hmi⟩, hL, hkeys, hfacts, htick⟩ := hpre
  obtain ⟨σ', i', hs, hi', hG', hmem', _hout, hpc', _hmi', _hregs', hframe⟩ :=
    segEval_sound appendStoreSeg c.σ c.tick c.steps 0x80002b44#64 vm
      (appendStoreL env src copied) lds hG hpc hmi hL hkeys hfacts
      (by show ChainOK 0x80002b44#64 [20, 21, 9] appendStoreSeg; decide) htick
  rw [hmem] at hmem'
  refine ⟨⟨σ', i', c.steps + evalBlocksFuel appendStoreSeg⟩, hs,
    ⟨⟨hG', hmem', ?_⟩, ?_, hi'⟩⟩
  · rw [hpc']; rfl
  · exact (hframe Register.x2 (by decide) (by decide)).trans hsp

/-- Exact post-store readbacks consumed by `frameRepr_append`.  These are
byte-level facts, not an assumed post-state `FrameRepr`. -/
structure EnvDefineAppendReadback
    (m : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (e : Nat) (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value)
    (cap names vals : Nat) : Prop where
  count : read32 m e = some (vars.length + 1)
  capRead : read32 m (e + 4) = some cap
  capBound : vars.length + 1 ≤ cap
  namesRead : read64 m (e + 8) = some names
  valsRead : read64 m (e + 16) = some vals
  old : ∀ i, (h : i < vars.length) →
    (∃ q, read64 m (names + 8 * i) = some q ∧ CString m q (vars[i].1)) ∧
    ValueRepr m N φc (vals + 24 * i) (vars[i].2)
  parentNone : parent = none → read64 m (e + 24) = some 0
  parentSome : ∀ pa, parent = some pa →
    read64 m (e + 24) = some (φf pa) ∧ φf pa ≠ 0
  newName : ∃ q, read64 m (names + 8 * vars.length) = some q ∧ CString m q name
  newValue : ValueRepr m N φc (vals + 24 * vars.length) v

theorem EnvDefineAppendReadback.frame
    {m : Mem} {N : NativeAddrs} {φf φc : Vsa.While.Addr → Nat}
    {e : Nat} {parent : Option Vsa.While.Addr}
    {vars : List (String × Vsa.While.Value)}
    {name : String} {v : Vsa.While.Value}
    {cap names vals : Nat}
    (h : EnvDefineAppendReadback m N φf φc e parent vars name v cap names vals) :
    FrameRepr m N φf φc e ⟨parent, vars ++ [(name, v)]⟩ :=
  frameRepr_append m N φf φc e parent vars name v cap names vals
    h.count h.capRead h.capBound h.namesRead h.valsRead h.old
    h.parentNone h.parentSome h.newName h.newValue

/-- Exact public-memory preservation required of the append write log. -/
structure AppendStorePublicFrame
    (sp env src copied : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) : Prop where
  code : ∀ a, 0x80002a5c ≤ a → a < 0x80002c10 →
    (writeLog m0 (evalBlocks appendStoreSeg
      (SegEvalState.init (appendStoreL env src copied) lds)).log)[a]? = m0[a]?
  spills : ∀ a, sp.toNat ≤ a → a < sp.toNat + 64 →
    (writeLog m0 (evalBlocks appendStoreSeg
      (SegEvalState.init (appendStoreL env src copied) lds)).log)[a]? = m0[a]?

/-- The reflected append log has only real store widths. -/
theorem appendStoreLogWidths (env src copied : BitVec 64)
    (lds : List (List (BitVec 8))) :
    ∀ e ∈ (evalBlocks appendStoreSeg
      (SegEvalState.init (appendStoreL env src copied) lds)).log,
      e.2.1 = 1 ∨ e.2.1 = 2 ∨ e.2.1 = 4 ∨ e.2.1 = 8 := by
  intro e he
  simp [appendStoreSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM,
    wentryM, widthOfM, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG,
    eraseG, eaddrM, mkLine, decodeM] at he
  rcases he with rfl | rfl | rfl | rfl | rfl <;> simp

/-- The five reflected stores, normalized to the semantic append addresses. -/
theorem appendStoreLogExact
    (env src copied : BitVec 64) (lds : List (List (BitVec 8)))
    (count names vals : Nat)
    (hcount : bytesVal .lw (lds.getD 0 []) = BitVec.ofNat 64 count)
    (hnames : bytesVal .ld (lds.getD 1 []) = BitVec.ofNat 64 names)
    (hvals : bytesVal .ld (lds.getD 2 []) = BitVec.ofNat 64 vals)
    (hcount32 : count + 1 < 2^31)
    (hnamesHi : names + 8 * count + 8 ≤ 2^64)
    (hvalsHi : vals + 24 * count + 24 ≤ 2^64)
    (henvHi : env.toNat + 4 ≤ 2^64) :
    (evalBlocks appendStoreSeg
      (SegEvalState.init (appendStoreL env src copied) lds)).log =
      [(names + 8 * count, 8, copied),
       (vals + 24 * count, 8, bytesVal .ld (lds.getD 3 [])),
       (vals + 24 * count + 8, 8, bytesVal .ld (lds.getD 4 [])),
       (vals + 24 * count + 16, 8, bytesVal .ld (lds.getD 5 [])),
       (env.toNat, 4, BitVec.ofNat 64 (count + 1))] := by
  have hhead : lds.head?.getD [] = lds.getD 0 [] := by cases lds <;> rfl
  have hc : bytesVal .lw (lds.head?.getD []) = BitVec.ofNat 64 count :=
    (congrArg (bytesVal .lw) hhead).trans hcount
  have hn : bytesVal .ld (lds[1]?.getD []) = BitVec.ofNat 64 names := hnames
  have hv : bytesVal .ld (lds[2]?.getD []) = BitVec.ofNat 64 vals := hvals
  have hcount64 : count < 2^64 := by omega
  have hnames64 : names < 2^64 := by omega
  have hvals64 : vals < 2^64 := by omega
  have hstride8 :
      (shift_bits_left (bytesVal .lw (lds.head?.getD []))
        (Sail.BitVec.extractLsb (3#6) 5 0)).toNat = 8 * count := by
    rw [hc, shl3_lit, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount64]
    rw [show (2 : Nat) ^ 3 = 8 by decide]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hstride24 :
      (shift_bits_left
          (shift_bits_left (bytesVal .lw (lds.head?.getD []))
              (Sail.BitVec.extractLsb (1#6) 5 0) +
            bytesVal .lw (lds.head?.getD []))
          (Sail.BitVec.extractLsb (3#6) 5 0)).toNat = 24 * count := by
    rw [hc, congrArg BitVec.toNat (stride_24 count (by omega)),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hinc :
      sign_extend (m := 64)
          (Sail.BitVec.extractLsb
            ((BitVec.ofNat 64 count) + sign_extend (m := 64) (1#12)) 31 0) =
        BitVec.ofNat 64 (count + 1) := by
    apply BitVec.eq_of_toNat_eq
    have hsext1 : (sign_extend (m := 64) (1#12) : BitVec 64).toNat = 1 := by decide
    have hsum :
        ((BitVec.ofNat 64 count) + sign_extend (m := 64) (1#12)).toNat = count + 1 := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hcount64,
        hsext1, Nat.mod_eq_of_lt (by omega)]
    show ((Sail.BitVec.extractLsb
        ((BitVec.ofNat 64 count) + sign_extend (m := 64) (1#12)) 31 0).signExtend 64).toNat = _
    have hslice : Sail.BitVec.extractLsb
        ((BitVec.ofNat 64 count) + sign_extend (m := 64) (1#12)) 31 0 =
          BitVec.ofNat 32 (count + 1) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat]
      show (BitVec.ofNat (31 - 0 + 1)
          ((((BitVec.ofNat 64 count) + sign_extend (m := 64) (1#12)).toNat) >>> 0)).toNat = _
      rw [BitVec.toNat_ofNat, Nat.shiftRight_zero, hsum]
    rw [hslice, BitVec.toNat_signExtend]
    have hmsb : (BitVec.ofNat 32 (count + 1)).msb = false := by
      rw [BitVec.msb_eq_getLsbD_last]
      simp only [BitVec.getLsbD_ofNat]
      rw [Nat.testBit_lt_two_pow (by omega)]
      rfl
    rw [hmsb, if_neg (by simp), Nat.add_zero, BitVec.toNat_setWidth,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : count + 1 < 2 ^ (31 - 0 + 1)),
      Nat.mod_eq_of_lt (by omega : count + 1 < 2 ^ 64)]
  simp [appendStoreSeg, evalBlocks, evalBlock, SegEvalState.init, wlogM,
    wentryM, widthOfM, runGM, stepGM, stepLdsM, wvalM, srcVal, lookupG,
    eraseG, eaddrM, mkLine, decodeM, shamtOf]
  constructor
  · constructor
    · rw [congrArg BitVec.toNat hn, hstride8, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hnames64]
      have hz : (sign_extend (m := 64) (0#12) : BitVec 64).toNat = 0 := by decide
      rw [hz, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    · simp [appendStoreL, lookupG, eraseG]
  · constructor
    · rw [congrArg BitVec.toNat hv, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hvals64, hstride24]
      have hz : (sign_extend (m := 64) (0#12) : BitVec 64).toNat = 0 := by decide
      rw [hz, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    · constructor
      · rw [congrArg BitVec.toNat hv, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt hvals64, hstride24]
        have h8 : (sign_extend (m := 64) (8#12) : BitVec 64).toNat = 8 := by decide
        rw [h8, Nat.mod_eq_of_lt (by omega)]
      · constructor
        · rw [congrArg BitVec.toNat hv, BitVec.toNat_ofNat,
            Nat.mod_eq_of_lt hvals64, hstride24]
          have h16 : (sign_extend (m := 64) (16#12) : BitVec 64).toNat = 16 := by decide
          rw [h16, Nat.mod_eq_of_lt (by omega)]
        · constructor
          · simp [appendStoreL, lookupG, eraseG]
            have hz : (sign_extend (m := 64) (0#12) : BitVec 64).toNat = 0 := by decide
            rw [hz, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
          · rw [hc]
            exact hinc

/-- Concrete arena windows cover every entry of the normalized append log. -/
theorem appendStoreWritesInArena
    (A : Arena) (env src copied : BitVec 64)
    (lds : List (List (BitVec 8))) (count names vals : Nat)
    (hcount : bytesVal .lw (lds.getD 0 []) = BitVec.ofNat 64 count)
    (hnames : bytesVal .ld (lds.getD 1 []) = BitVec.ofNat 64 names)
    (hvals : bytesVal .ld (lds.getD 2 []) = BitVec.ofNat 64 vals)
    (hcount32 : count + 1 < 2^31)
    (hnamesHi : names + 8 * count + 8 ≤ 2^64)
    (hvalsHi : vals + 24 * count + 24 ≤ 2^64)
    (henvHi : env.toNat + 4 ≤ 2^64)
    (hnameA : A.contains (names + 8 * count) 8)
    (hvalsA : A.contains (vals + 24 * count) 24)
    (henvA : A.contains env.toNat 4) :
    ∀ e ∈ (evalBlocks appendStoreSeg
        (SegEvalState.init (appendStoreL env src copied) lds)).log,
      A.contains e.1 e.2.1 := by
  change A.lo ≤ vals + 24 * count ∧ vals + 24 * count + 24 ≤ A.hi at hvalsA
  obtain ⟨hvalsLo, hvalsHiA⟩ := hvalsA
  intro e he
  rw [appendStoreLogExact env src copied lds count names vals hcount hnames hvals
    hcount32 hnamesHi hvalsHi henvHi] at he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact hnameA
  · change A.contains (vals + 24 * count) 8
    exact ⟨hvalsLo, by omega⟩
  · change A.contains (vals + 24 * count + 8) 8
    exact ⟨by omega, by omega⟩
  · change A.contains (vals + 24 * count + 16) 8
    exact ⟨by omega, hvalsHiA⟩
  · exact henvA

/-- Concrete memory tower induced by the five append stores. -/
def AppendStoreTower (m : Mem) (env names vals count : Nat)
    (copied d0 d1 d2 : BitVec 64) : Mem :=
  writeMap4
    (writeMap8
      (writeMap8
        (writeMap8
          (writeMap8 m (names + 8 * count) (sdData_val copied))
          (vals + 24 * count) (sdData_val d0))
        (vals + 24 * count + 8) (sdData_val d1))
      (vals + 24 * count + 16) (sdData_val d2))
    env (swData (BitVec.ofNat 64 (count + 1)))

/-- Addresses untouched by the name slot, value slot, and count stores. -/
def AppendUntouched (env names vals count a : Nat) : Prop :=
  (a < names + 8 * count ∨ names + 8 * count + 8 ≤ a) ∧
  (a < vals + 24 * count ∨ vals + 24 * count + 24 ≤ a) ∧
  (a < env ∨ env + 4 ≤ a)

theorem appendStoreTowerOutside
    (m : Mem) (env names vals count a : Nat)
    (copied d0 d1 d2 : BitVec 64)
    (ha : AppendUntouched env names vals count a) :
    (AppendStoreTower m env names vals count copied d0 d1 d2)[a]? = m[a]? := by
  rcases ha with ⟨hn, hv, he⟩
  unfold AppendStoreTower
  rw [getElem_writeMap4_disjoint _ _ _ _ he,
    getElem_writeMap8_disjoint _ _ _ _ (by rcases hv with h | h <;> omega),
    getElem_writeMap8_disjoint _ _ _ _ (by rcases hv with h | h <;> omega),
    getElem_writeMap8_disjoint _ _ _ _ (by rcases hv with h | h <;> omega),
    getElem_writeMap8_disjoint _ _ _ _ hn]

theorem appendStoreTowerAgree
    (m : Mem) (env names vals count : Nat)
    (copied d0 d1 d2 : BitVec 64) :
    AgreeP (AppendUntouched env names vals count) m
      (AppendStoreTower m env names vals count copied d0 d1 d2) := by
  intro a ha
  exact (appendStoreTowerOutside m env names vals count a copied d0 d1 d2 ha).symm

/-- The three value stores are an exact total 24-byte copy from the loaded
source words; the final count store is required to be disjoint. -/
theorem appendStoreTowerCopy
    (m : Mem) (env names vals count src : Nat)
    (copied d0 d1 d2 : BitVec 64)
    (b0 b1 b2 : List (BitVec 8))
    (hd0 : d0 = bytesVal .ld b0) (hd1 : d1 = bytesVal .ld b1)
    (hd2 : d2 = bytesVal .ld b2)
    (hp0 : LPins8 m src b0) (hp1 : LPins8 m (src + 8) b1)
    (hp2 : LPins8 m (src + 16) b2)
    (henv : env + 4 ≤ vals + 24 * count ∨
      vals + 24 * count + 24 ≤ env) :
    ∀ j, j < 24 →
      (AppendStoreTower m env names vals count copied d0 d1 d2)[vals + 24 * count + j]? =
        some ((m[src + j]?).getD 0) := by
  intro j hj
  subst d0; subst d1; subst d2
  unfold AppendStoreTower
  rw [getElem_writeMap4_disjoint _ _ _ _ (by rcases henv with h | h <;> omega)]
  by_cases hj0 : j < 8
  · rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
      getElem_writeMap8_disjoint _ _ _ _ (by omega),
      writeMap8_ld_byte _ (vals + 24 * count) b0 j hj0]
    exact congrArg some (lpins8_byte m src b0 hp0 j hj0).symm
  · by_cases hj1 : j < 16
    · have hk : j - 8 < 8 := by omega
      rw [getElem_writeMap8_disjoint _ _ _ _ (by omega),
        show vals + 24 * count + j = vals + 24 * count + 8 + (j - 8) by omega,
        writeMap8_ld_byte _ (vals + 24 * count + 8) b1 (j - 8) hk,
        show src + j = src + 8 + (j - 8) by omega]
      exact congrArg some (lpins8_byte m (src + 8) b1 hp1 (j - 8) hk).symm
    · have hk : j - 16 < 8 := by omega
      rw [show vals + 24 * count + j = vals + 24 * count + 16 + (j - 16) by omega,
        writeMap8_ld_byte _ (vals + 24 * count + 16) b2 (j - 16) hk,
        show src + j = src + 16 + (j - 16) by omega]
      exact congrArg some (lpins8_byte m (src + 16) b2 hp2 (j - 16) hk).symm

/-- Represented-footprint geometry needed to preserve the old frame while its
fresh terminal slots and count are written. -/
structure EnvDefineAppendFootprint
    (m : Mem) (env names vals count copied src : Nat)
    (vars : List (String × Vsa.While.Value)) (name : String)
    (v : Vsa.While.Value) : Prop where
  headerRest : ∀ k, env + 4 ≤ k → k < env + 32 →
    AppendUntouched env names vals count k
  oldNameSlots : ∀ i, i < vars.length → ∀ k, k < 8 →
    AppendUntouched env names vals count (names + 8 * i + k)
  oldNames : ∀ i, (hi : i < vars.length) → ∀ q,
    read64 m (names + 8 * i) = some q → ∀ k, k ≤ (vars[i].1).length →
      AppendUntouched env names vals count (q + k)
  oldValueHeaders : ∀ i, i < vars.length → ∀ k,
    valHeader (vals + 24 * i) k → AppendUntouched env names vals count k
  oldValueStrings : ∀ i, (hi : i < vars.length) →
    ValuePayloadCovered (AppendUntouched env names vals count) m
      (vals + 24 * i) vars[i].2
  copiedString : ∀ k, k ≤ name.length →
    AppendUntouched env names vals count (copied + k)
  sourcePayload : ValuePayloadCovered (AppendUntouched env names vals count)
    m src v
  newNameValue : names + 8 * count + 8 ≤ vals + 24 * count ∨
    vals + 24 * count + 24 ≤ names + 8 * count
  newNameCount : names + 8 * count + 8 ≤ env ∨ env + 4 ≤ names + 8 * count
  valueCount : env + 4 ≤ vals + 24 * count ∨ vals + 24 * count + 24 ≤ env

/-- The exact five-write log plus represented-footprint geometry reconstructs
all append readbacks. No post-state representation is assumed. -/
theorem appendStoreReadback
    (env src copied : BitVec 64) (lds : List (List (BitVec 8)))
    (m : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value) (cap names vals : Nat)
    (hframe : FrameRepr m N φf φc env.toNat ⟨parent, vars⟩)
    (hcap : read32 m (env.toNat + 4) = some cap)
    (happendArm : vars.length < cap)
    (hnamesMem : read64 m (env.toNat + 8) = some names)
    (hvalsMem : read64 m (env.toNat + 16) = some vals)
    (hcount : bytesVal .lw (lds.getD 0 []) = BitVec.ofNat 64 vars.length)
    (hnames : bytesVal .ld (lds.getD 1 []) = BitVec.ofNat 64 names)
    (hvals : bytesVal .ld (lds.getD 2 []) = BitVec.ofNat 64 vals)
    (hp0 : LPins8 m src.toNat (lds.getD 3 []))
    (hp1 : LPins8 m (src.toNat + 8) (lds.getD 4 []))
    (hp2 : LPins8 m (src.toNat + 16) (lds.getD 5 []))
    (hword : ValueWordRepr m N φc src.toNat v)
    (hcopied : CString m copied.toNat name)
    (hfp : EnvDefineAppendFootprint m env.toNat names vals vars.length
      copied.toNat src.toNat vars name v)
    (hcount32 : vars.length + 1 < 2^31)
    (hnamesHi : names + 8 * vars.length + 8 ≤ 2^64)
    (hvalsHi : vals + 24 * vars.length + 24 ≤ 2^64)
    (henvHi : env.toNat + 4 ≤ 2^64) :
    EnvDefineAppendReadback
      (writeLog m (evalBlocks appendStoreSeg
        (SegEvalState.init (appendStoreL env src copied) lds)).log)
      N φf φc env.toNat parent vars name v cap names vals := by
  let m' := AppendStoreTower m env.toNat names vals vars.length copied
    (bytesVal .ld (lds.getD 3 [])) (bytesVal .ld (lds.getD 4 []))
    (bytesVal .ld (lds.getD 5 []))
  have hmem : writeLog m (evalBlocks appendStoreSeg
        (SegEvalState.init (appendStoreL env src copied) lds)).log = m' := by
    rw [appendStoreLogExact env src copied lds vars.length names vals hcount hnames hvals
      hcount32 hnamesHi hvalsHi henvHi]
    rfl
  rw [hmem]
  have hag : AgreeP (AppendUntouched env.toNat names vals vars.length) m m' :=
    appendStoreTowerAgree m env.toNat names vals vars.length copied
      (bytesVal .ld (lds.getD 3 [])) (bytesVal .ld (lds.getD 4 []))
      (bytesVal .ld (lds.getD 5 []))
  obtain ⟨hcount0, ⟨cap0, hcap0, hcapLe⟩,
    ⟨pn, pv, hpn, hpv, hold⟩, hparent⟩ := hframe
  have hcapEq : cap0 = cap := Option.some.inj (hcap0.symm.trans hcap)
  have hpnEq : pn = names := Option.some.inj (hpn.symm.trans hnamesMem)
  have hpvEq : pv = vals := Option.some.inj (hpv.symm.trans hvalsMem)
  subst cap0; subst pn; subst pv
  have hcapNext : vars.length + 1 ≤ cap := by omega
  refine ⟨?_, ?_, hcapNext, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold m' AppendStoreTower
    rw [read32_writeMap4, swData_toNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  · rw [← read32_agreeP hag (fun k hk => hfp.headerRest _ (by omega) (by omega))]
    exact hcap
  · rw [← read64_agreeP hag (fun k hk => hfp.headerRest _ (by omega) (by omega))]
    exact hnamesMem
  · rw [← read64_agreeP hag (fun k hk => hfp.headerRest _ (by omega) (by omega))]
    exact hvalsMem
  · intro i hi
    obtain ⟨⟨q, hq, hqs⟩, hv⟩ := hold i hi
    refine ⟨⟨q, ?_, ?_⟩, ?_⟩
    · rw [← read64_agreeP hag (hfp.oldNameSlots i hi)]
      exact hq
    · exact cstring_agreeP hag hqs (hfp.oldNames i hi q hq)
    · exact valueRepr_agreeP hag (hfp.oldValueHeaders i hi)
        (hfp.oldValueStrings i hi) hv
  · intro hnone
    simp only [hnone] at hparent
    rw [← read64_agreeP hag (fun k hk => hfp.headerRest _ (by omega) (by omega))]
    exact hparent
  · intro pa hsome
    simp only [hsome] at hparent
    refine ⟨?_, hparent.2⟩
    rw [← read64_agreeP hag (fun k hk => hfp.headerRest _ (by omega) (by omega))]
    exact hparent.1
  · refine ⟨copied.toNat, ?_, ?_⟩
    · unfold m' AppendStoreTower
      rw [read64_writeMap4_disjoint _ _ _ _ hfp.newNameCount,
        read64_writeMap8_disjoint _ _ _ _ (by rcases hfp.newNameValue with h | h <;> omega),
        read64_writeMap8_disjoint _ _ _ _ (by rcases hfp.newNameValue with h | h <;> omega),
        read64_writeMap8_disjoint _ _ _ _ (by rcases hfp.newNameValue with h | h <;> omega),
        read64_writeMap8, sdData_toNat]
    · exact cstring_agreeP hag hcopied (hfp.copiedString)
  · apply valueRepr_copy_total_exact
    · exact appendStoreTowerCopy m env.toNat names vals vars.length src.toNat copied
        (bytesVal .ld (lds.getD 3 [])) (bytesVal .ld (lds.getD 4 []))
        (bytesVal .ld (lds.getD 5 [])) (lds.getD 3 []) (lds.getD 4 [])
        (lds.getD 5 []) rfl rfl rfl hp0 hp1 hp2 hfp.valueCount
    · cases v with
      | str s => exact fun p hp k hk => hag _ (hfp.sourcePayload p hp k hk)
      | native f => exact fun p hp k hk => hag _ (hfp.sourcePayload p hp k hk)
      | null | bool | int | closure => trivial
    · exact hword.repr

/-- Exact footprint certificate for an unchanged frame under the append
write-set. -/
structure FrameAppendFootprint
    (m : Mem) (env names vals count : Nat) (e : Nat)
    (f : Vsa.While.Frame) : Prop where
  header : ∀ k, envHeader e k → AppendUntouched env names vals count k
  slots : ∀ pn pv, read64 m (e + 8) = some pn → read64 m (e + 16) = some pv →
    ∀ i, i < f.vars.length →
      (∀ k, k < 8 → AppendUntouched env names vals count (pn + 8 * i + k)) ∧
      (∀ k, valHeader (pv + 24 * i) k → AppendUntouched env names vals count k)
  namesPayload : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, (hi : i < f.vars.length) → ∀ q,
      read64 m (pn + 8 * i) = some q → ∀ k, k ≤ (f.vars[i].1).length →
        AppendUntouched env names vals count (q + k)
  valuePayload : ∀ pn pv, read64 m (e + 8) = some pn →
    read64 m (e + 16) = some pv → ∀ i, (hi : i < f.vars.length) →
      ValuePayloadCovered (AppendUntouched env names vals count) m
        (pv + 24 * i) f.vars[i].2

theorem FrameAppendFootprint.survive
    {m m' : Mem} {N : NativeAddrs} {φf φc : Vsa.While.Addr → Nat}
    {env names vals count e : Nat} {f : Vsa.While.Frame}
    (h : FrameAppendFootprint m env names vals count e f)
    (hag : AgreeP (AppendUntouched env names vals count) m m')
    (hfr : FrameRepr m N φf φc e f) : FrameRepr m' N φf φc e f :=
  frameRepr_agreeP hag h.header h.slots h.namesPayload h.valuePayload hfr

/-- Exact footprint certificate for an unchanged closure. -/
structure ClosureAppendFootprint
    (m m' : Mem) (env names vals count p : Nat)
    (cd : Vsa.While.ClosureData) : Prop where
  header : ∀ k, closHeader p k → AppendUntouched env names vals count k
  expr : ∀ q, read64 m p = some q →
    ExprRepr m q (.fn cd.name cd.params cd.body) →
    ExprRepr m' q (.fn cd.name cd.params cd.body)

theorem ClosureAppendFootprint.survive
    {m m' : Mem} {φf : Vsa.While.Addr → Nat}
    {env names vals count p : Nat} {cd : Vsa.While.ClosureData}
    (h : ClosureAppendFootprint m m' env names vals count p cd)
    (hag : AgreeP (AppendUntouched env names vals count) m m')
    (hcl : ClosureRepr m φf p cd) : ClosureRepr m' φf p cd :=
  closureRepr_agreeP hag h.header h.expr hcl

/-- Whole-store footprint for the three append write windows. -/
structure StoreAppendFootprint
    (m m' : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (store : Vsa.While.Store) (target : Vsa.While.Addr)
    (env names vals count : Nat) : Prop where
  frames : ∀ fa, (hfa : fa < store.frames.size) → fa ≠ target →
    FrameAppendFootprint m env names vals count (φf fa) store.frames[fa]
  closures : ∀ ca, (hca : ca < store.closures.size) →
    ClosureAppendFootprint m m' env names vals count (φc ca) store.closures[ca]

/-- Exact protected footprints supply the unchanged store after append. -/
theorem StoreAppendFootprint.of_covered
    {m m' : Mem} {N : NativeAddrs} {φf φc : Vsa.While.Addr → Nat}
    {store : Vsa.While.Store} {target : Vsa.While.Addr} {names vals : Nat}
    (ht : target < store.frames.size)
    (hframes : ∀ fa, (hf : fa < store.frames.size) → fa ≠ target →
      FrameFootprintCovered m φf fa store.frames[fa]
        (AppendOutside (φf target) names vals store.frames[target].vars.length))
    (hclosures : ∀ ca, (hc : ca < store.closures.size) →
      ClosureFootprintCovered m φc ca store.closures[ca]
        (AppendOutside (φf target) names vals store.frames[target].vars.length))
    (hag : AgreeP (AppendUntouched (φf target) names vals
      store.frames[target].vars.length) m m') :
    StoreAppendFootprint m m' N φf φc store target (φf target) names vals
      store.frames[target].vars.length := by
  refine ⟨?_, ?_⟩
  · intro fa hfa hne
    have h := hframes fa hfa hne
    exact
      { header := by
          intro k hk
          simpa [AppendOutside, AppendUntouched] using h.header k hk
        slots := by
          intro pn pv hpn hpv i hi
          simpa [AppendOutside, AppendUntouched] using h.slots pn pv hpn hpv i hi
        namesPayload := by
          intro pn pv hpn hpv i hi q hq k hk
          simpa [AppendOutside, AppendUntouched] using
            h.names pn pv hpn hpv i hi q hq k hk
        valuePayload := by
          intro pn pv hpn hpv i hi
          simpa [AppendOutside, AppendUntouched] using h.values pn pv hpn hpv i hi }
  · intro ca hca
    have h := hclosures ca hca
    refine
      { header := by
          intro k hk
          simpa [AppendOutside, AppendUntouched] using h.header k hk
        expr := ?_ }
    intro q hq hexpr
    apply exprRepr_agreeP hag
    intro a ha
    simpa [AppendOutside, AppendUntouched] using h.ast q hq a ha
    exact hexpr

/-- The global heap-separation invariant supplies the append-specific
representation footprint. -/
theorem StoreAppendFootprint.of_heap_owned
    {m m' : Mem} {N : NativeAddrs} {φf φc : Vsa.While.Addr → Nat}
    {store : Vsa.While.Store} {target : Vsa.While.Addr}
    {cap names vals : Nat}
    (ht : target < store.frames.size)
    (howned : StoreHeapOwned m φf φc exts store)
    (hcap : read32 m (φf target + 4) = some cap)
    (hnames : read64 m (φf target + 8) = some names)
    (hvals : read64 m (φf target + 16) = some vals)
    (happend : store.frames[target].vars.length < cap)
    (hag : AgreeP (AppendUntouched (φf target) names vals
      store.frames[target].vars.length) m m') :
    StoreAppendFootprint m m' N φf φc store target (φf target) names vals
      store.frames[target].vars.length := by
  obtain ⟨hframes, hclosures⟩ :=
    howned.appendSeparated target ht cap names vals hcap hnames hvals happend
  exact StoreAppendFootprint.of_covered ht hframes hclosures hag

/-- Allocation roles and immutable sharing supply the existing append consumer. -/
theorem StoreAppendFootprint.of_runtime_owned
    {m m' : Mem} {N : NativeAddrs} {φf φc : Vsa.While.Addr → Nat}
    {A : Arena} {exts : List Extent} {alloc : RuntimeOwnership.Allocations}
    {shared readable writes : Nat → Prop}
    {store : Vsa.While.Store} {target : Vsa.While.Addr}
    {cap names vals : Nat}
    (ht : target < store.frames.size)
    (howned : RuntimeOwnership.HeapOwned A exts m φf φc alloc
      shared readable writes store)
    (hcap : read32 m (φf target + 4) = some cap)
    (hnames : read64 m (φf target + 8) = some names)
    (hvals : read64 m (φf target + 16) = some vals)
    (happend : store.frames[target].vars.length < cap)
    (hag : AgreeP (AppendUntouched (φf target) names vals
      store.frames[target].vars.length) m m') :
    StoreAppendFootprint m m' N φf φc store target (φf target) names vals
      store.frames[target].vars.length := by
  obtain ⟨hframes, hclosures⟩ := howned.store.appendSeparated howned.ledger
    howned.immutable target ht cap names vals hcap hnames hvals happend
  exact StoreAppendFootprint.of_covered ht hframes hclosures hag

#print axioms StoreAppendFootprint.of_covered
#print axioms StoreAppendFootprint.of_runtime_owned

/-- Lift the reconstructed target append to the whole semantic store. -/
theorem storeDefineAdvance_of_append
    {m m' : Mem} {N : NativeAddrs} {A : Arena}
    {φf φc : Vsa.While.Addr → Nat} {store : Vsa.While.Store}
    {target : Vsa.While.Addr} {f : Vsa.While.Frame}
    {name : String} {v : Vsa.While.Value} {env names vals count : Nat}
    (hstore : StoreRepr m N A φf φc store)
    (hget : store.frames[target]? = some f)
    (habsent : f.vars.any (·.1 == name) = false)
    (hnew : FrameRepr m' N φf φc (φf target)
      ⟨f.parent, f.vars ++ [(name, v)]⟩)
    (hag : AgreeP (AppendUntouched env names vals count) m m')
    (hfoot : StoreAppendFootprint m m' N φf φc store target env names vals count) :
    StoreDefineAdvance N A φf φc store target name v m' := by
  obtain ⟨htargetBound, htargetGet⟩ := Array.getElem?_eq_some_iff.mp hget
  refine
    { mutated := ?_
      others := ?_
      closures := ?_
      φf_inj := ?_
      φc_inj := ?_
      frames_arena := ?_
      closures_arena := ?_ }
  · intro _
    simp only [Vsa.While.Store.define, Array.getElem_modify, if_pos]
    rw [htargetGet, habsent]
    exact hnew
  · intro fa hfa hne
    have hfaOld : fa < store.frames.size := by
      simpa [Vsa.While.Store.define] using hfa
    have hs := (hfoot.frames fa hfaOld hne).survive hag (hstore.frames fa hfaOld)
    simpa [Vsa.While.Store.define, Array.getElem_modify, hne, Ne.symm hne] using hs
  · intro ca hca
    have hcaOld : ca < store.closures.size := by
      simpa [Vsa.While.Store.define] using hca
    simpa [Vsa.While.Store.define] using
      (hfoot.closures ca hcaOld).survive hag (hstore.closures ca hcaOld)
  · intro p q hp hq heq
    exact hstore.φf_inj p q (by simpa [Vsa.While.Store.define] using hp)
      (by simpa [Vsa.While.Store.define] using hq) heq
  · intro p q hp hq heq
    exact hstore.φc_inj p q (by simpa [Vsa.While.Store.define] using hp)
      (by simpa [Vsa.While.Store.define] using hq) heq
  · intro fa hfa
    exact hstore.frames_arena fa (by simpa [Vsa.While.Store.define] using hfa)
  · intro ca hca
    exact hstore.closures_arena ca (by simpa [Vsa.While.Store.define] using hca)

/-- Arena containment of all five concrete append writes implies code/spill
preservation. -/
theorem appendStorePublicFrame_of_arena
    (A : Arena) (sp env src copied : BitVec 64)
    (lds : List (List (BitVec 8))) (m0 : Mem)
    (hwrites : ∀ e ∈ (evalBlocks appendStoreSeg
        (SegEvalState.init (appendStoreL env src copied) lds)).log,
      A.contains e.1 e.2.1)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo) :
    AppendStorePublicFrame sp env src copied lds m0 := by
  refine ⟨?_, ?_⟩
  · intro a ha0 ha1
    apply writeLog_getElem_disjoint a _ m0 (appendStoreLogWidths env src copied lds)
    intro e he
    obtain ⟨elo, ehi⟩ := hwrites e he
    rcases harenaCode with hbefore | hafter
    · right; omega
    · left; omega
  · intro a ha0 ha1
    apply writeLog_getElem_disjoint a _ m0 (appendStoreLogWidths env src copied lds)
    intro e he
    obtain ⟨elo, ehi⟩ := hwrites e he
    rcases harenaStack with hbefore | hafter
    · right; omega
    · left; omega
/-- Machine and semantic carrier at the shared append epilogue. -/
structure EnvDefineAppendReady
    (saved : (R : Register) → Option (RegisterType R))
    (env src copied sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value)
    (cap names vals : Nat) (c : Config) : Prop where
  row : AppendStorePost env src copied lds m0 c
  spReg : c.σ.regs.get? Register.x2 = some sp
  savedSpills : EnvDefineSavedSpillFrame sp saved c
  tick : c.tick < 2
  readback : EnvDefineAppendReadback c.σ.mem N φf φc env.toNat
    parent vars name v cap names vals

/-- Run the five-store append block, preserving the saved spill image and
landing the exact byte-level readback carrier. -/
theorem envDefineAppendStore
    (saved : (R : Register) → Option (RegisterType R))
    (env src copied sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value)
    (cap names vals : Nat)
    (A : Arena)
    (hnameA : A.contains (names + 8 * vars.length) 8)
    (hvalsA : A.contains (vals + 24 * vars.length) 24)
    (henvA : A.contains env.toNat 4)
    (harenaStack : A.hi ≤ sp.toNat ∨ sp.toNat + 64 ≤ A.lo)
    (harenaCode : A.hi ≤ 0x80002a5c ∨ 0x80002c10 ≤ A.lo)
    (hframe : FrameRepr m0 N φf φc env.toNat ⟨parent, vars⟩)
    (hcap : read32 m0 (env.toNat + 4) = some cap)
    (happendArm : vars.length < cap)
    (hnamesMem : read64 m0 (env.toNat + 8) = some names)
    (hvalsMem : read64 m0 (env.toNat + 16) = some vals)
    (hcount : bytesVal .lw (lds.getD 0 []) = BitVec.ofNat 64 vars.length)
    (hnames : bytesVal .ld (lds.getD 1 []) = BitVec.ofNat 64 names)
    (hvals : bytesVal .ld (lds.getD 2 []) = BitVec.ofNat 64 vals)
    (hp0 : LPins8 m0 src.toNat (lds.getD 3 []))
    (hp1 : LPins8 m0 (src.toNat + 8) (lds.getD 4 []))
    (hp2 : LPins8 m0 (src.toNat + 16) (lds.getD 5 []))
    (hword : ValueWordRepr m0 N φc src.toNat v)
    (hcopied : CString m0 copied.toNat name)
    (hfp : EnvDefineAppendFootprint m0 env.toNat names vals vars.length
      copied.toNat src.toNat vars name v)
    (hcount32 : vars.length + 1 < 2^31)
    (hnamesHi : names + 8 * vars.length + 8 ≤ 2^64)
    (hvalsHi : vals + 24 * vars.length + 24 ≤ 2^64)
    (henvHi : env.toNat + 4 ≤ 2^64) :
    Triple
      (fun c => SegPre appendStoreSeg (appendStoreL env src copied) lds
          0x80002b44#64 m0 c ∧
        c.σ.regs.get? Register.x2 = some sp ∧
        EnvDefineSavedSpillFrame sp saved c)
      (EnvDefineAppendReady saved env src copied sp lds m0 N φf φc
        parent vars name v cap names vals) := by
  intro c ⟨hpre, hsp, hsaved⟩
  have hwrites := appendStoreWritesInArena A env src copied lds vars.length names vals
    hcount hnames hvals hcount32 hnamesHi hvalsHi henvHi hnameA hvalsA henvA
  have hpublic := appendStorePublicFrame_of_arena A sp env src copied lds m0
    hwrites harenaStack harenaCode
  have hread := appendStoreReadback env src copied lds m0 N φf φc parent vars name v
    cap names vals hframe hcap happendArm hnamesMem hvalsMem hcount hnames hvals
    hp0 hp1 hp2 hword hcopied hfp hcount32 hnamesHi hvalsHi henvHi
  obtain ⟨c', hs, hrow, hsp', htick'⟩ :=
    appendStoreRowSp env src copied sp lds m0 c ⟨hpre, hsp⟩
  have hsaved' : EnvDefineSavedSpillFrame sp saved c' := by
    apply hsaved.of_interval_agree
    · intro a ha0 ha1
      rw [hrow.2.1, hpre.2.1]
      exact hpublic.code a ha0 ha1
    · intro a ha0 ha1
      rw [hrow.2.1, hpre.2.1]
      exact hpublic.spills a ha0 ha1
  have hread' : EnvDefineAppendReadback c'.σ.mem N φf φc env.toNat
      parent vars name v cap names vals := by
    rw [hrow.2.1]
    exact hread
  exact ⟨c', hs, hrow, hsp', hsaved', htick', hread'⟩

/-- Run the shared exact epilogue after append and retain the appended frame. -/
theorem envDefineAppendEpilogue
    (saved : (R : Register) → Option (RegisterType R))
    (env src copied sp : BitVec 64) (lds : List (List (BitVec 8)))
    (m0 : Mem) (N : NativeAddrs) (φf φc : Vsa.While.Addr → Nat)
    (parent : Option Vsa.While.Addr)
    (vars : List (String × Vsa.While.Value))
    (name : String) (v : Vsa.While.Value)
    (cap names vals : Nat) :
    Triple
      (EnvDefineAppendReady saved env src copied sp lds m0 N φf φc
        parent vars name v cap names vals)
      (fun c => ∃ m,
        EnvDefineEpilogueExactPost sp saved m c ∧
        FrameRepr c.σ.mem N φf φc env.toNat
          ⟨parent, vars ++ [(name, v)]⟩) := by
  intro c h
  have hframe := h.readback.frame
  obtain ⟨epiLds, hfacts, hvalues⟩ := h.savedSpills.chainFacts
  have hpre : SegPre envDefineEpilogueSeg (envDefineEpilogueL sp) epiLds
      0x80002aec#64 c.σ.mem c :=
    ⟨h.row.1, rfl, h.row.2.2, h.row.1.minstret, ⟨h.spReg, trivial⟩,
      (by show KeysOK [2]; decide), hfacts, h.tick⟩
  obtain ⟨c', hs, hp⟩ := envDefineEpilogueRow sp epiLds c.σ.mem c hpre
  have hret := envDefineEpilogueExact_of_post sp saved epiLds c.σ.mem c' hvalues hp
  refine ⟨c', hs, c.σ.mem, hret, ?_⟩
  rw [hret.mem]
  exact hframe

#print axioms appendStoreRowSp
#print axioms EnvDefineAppendReadback.frame
#print axioms appendStoreLogWidths
#print axioms appendStoreLogExact
#print axioms appendStoreReadback
#print axioms storeDefineAdvance_of_append
#print axioms appendStorePublicFrame_of_arena
#print axioms envDefineAppendStore
#print axioms envDefineAppendEpilogue

end Vsa.Sim
