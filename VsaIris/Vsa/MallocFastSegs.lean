import Vsa.Sim.ChainFactsTac
import Vsa.Sim.DeriveCaseRow
import VsaIris.Vsa.MallocFastCode
import VsaIris.Vsa.MallocFastLines
import Vsa.Sim.ExecRetEpilogue
import Vsa.Sim.Muldi3Spec
import Vsa.Sim.DlHeap

/-!
# `_malloc_r`'s top-split fast path, reflected

The path for a request `24 ≤ n ≤ 487` from a heap with no free chunk and a
clear `binblocks` bitmap, as `#derive_case` segments (chains generated from
`experiments/disasm.txt`). Calls to the lock hooks are `jal` seams between
segments.

* `segWrap` (`malloc`): `mv a1,a0; ld a0,_impure_ptr; j _malloc_r`.
* `segPro`: the frame, the size-class tests, `nb = (n + 23) & -16` saved at
  `8(sp)`.
* `segLock`/`segAcq`, `segUnlock`/`segRel`: the lock hooks and the retarget
  `ret`s.
* `segBins`: the size-class test, the bin index, both empty-bin checks, the
  unsorted-bin and `binblocks` tests (index-dependent, proved per size class);
* `segSplit`: the top size tests and the split stores (symbolic in the top).
* `segEpi`: the return value `top + 16` and the epilogue.

For each segment, `*_facts` discharges its `ChainFacts` from the path's code
bytes (`PathLoaded`) and named hypotheses on its pins.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail Vsa

namespace Vsa.Sim

#derive_case segWrap chain
  [(0x80004790#64, 0x00050593#32),
   (0x80004794#64, 0x4601b503#32)]
  terminator ⟨0x80004798#64, 0x0100006f#32, 0x6f#8, 0x00#8, 0x00#8, 0x01#8,
      .j, 0, 0, 0#13, 0x000010#21, 0#12⟩

#derive_case segPro chain
  [(0x800047a8#64, 0xfa010113#32),
   (0x800047ac#64, 0x04813823#32),
   (0x800047b0#64, 0x04113c23#32),
   (0x800047b4#64, 0x01758713#32),
   (0x800047b8#64, 0x02e00793#32),
   (0x800047bc#64, 0x00050413#32)]
  terminator ⟨0x800047c0#64, 0x08e7ee63#32, 0x63#8, 0xee#8, 0xe7#8, 0x08#8,
      .br bop.BLTU true, 15, 14, 0x09c#13, 0#21, 0#12⟩ ;;
  [(0x8000485c#64, 0x00100793#32),
   (0x80004860#64, 0xff077713#32),
   (0x80004864#64, 0x01f79793#32)]
  terminator ⟨0x80004868#64, 0xfcf77ce3#32, 0xe3#8, 0x7c#8, 0xf7#8, 0xfc#8,
      .br bop.BGEU false, 14, 15, 0x1fd8#13, 0#21, 0#12⟩ ;;
  []
  terminator ⟨0x8000486c#64, 0xfcb76ae3#32, 0xe3#8, 0x6a#8, 0xb7#8, 0xfc#8,
      .br bop.BLTU false, 14, 11, 0x1fd4#13, 0#21, 0#12⟩ ;;
  [(0x80004870#64, 0x00e13423#32)]

#derive_case segLock chain
  [(0x80005068#64, 0x4c818513#32)]
  terminator ⟨0x8000506c#64, 0x7750106f#32, 0x6f#8, 0x10#8, 0x50#8, 0x77#8,
      .j, 0, 0, 0#13, 0x001f74#21, 0#12⟩

#derive_case segAcq chain
  []
  terminator ⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case segUnlock chain
  [(0x80005070#64, 0x4c818513#32)]
  terminator ⟨0x80005074#64, 0x7850106f#32, 0x6f#8, 0x10#8, 0x50#8, 0x78#8,
      .j, 0, 0, 0#13, 0x001f84#21, 0#12⟩

#derive_case segRel chain
  []
  terminator ⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case segEpi chain
  [(0x80004c14#64, 0x00813783#32),
   (0x80004c18#64, 0x01078513#32)]
  terminator ⟨0x80004c1c#64, 0xc15ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xc1#8,
      .j, 0, 0, 0#13, 0x1ffc14#21, 0#12⟩ ;;
  [(0x80004830#64, 0x05813083#32),
   (0x80004834#64, 0x05013403#32),
   (0x80004838#64, 0x06010113#32)]
  terminator ⟨0x8000483c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
      .jr, 1, 0, 0#13, 0#21, 0x000#12⟩

#derive_case segBins chain
  [(0x80004878#64, 0x00813703#32),
   (0x8000487c#64, 0x1f700793#32)]
  terminator ⟨0x80004880#64, 0x4ee7f263#32, 0x63#8, 0xf2#8, 0xe7#8, 0x4e#8,
      .br bop.BGEU true, 15, 14, 0x4e4#13, 0#21, 0#12⟩ ;;
  [(0x80004d64#64, 0x00375893#32),
   (0x80004d68#64, 0x00189693#32),
   (0x80004d6c#64, 0x0026869b#32),
   (0x80004d70#64, 0x00369693#32)]
  terminator ⟨0x80004d74#64, 0xa69ff06f#32, 0x6f#8, 0xf0#8, 0x9f#8, 0xa6#8,
      .j, 0, 0, 0#13, 0x1ffa68#21, 0#12⟩ ;;
  [(0x800047dc#64, 0x00016817#32),
   (0x800047e0#64, 0x53480813#32),
   (0x800047e4#64, 0x00d806b3#32),
   (0x800047e8#64, 0x0086b783#32),
   (0x800047ec#64, 0xff068613#32)]
  terminator ⟨0x800047f0#64, 0x46c78863#32, 0x63#8, 0x88#8, 0xc7#8, 0x46#8,
      .br bop.BEQ true, 15, 12, 0x470#13, 0#21, 0#12⟩ ;;
  [(0x80004c60#64, 0x0186b783#32),
   (0x80004c64#64, 0x0028889b#32)]
  terminator ⟨0x80004c68#64, 0xc8f682e3#32, 0xe3#8, 0x82#8, 0xf6#8, 0xc8#8,
      .br bop.BEQ true, 13, 15, 0x1c84#13, 0#21, 0#12⟩ ;;
  [(0x800048ec#64, 0x02083783#32),
   (0x800048f0#64, 0x00016e97#32),
   (0x800048f4#64, 0x430e8e93#32)]
  terminator ⟨0x800048f8#64, 0x2fd78863#32, 0x63#8, 0x88#8, 0xd7#8, 0x2f#8,
      .br bop.BEQ true, 15, 29, 0x2f0#13, 0#21, 0#12⟩ ;;
  [(0x80004be8#64, 0x00883583#32)]
  terminator ⟨0x80004bec#64, 0xd7dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xd7#8,
      .j, 0, 0, 0#13, 0x1ffd7c#21, 0#12⟩ ;;
  [(0x80004968#64, 0x4028d79b#32),
   (0x8000496c#64, 0x00100513#32),
   (0x80004970#64, 0x00f51533#32)]
  terminator ⟨0x80004974#64, 0x0aa5ec63#32, 0x63#8, 0xec#8, 0xa5#8, 0x0a#8,
      .br bop.BLTU true, 11, 10, 0x0b8#13, 0#21, 0#12⟩

#derive_case segSplit chain
  [(0x80004a2c#64, 0x01083783#32),
   (0x80004a30#64, 0x0087b603#32),
   (0x80004a34#64, 0xffc67313#32),
   (0x80004a38#64, 0x40e306b3#32)]
  terminator ⟨0x80004a3c#64, 0x00e36663#32, 0x63#8, 0x66#8, 0xe3#8, 0x00#8,
      .br bop.BLTU false, 6, 14, 0x00c#13, 0#21, 0#12⟩ ;;
  [(0x80004a40#64, 0x0206a613#32)]
  terminator ⟨0x80004a44#64, 0x1a060663#32, 0x63#8, 0x06#8, 0x06#8, 0x1a#8,
      .br bop.BEQ true, 12, 0, 0x1ac#13, 0#21, 0#12⟩ ;;
  [(0x80004bf0#64, 0x00176613#32),
   (0x80004bf4#64, 0x00c7b423#32),
   (0x80004bf8#64, 0x00e78733#32),
   (0x80004bfc#64, 0x00f13423#32),
   (0x80004c00#64, 0x0016e693#32),
   (0x80004c04#64, 0x00e83823#32),
   (0x80004c08#64, 0x00040513#32),
   (0x80004c0c#64, 0x00d73423#32)]

end Vsa.Sim

namespace VsaIris.MallocFast

open Vsa.Sim

/-! ## Memory-fact and comparison helpers -/

theorem ea_of {L : GRegs} {a : MInstr} (base : BitVec 64) (off : Nat)
    (hsrc : srcVal a.rs1 L = base) (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off)
    (hno : base.toNat + off < 2 ^ 64) : (eaddrM a L).toNat = base.toNat + off := by
  unfold eaddrM; rw [hsrc, BitVec.toNat_add, himm, Nat.mod_eq_of_lt hno]

theorem ldFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (hk : a.kind = .ld) (ea : Nat) (hea : (eaddrM a L).toNat = ea)
    (hlo : 0x80000000 ≤ ea) (hhi : ea + 8 ≤ 0x100000000)
    (hw : ea + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea) (hp : LPins8 m ea bs) : MemFacts m L bs a := by
  unfold MemFacts; rw [hk]; rw [hea]; exact ⟨⟨hlo, hhi, hw⟩, hp⟩

theorem sdFact {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    (hk : a.kind = .sd) (ea : Nat) (hea : (eaddrM a L).toNat = ea)
    (hlo : 0x80000000 ≤ ea) (hhi : ea + 8 ≤ 0x100000000)
    (hw : tohostAddr + 16 ≤ ea) (hal : ea % 8 = 0) : MemFacts m L bs a := by
  unfold MemFacts; rw [hk]; rw [hea]; exact ⟨hlo, hhi, hw, hal⟩

theorem ult_iff (a b : BitVec 64) : zopz0zI_u a b = true ↔ a.toNat < b.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

theorem ult_false_iff (a b : BitVec 64) : zopz0zI_u a b = false ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zI_u; simp [Sail.BitVec.toNatInt]

theorem uge_iff (a b : BitVec 64) : zopz0zKzJ_u a b = true ↔ b.toNat ≤ a.toNat := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt]

theorem uge_false_iff (a b : BitVec 64) : zopz0zKzJ_u a b = false ↔ a.toNat < b.toNat := by
  unfold zopz0zKzJ_u; simp [Sail.BitVec.toNatInt]

/-- `x + imm` for a small non-negative immediate. -/
theorem add_imm (x : BitVec 64) (imm : BitVec 12) (c : Nat)
    (hc : (sign_extend (m := 64) imm : BitVec 64).toNat = c) (hno : x.toNat + c < 2 ^ 64) :
    (x + sign_extend (m := 64) imm).toNat = x.toNat + c := by
  rw [BitVec.toNat_add, hc, Nat.mod_eq_of_lt hno]

/-- `x + imm` for a negative immediate `-d`. -/
theorem sub_imm (x : BitVec 64) (imm : BitVec 12) (d : Nat)
    (hc : (sign_extend (m := 64) imm : BitVec 64).toNat = 2 ^ 64 - d) (hd : d ≤ x.toNat) (hd0 : 0 < d) :
    (x + sign_extend (m := 64) imm).toNat = x.toNat - d := by
  rw [BitVec.toNat_add, hc]
  have := x.isLt
  rw [show x.toNat + (2 ^ 64 - d) = (x.toNat - d) + 2 ^ 64 by omega, Nat.add_mod_right,
    Nat.mod_eq_of_lt (by omega)]

/-- Masking with `-16` rounds down to a multiple of 16. -/
theorem and_m16_toNat (a : BitVec 64) :
    (a &&& sign_extend (m := 64) (0xff0#12)).toNat = a.toNat / 16 * 16 := by
  have hmeq : (sign_extend (m := 64) (0xff0#12) : BitVec 64) = (BitVec.allOnes 64) <<< 4 := by
    decide
  have hshift : (a &&& sign_extend (m := 64) (0xff0#12)) = (a >>> 4) <<< 4 := by
    rw [hmeq]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < 4
    · simp only [hi, decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.and_true,
        Bool.and_self, implies_true]
    · by_cases hlt : i < 64
      · have h3 : 4 + (i - 4) = i := by omega
        have h2 : i - 4 < 64 := by omega
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt, decide_true,
          h2, Bool.and_true, h3, Bool.and_self, implies_true]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt,
          Bool.false_and, Bool.and_false, hge, Bool.and_self, implies_true]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  rw [Nat.shiftRight_eq_div_pow]
  have hb : a.toNat / 16 < 2 ^ 60 := by omega
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

/-! ## `segWrap` -/

/-- The `_impure_ptr` word. -/
def impW : List (BitVec 8) := [0x38#8, 0xb5#8, 0x01#8, 0x80#8, 0x00#8, 0x00#8, 0x00#8, 0x00#8]

/-- `__global_pointer$`. -/
abbrev gpV : BitVec 64 := 0x8001b510#64

abbrev wrapL (n a1 : BitVec 64) : GRegs := [(10, n), (11, a1), (3, gpV)]

theorem wrap_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m) (n a1 : BitVec 64) :
    ChainFacts m m (wrapL n a1) [impW] segWrap := by
  unfold segWrap ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  refine ldFact rfl 0x8001b970 ((ea_of gpV 1120 rfl (by decide) (by decide)).trans (by decide))
    (by decide) (by decide) (by decide) ?_
  change LPins8 m 0x8001b970 impW
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := path_impure hcode
  simp only [LPins8, impW, List.getD_cons_zero, List.getD_cons_succ, h0, h1, h2, h3, h4, h5, h6, h7,
    Option.getD_some]
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## `segPro` -/

/-- The caller's stack pointer: 96 bytes of frame above the HTIF window, in
32-bit RAM, 16-aligned. -/
structure SpGeom (s : BitVec 64) : Prop where
  lo : tohostAddr + 16 + 96 ≤ s.toNat
  hi : s.toNat ≤ 0x100000000
  align : s.toNat % 16 = 0

theorem sp96 {s : BitVec 64} (h : SpGeom s) :
    (s + sign_extend (m := 64) (0xfa0#12)).toNat = s.toNat - 96 := by
  have := h.lo; unfold tohostAddr at this
  exact sub_imm s _ 96 (by decide) (by omega) (by decide)

/-- `nb = (n + 23) & -16`. -/
abbrev nbOf (n : BitVec 64) : BitVec 64 := n + sign_extend (m := 64) (0x017#12) &&& sign_extend (m := 64) (0xff0#12)

theorem nbOf_toNat {n : BitVec 64} (hn : n.toNat ≤ 487) : (nbOf n).toNat = (n.toNat + 23) / 16 * 16 := by
  unfold nbOf
  rw [and_m16_toNat, add_imm n _ 23 (by decide) (by omega)]

abbrev proL (s s0 r n a0 a4 a5 : BitVec 64) : GRegs :=
  [(2, s), (8, s0), (1, r), (11, n), (10, a0), (14, a4), (15, a5)]

theorem stackStore {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    {s : BitVec 64} (h : SpGeom s) (off : Nat) (hk : a.kind = .sd)
    (hsrc : srcVal a.rs1 L = s + sign_extend (m := 64) (0xfa0#12))
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off) (hoff : off + 8 ≤ 96)
    (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  have h96 := sp96 h
  have hlo := h.lo; have hhi := h.hi; have hal := h.align
  unfold tohostAddr at hlo
  refine sdFact hk _ (ea_of _ off hsrc himm (by rw [h96]; omega)) ?_ ?_ ?_ ?_ <;>
    rw [h96] <;> first | omega | (unfold tohostAddr; omega)

theorem pro_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m)
    {s s0 r n a0 a4 a5 : BitVec 64} (hs : SpGeom s) (hn : 24 ≤ n.toNat) (hn' : n.toNat ≤ 487) :
    ChainFacts m m (proL s s0 r n a0 a4 a5) [] segPro := by
  have hnb := nbOf_toNat hn'
  unfold segPro ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  · exact stackStore hs 80 rfl rfl (by decide) (by decide) (by decide)
  · exact stackStore hs 88 rfl rfl (by decide) (by decide) (by decide)
  · rw [ult_iff, add_imm n _ 23 (by decide) (by omega)]
    rw [show (0#64 + sign_extend (m := 64) (46#12) : BitVec 64).toNat = 46 by decide]
    omega
  · rw [uge_false_iff]
    change (nbOf n).toNat < _
    refine Nat.lt_of_lt_of_le ?_ (show 2 ^ 31 ≤ _ by decide)
    rw [hnb]; omega
  · rw [ult_false_iff]
    change n.toNat ≤ (nbOf n).toNat
    rw [hnb]; omega
  · exact stackStore hs 8 rfl rfl (by decide) (by decide) (by decide)

/-! ## The lock hooks -/

theorem lock_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m) (a0 : BitVec 64) :
    ChainFacts m m [(10, a0), (3, gpV)] [] segLock := by
  unfold segLock ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"

theorem unlock_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m) (a0 : BitVec 64) :
    ChainFacts m m [(10, a0), (3, gpV)] [] segUnlock := by
  unfold segUnlock ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"

theorem ret_facts_acq {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m) (ra : BitVec 64)
    (hra : ra.toNat % 4 = 0) : ChainFacts m m [(1, ra)] [] segAcq := by
  unfold segAcq ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  rw [ret_tgt ra hra]; exact hra

theorem ret_facts_rel {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m) (ra : BitVec 64)
    (hra : ra.toNat % 4 = 0) : ChainFacts m m [(1, ra)] [] segRel := by
  unfold segRel ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  rw [ret_tgt ra hra]; exact hra

/-! ## Loads from the owned image -/

/-- The 8 image bytes at `a`, as a load's byte list. -/
def wordOf (f : Nat → BitVec 8) (a : Nat) : List (BitVec 8) :=
  [f a, f (a + 1), f (a + 2), f (a + 3), f (a + 4), f (a + 5), f (a + 6), f (a + 7)]

theorem lpins_of_img {m : Std.ExtHashMap Nat (BitVec 8)} {f : Nat → BitVec 8} {a : Nat}
    (h : ∀ k, k < 8 → (m[a + k]?).getD 0 = f (a + k)) : LPins8 m a (wordOf f a) := by
  simp only [LPins8, wordOf, List.getD_cons_zero, List.getD_cons_succ]
  exact ⟨by simpa using h 0 (by omega), h 1 (by omega), h 2 (by omega), h 3 (by omega),
    h 4 (by omega), h 5 (by omega), h 6 (by omega), h 7 (by omega)⟩

/-- A load's value from any memory holding the image where it reads. -/
theorem wordOf_value {f : Nat → BitVec 8} {a : Nat} {m : Std.ExtHashMap Nat (BitVec 8)} {v : BitVec 64}
    (him : ∀ k, k < 8 → m[a + k]? = some (f (a + k))) (hr : Vsa.MemRepr.read64 m a = some v.toNat) :
    bytesVal .ld (wordOf f a) = v := by
  have := execRetEpilogueWord_value m a v hr
  have e : execRetEpilogueWord m a = wordOf f a := by
    simp only [execRetEpilogueWord, wordOf]
    rw [show m[a]? = some (f a) by simpa using him 0 (by omega), him 1 (by omega), him 2 (by omega),
      him 3 (by omega), him 4 (by omega), him 5 (by omega), him 6 (by omega), him 7 (by omega)]
    rfl
  rwa [e] at this

/-- A load from the stack frame `[sp, sp + 96)`. -/
theorem frameLoad {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {f : Nat → BitVec 8}
    {sp : BitVec 64} (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (off : Nat) (hk : a.kind = .ld) (hsrc : srcVal a.rs1 L = sp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off) (hoff : off + 8 ≤ 96)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k)) :
    MemFacts m L (wordOf f (sp.toNat + off)) a := by
  unfold tohostAddr at hsp
  refine ldFact hk _ (ea_of sp off hsrc himm (by omega)) (by omega) (by omega)
    (by unfold tohostAddr; omega) (lpins_of_img fun k hk => ?_)
  rw [Nat.add_assoc]; exact hpin (off + k) (by omega)

/-! ## `segEpi` -/

abbrev epiL (sp a5 a0 ra s0 : BitVec 64) : GRegs := [(2, sp), (15, a5), (10, a0), (1, ra), (8, s0)]

abbrev epiLds (f : Nat → BitVec 8) (sp : BitVec 64) : List (List (BitVec 8)) :=
  [wordOf f (sp.toNat + 8), wordOf f (sp.toNat + 88), wordOf f (sp.toNat + 80)]

theorem epi_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m) {sp a5 a0 ra s0 r : BitVec 64}
    {f : Nat → BitVec 8} (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hr : bytesVal .ld (wordOf f (sp.toNat + 88)) = r) (hral : r.toNat % 4 = 0) :
    ChainFacts m m (epiL sp a5 a0 ra s0) (epiLds f sp) segEpi := by
  unfold segEpi ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  · exact frameLoad hsp hsp' 8 rfl rfl (by decide) (by decide) hpin
  · exact frameLoad (m := m) hsp hsp' 88 rfl rfl (by decide) (by decide) hpin
  · exact frameLoad (m := m) hsp hsp' 80 rfl rfl (by decide) (by decide) hpin
  · change (Sail.BitVec.update (bytesVal .ld (wordOf f (sp.toNat + 88)) + sign_extend (m := 64) (0#12))
      0 0#1).toNat % 4 = 0
    rw [hr, ret_tgt r hral]; exact hral

/-! ## `segBins` -/

abbrev binsL (sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64) : GRegs :=
  [(2, sp), (10, a0), (11, a1), (12, a2), (13, a3), (14, a4), (15, a5), (16, a6), (17, a7), (29, t4)]

/-- The loads of `segBins`: the saved `nb`, the two bins' `bk` words, the unsorted
bin's `fd` word, and `binblocks`. -/
abbrev binsLds (f : Nat → BitVec 8) (sp : BitVec 64) (nb : Nat) : List (List (BitVec 8)) :=
  [wordOf f (sp.toNat + 8), wordOf f (Vsa.Sim.DlHeap.binAt (nb / 8) + 24),
   wordOf f (Vsa.Sim.DlHeap.binAt (nb / 8 + 1) + 24), wordOf f (Vsa.Sim.DlHeap.binAt 1 + 16),
   wordOf f Vsa.Sim.DlHeap.binblocksAddr]

/-- The chunk sizes of requests `24..487`. -/
def sizeClasses : List Nat := (List.range 30).map (fun j => 32 + 16 * j)

theorem mem_sizeClasses {nb : Nat} (h16 : nb % 16 = 0) (h1 : 32 ≤ nb) (h2 : nb ≤ 496) :
    nb ∈ sizeClasses := by
  unfold sizeClasses
  exact List.mem_map.2 ⟨(nb - 32) / 16, List.mem_range.2 (by omega), by omega⟩

/-- The empty-bin facts `segBins` reads, over the image. -/
structure BinsImg (f : Nat → BitVec 8) : Prop where
  bk : ∀ i, 0 < i → i < 128 → bytesVal .ld (wordOf f (Vsa.Sim.DlHeap.binAt i + 24)) =
    BitVec.ofNat 64 (Vsa.Sim.DlHeap.binAt i)
  fd1 : bytesVal .ld (wordOf f (Vsa.Sim.DlHeap.binAt 1 + 16)) =
    BitVec.ofNat 64 (Vsa.Sim.DlHeap.binAt 1)
  binblocks : bytesVal .ld (wordOf f Vsa.Sim.DlHeap.binblocksAddr) = 0#64

set_option hygiene false in
/-- `segBins`' leftovers for one concrete chunk size `c`. -/
macro "bins_case " c:term : tactic => `(tactic| (
  unfold segBins ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  all_goals (try simp only [binsLds, List.tail_cons])
  · exact frameLoad hsp hsp' 8 rfl rfl (by decide) (by decide) hpin
  · simp only [hv1]; decide
  · refine ldFact rfl (Vsa.Sim.DlHeap.binAt ($c / 8) + 24)
      (by unfold eaddrM; seg_norm; simp only [binsLds, hv1]; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hv1, hb.bk ($c / 8) (by decide) (by decide)]; decide
  · refine ldFact rfl (Vsa.Sim.DlHeap.binAt ($c / 8 + 1) + 24)
      (by unfold eaddrM; seg_norm; simp only [binsLds, hv1]; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hv1, hb.bk ($c / 8 + 1) (by decide) (by decide)]; decide
  · refine ldFact rfl (Vsa.Sim.DlHeap.binAt 1 + 16)
      (by unfold eaddrM; seg_norm; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binAt Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hb.fd1]; decide
  · refine ldFact rfl Vsa.Sim.DlHeap.binblocksAddr
      (by unfold eaddrM; seg_norm; decide) (by decide) (by decide)
      (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.binblocksAddr Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.binblocksAddr Vsa.Sim.DlHeap.avAddr; omega))
  · simp only [hv1, hb.binblocks]; decide))

section BinsCases

variable {m : Std.ExtHashMap Nat (BitVec 8)} {sp a0 a1 a2 a3 a4 a5 a6 a7 t4 : BitVec 64}
  {f : Nat → BitVec 8}

theorem bins_facts_32 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 32) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 32) segBins := by
  bins_case 32

theorem bins_facts_48 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 48) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 48) segBins := by
  bins_case 48

theorem bins_facts_64 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 64) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 64) segBins := by
  bins_case 64

theorem bins_facts_80 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 80) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 80) segBins := by
  bins_case 80

theorem bins_facts_96 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 96) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 96) segBins := by
  bins_case 96

theorem bins_facts_112 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 112) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 112) segBins := by
  bins_case 112

theorem bins_facts_128 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 128) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 128) segBins := by
  bins_case 128

theorem bins_facts_144 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 144) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 144) segBins := by
  bins_case 144

theorem bins_facts_160 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 160) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 160) segBins := by
  bins_case 160

theorem bins_facts_176 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 176) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 176) segBins := by
  bins_case 176

theorem bins_facts_192 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 192) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 192) segBins := by
  bins_case 192

theorem bins_facts_208 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 208) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 208) segBins := by
  bins_case 208

theorem bins_facts_224 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 224) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 224) segBins := by
  bins_case 224

theorem bins_facts_240 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 240) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 240) segBins := by
  bins_case 240

theorem bins_facts_256 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 256) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 256) segBins := by
  bins_case 256

theorem bins_facts_272 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 272) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 272) segBins := by
  bins_case 272

theorem bins_facts_288 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 288) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 288) segBins := by
  bins_case 288

theorem bins_facts_304 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 304) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 304) segBins := by
  bins_case 304

theorem bins_facts_320 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 320) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 320) segBins := by
  bins_case 320

theorem bins_facts_336 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 336) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 336) segBins := by
  bins_case 336

theorem bins_facts_352 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 352) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 352) segBins := by
  bins_case 352

theorem bins_facts_368 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 368) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 368) segBins := by
  bins_case 368

theorem bins_facts_384 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 384) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 384) segBins := by
  bins_case 384

theorem bins_facts_400 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 400) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 400) segBins := by
  bins_case 400

theorem bins_facts_416 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 416) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 416) segBins := by
  bins_case 416

theorem bins_facts_432 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 432) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 432) segBins := by
  bins_case 432

theorem bins_facts_448 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 448) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 448) segBins := by
  bins_case 448

theorem bins_facts_464 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 464) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 464) segBins := by
  bins_case 464

theorem bins_facts_480 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 480) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 480) segBins := by
  bins_case 480

theorem bins_facts_496 (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 496) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp 496) segBins := by
  bins_case 496

/-- `segBins` for every chunk size of the fast path, one class per theorem. -/
theorem bins_facts (hcode : PathLoaded m)
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hpin : ∀ k, k < 96 → (m[sp.toNat + k]?).getD 0 = f (sp.toNat + k))
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a) {nb : Nat} (hcls : nb ∈ sizeClasses)
    (hv1 : bytesVal .ld (wordOf f (sp.toNat + 8)) = BitVec.ofNat 64 nb) (hb : BinsImg f) :
    ChainFacts m m (binsL sp a0 a1 a2 a3 a4 a5 a6 a7 t4) (binsLds f sp nb) segBins := by
  simp only [sizeClasses, List.mem_map, List.mem_range] at hcls
  obtain ⟨j, hj, rfl⟩ := hcls
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨
    j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨
    j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact bins_facts_32 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_48 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_64 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_80 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_96 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_112 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_128 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_144 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_160 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_176 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_192 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_208 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_224 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_240 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_256 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_272 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_288 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_304 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_320 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_336 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_352 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_368 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_384 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_400 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_416 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_432 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_448 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_464 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_480 hcode hsp hsp' hpin hglob hv1 hb
  · exact bins_facts_496 hcode hsp hsp' hpin hglob hv1 hb

end BinsCases

/-! ## `segSplit` -/

/-- Masking with `-4` clears the two low bits. -/
theorem and_m4_toNat (a : BitVec 64) :
    (a &&& sign_extend (m := 64) (0xffc#12)).toNat = a.toNat / 4 * 4 := by
  have hmeq : (sign_extend (m := 64) (0xffc#12) : BitVec 64) = (BitVec.allOnes 64) <<< 2 := by
    decide
  have hshift : (a &&& sign_extend (m := 64) (0xffc#12)) = (a >>> 2) <<< 2 := by
    rw [hmeq]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < 2
    · simp only [hi, decide_true, Bool.not_true, Bool.false_and, Bool.and_false, implies_true]
    · by_cases hlt : i < 64
      · have h3 : 2 + (i - 2) = i := by omega
        have h2 : i - 2 < 64 := by omega
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt, decide_true,
          h2, Bool.and_true, h3, Bool.and_self, implies_true]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp only [hi, decide_false, Bool.not_false, hlt, Bool.false_and, hge, Bool.and_self,
          implies_true]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  rw [Nat.shiftRight_eq_div_pow]
  have hb : a.toNat / 4 < 2 ^ 62 := by omega
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

/-- `slti x, 32` is false for a non-negative `x ≥ 32`. -/
theorem slt32_false (x : BitVec 64) (h1 : 32 ≤ x.toNat) (h2 : x.toNat < 2 ^ 63) :
    zopz0zI_s x (sign_extend (m := 64) (32#12)) = false := by
  unfold zopz0zI_s
  rw [BitVec.toInt_eq_toNat_of_lt (by omega),
    show (sign_extend (m := 64) (32#12) : BitVec 64).toInt = 32 by decide]
  simp; omega

/-- A store into the stack frame `[sp, sp + 96)`. -/
theorem frameStore {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {a : MInstr} {bs : List (BitVec 8)}
    {sp : BitVec 64} (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000)
    (hal : sp.toNat % 8 = 0) (off : Nat) (hk : a.kind = .sd) (hsrc : srcVal a.rs1 L = sp)
    (himm : (sign_extend (m := 64) a.imm : BitVec 64).toNat = off) (hoff : off + 8 ≤ 96)
    (hoff8 : off % 8 = 0) : MemFacts m L bs a := by
  unfold tohostAddr at hsp
  exact sdFact hk _ (ea_of sp off hsrc himm (by omega)) (by omega) (by omega)
    (by unfold tohostAddr; omega) (by omega)

abbrev splitL (sp a0 s0 a2 a3 a5 t1 : BitVec 64) (nb : Nat) : GRegs :=
  [(2, sp), (10, a0), (8, s0), (12, a2), (13, a3), (14, BitVec.ofNat 64 nb), (15, a5),
   (16, 0x8001ad10#64), (6, t1)]

/-- The loads of `segSplit`: `av->top` and the top chunk's header. -/
abbrev splitLds (f : Nat → BitVec 8) (top : Nat) : List (List (BitVec 8)) :=
  [wordOf f Vsa.Sim.DlHeap.topAddr, wordOf f (top + 8)]

/-- The top chunk `segSplit` splits, named. -/
structure SplitTop (f : Nat → BitVec 8) (top size nb : Nat) : Prop where
  top_ptr : bytesVal .ld (wordOf f Vsa.Sim.DlHeap.topAddr) = BitVec.ofNat 64 top
  header : bytesVal .ld (wordOf f (top + 8)) = BitVec.ofNat 64 (size + 1)
  top_lo : Vsa.Sim.DlHeap.heapStart ≤ top
  top_hi : top + size ≤ Vsa.Sim.DlHeap.heapEnd
  top_align : top % 16 = 0
  size_align : size % 16 = 0
  room : nb + 32 ≤ size
  nb16 : nb % 16 = 0
  nb32 : 32 ≤ nb

theorem split_facts {m : Std.ExtHashMap Nat (BitVec 8)} (hcode : PathLoaded m)
    {sp a0 s0 a2 a3 a5 t1 : BitVec 64} {f : Nat → BitVec 8} {nb top size : Nat}
    (hsp : tohostAddr + 16 ≤ sp.toNat) (hsp' : sp.toNat + 96 ≤ 0x100000000) (hspal : sp.toNat % 8 = 0)
    (hglob : ∀ a, 0x8001ad10 ≤ a → a < 0x8001b520 → (m[a]?).getD 0 = f a)
    (hhdr : ∀ k, k < 8 → (m[top + 8 + k]?).getD 0 = f (top + 8 + k))
    (ht : SplitTop f top size nb) :
    ChainFacts m m (splitL sp a0 s0 a2 a3 a5 t1 nb) (splitLds f top) segSplit := by
  have hlo := ht.top_lo; have hhi := ht.top_hi; have hroom := ht.room
  unfold Vsa.Sim.DlHeap.heapStart at hlo; unfold Vsa.Sim.DlHeap.heapEnd at hhi
  have htop : (BitVec.ofNat 64 top).toNat = top := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hnbv : (BitVec.ofNat 64 nb).toNat = nb := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hszv : (BitVec.ofNat 64 (size + 1)).toNat = size + 1 := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hmask : (BitVec.ofNat 64 (size + 1) &&& sign_extend (m := 64) (0xffc#12)).toNat = size := by
    rw [and_m4_toNat, hszv]; have := ht.size_align; omega
  have htn : (BitVec.ofNat 64 top + BitVec.ofNat 64 nb).toNat = top + nb := by
    rw [BitVec.toNat_add, htop, hnbv, Nat.mod_eq_of_lt (by omega)]
  unfold segSplit ChainFacts
  chain_facts hcode with "VsaIris.MallocFast.path_at_"
  all_goals seg_norm
  all_goals (try simp only [splitLds, List.tail_cons])
  · refine ldFact rfl Vsa.Sim.DlHeap.topAddr (by unfold eaddrM; seg_norm; decide) (by decide)
      (by decide) (by decide) (lpins_of_img fun k hk => hglob _
        (by unfold Vsa.Sim.DlHeap.topAddr Vsa.Sim.DlHeap.avAddr; omega)
        (by unfold Vsa.Sim.DlHeap.topAddr Vsa.Sim.DlHeap.avAddr; omega))
  · refine ldFact rfl (top + 8) ((ea_of (BitVec.ofNat 64 top) 8
      (by seg_norm; rw [ht.top_ptr]) (by decide) (by omega)).trans (by rw [htop]))
      (by omega) (by omega) (by unfold tohostAddr; omega) (lpins_of_img hhdr)
  · rw [ht.header, ult_false_iff, hmask, hnbv]; omega
  · rw [ht.header, slt32_false _ (by rw [BitVec.toNat_sub, hmask, hnbv]; omega)
      (by rw [BitVec.toNat_sub, hmask, hnbv]; omega)]
    decide
  · refine sdFact rfl (top + 8) ((ea_of (BitVec.ofNat 64 top) 8
      (by seg_norm; rw [ht.top_ptr]) (by decide) (by omega)).trans (by rw [htop]))
      (by omega) (by omega) (by unfold tohostAddr; omega) (by have := ht.top_align; omega)
  · exact frameStore hsp hsp' hspal 8 rfl rfl (by decide) (by decide) (by decide)
  · refine sdFact rfl Vsa.Sim.DlHeap.topAddr (by unfold eaddrM; seg_norm; decide) (by decide)
      (by decide) (by decide) (by decide)
  · refine sdFact rfl (top + nb + 8) ((ea_of (BitVec.ofNat 64 top + BitVec.ofNat 64 nb) 8
      (by seg_norm; rw [ht.top_ptr]) (by decide) (by omega)).trans (by rw [htn]))
      (by omega) (by omega) (by unfold tohostAddr; omega)
      (by have := ht.top_align; have := ht.nb16; omega)

end VsaIris.MallocFast
