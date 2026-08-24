import Vsa.Sim.MemLoad
import Vsa.Sim.ExecuteAlu

/-!
# M2 — `execute_LOAD` characterization on the M-mode / Bare / naturally-aligned hot path

The execute-clause analogue of the data-read chain in `Vsa/Sim/MemLoad.lean`.
`execute_LOAD imm rs1 rd is_unsigned width` (`InstsEnd.lean:6779`) computes
`offset = sign_extend imm`, asserts `width ≤ xlen_bytes`, then

    match ← vmem_read rs1 offset width (Load Data) false false false with
    | .Ok data => wX_bits rd (extend_value is_unsigned data); pure RETIRE_SUCCESS
    | .Err e   => pure e

`vmem_read` resolves the effective address via `get_transformed_data_addr`
(`ext_data_get_addr` reads `rX_bits rs1`, adds the offset; then
`transform_effective_address`), then `vmem_read_addr`, which — after an alignment
check and a `split_on_page_boundary`/`do_split_access` computation that on the
Bare path is a no-op — calls `translate_and_read_value` (MemLoad's top lemmas
`translate_and_read_value_data_{eight,four,two,one}`) and reassembles the bytes
with a full-width `updateSubrange` over a zero seed.

On the hot path all of the intermediate control-plane reads (`mstatus`,
`cur_privilege`, `mseccfg`) collapse:

* `effectivePrivilege (Load Data) mstatus Machine = Machine` (MPRV = 0);
* `get_pmlen (Load Data) Machine = 0` (`mseccfg.PMM = 0 ⇒ PMM_Disabled`), so
  `pm_transform_PA vaddr 0` is the identity `zero_extend (extractLsb a 63 0) = a`;
* `translationMode Machine = Bare`, so `do_split_access = false` — the
  page-split reads are skipped regardless of `split_on_page_boundary`'s value.

Every link is read-only up to the final `wX_bits rd` write, whose target state
`σ'` the caller supplies (a real insert, or `σ` for the `x0` no-op), exactly as
in `Vsa/Sim/ExecuteAlu.lean`.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `get_pmlen (Load Data) Machine = 0` on the M-mode hot path. -/

/-- `get_pmlen (Load Data) Machine = 0`. `is_pmm_applicable` is `true` for a data
access (`bne (Load Data) (InstructionFetch/PTE) = true`, `Machine == Machine`,
`xlen = 64`), reading `mstatus` (the `MXR` disjunct is short-circuited by the
`Machine ==` disjunct but the read is still forced). `get_pmm Machine` reads
`mseccfg`; with `mseccfg.PMM = 0` (`_get_Seccfg_PMM 0 = 0`) the mode is
`PMM_Disabled ⇒ pmlen 0`. -/
theorem get_pmlen_data_machine
    (σ : SequentialState RegisterType trivialChoiceSource)
    (vmstatus : RegisterType Register.mstatus)
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg)) :
    (get_pmlen (MemoryAccessType.Load mem_payload.Data) Privilege.Machine).run σ
      = .ok 0 σ := by
  have h1 : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by decide
  have h2 : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.Load mem_payload.PageTableEntry : MemoryAccessType mem_payload)) = false := by decide
  have h3 : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.Store mem_payload.PageTableEntry : MemoryAccessType mem_payload)) = false := by decide
  have hpmm : pmm_mode_backwards (_get_Seccfg_PMM 0#64) = PointerMaskingMode.PMM_Disabled := rfl
  have hcond : ((Privilege.Machine == Privilege.Machine) || _get_Mstatus_MXR vmstatus == 0#1) = true := by
    rw [show (Privilege.Machine == Privilege.Machine) = true from by decide, Bool.true_or]
  have hxl : (Functions.xlen == 64) = true := by decide
  simp only [get_pmlen, is_pmm_applicable, get_pmm, bne, h1, h2, h3,
    Bool.not_false, Bool.true_and, Bool.and_true, hcond, hxl,
    bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hmseccfg, hpmm, if_true]

/-! ## `transform_effective_address (Virtaddr a) (Load Data)` is the identity. -/

/-- `transform_effective_address (Virtaddr a) (Load Data) = Virtaddr a` on the
Machine/Bare/pmlen-0 hot path. `effectivePrivilege = Machine` (MPRV = 0);
`get_pmlen = 0`; `translationMode Machine = Bare ⇒ pm_transform_PA a 0`, whose
`zero_extend (extractLsb a 63 0) = a`. -/
theorem transform_effective_address_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg)) :
    (transform_effective_address (virtaddr.Virtaddr a)
        (MemoryAccessType.Load mem_payload.Data)).run σ
      = .ok (virtaddr.Virtaddr a) σ := by
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  have hpm := get_pmlen_data_machine σ vmstatus hmstatus hmseccfg
  simp only [EStateM.run] at hep hpm
  unfold transform_effective_address
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [EStateM.bind]
  rw [hpm]
  simp only [translationMode, bind, EStateM.bind, EStateM.pure, pure]
  have hb : (Privilege.Machine == Privilege.Machine) = true := by decide
  simp only [hb, if_true]
  have hbb : (SATPMode.Bare == SATPMode.Bare) = true := by decide
  simp only [hbb, if_true, pm_transform_PA, EStateM.pure]
  have haeq : ∀ (n : Nat), n = 63 →
      (zero_extend (m := 64) (Sail.BitVec.extractLsb a n 0) : BitVec 64) = a := by
    rintro n rfl
    apply BitVec.eq_of_toNat_eq
    have hlt : a.toNat < 2 ^ 64 := a.isLt
    simp only [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb',
      Nat.shiftRight_zero, BitVec.toNat_ofNat]
    omega
  rw [haeq _ (by decide)]

/-! ## `get_transformed_data_addr rs offset (Load Data) width` on the hot path.

`ext_data_get_addr` reads `rX_bits rs` (hypothesis `hrs`), adds `offset`, and
wraps in `Ext_DataAddr_OK`; `transform_effective_address` is the identity
(`transform_effective_address_data`). Width-generic (the width argument is
`_width`, unused by `ext_data_get_addr`). -/
theorem get_transformed_data_addr_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset : BitVec 64) (v1 : BitVec 64) (width : Nat)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hrs : (rX_bits rs).run σ = .ok v1 σ) :
    (get_transformed_data_addr rs offset (MemoryAccessType.Load mem_payload.Data) width).run σ
      = .ok (Ext_DataAddr_Check.Ext_DataAddr_OK (virtaddr.Virtaddr (v1 + offset))) σ := by
  have htf := transform_effective_address_data σ (v1 + offset) vmstatus hpriv hmstatus hmprv hmseccfg
  simp only [EStateM.run] at hrs htf
  unfold get_transformed_data_addr ext_data_get_addr
  simp only [bind, EStateM.bind, EStateM.run, pure, EStateM.pure]
  rw [hrs]
  simp only [EStateM.bind, EStateM.pure]
  rw [htf]

/-! ## `split_on_page_boundary a width = (width, 0)` for an aligned in-page access.

For a `width`-aligned address (`width ∈ {1,2,4,8}`) the `[a, a+width)` window never
crosses a 4096-byte page boundary, so `intra_page_access` holds and the split is
`(width, 0)`. Proved per width (the `page_mask &&&` equality is `bv_omega` over the
concrete `width`). Only the *fact that it runs* matters downstream — its value
feeds `next_page_bytes`, which the Bare-path `do_split_access` ignores. -/
/-- Anding a 64-bit value with the page mask `0xF…F000` clears the low 12 bits:
`(x &&& page_mask).toNat = x.toNat / 4096 * 4096`. The bit-level bridge under the
`intra_page_access` comparison — proved once via `getLsbD` (`page_mask =
allOnes <<< 12`) and reused across widths. -/
theorem and_page_mask_toNat (a : BitVec 64) :
    (a &&& 0xFFFFFFFFFFFFF000#64).toNat = a.toNat / 4096 * 4096 := by
  have hmeq : (0xFFFFFFFFFFFFF000#64 : BitVec 64) = (BitVec.allOnes 64) <<< 12 := by decide
  have hshift : (a &&& 0xFFFFFFFFFFFFF000#64) = (a >>> 12) <<< 12 := by
    rw [hmeq]
    apply BitVec.eq_of_getLsbD_eq
    intro i
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_allOnes]
    by_cases hi : i < 12
    · simp only [hi, decide_true, Bool.not_true, Bool.false_and, Bool.and_false, Bool.and_true,
        Bool.and_self, implies_true]
    · by_cases hlt : i < 64
      · have h3 : 12 + (i - 12) = i := by omega
        have h2 : i - 12 < 64 := by omega
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt, decide_true,
          h2, Bool.and_true, h3, Bool.and_self, implies_true]
      · have hge : a.getLsbD i = false := BitVec.getLsbD_of_ge a i (by omega)
        simp only [hi, decide_false, Bool.not_false, Bool.true_and, hlt,
          Bool.false_and, Bool.and_false, hge, Bool.and_self, implies_true]
  rw [hshift, BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight]
  have ha : a.toNat < 2 ^ 64 := a.isLt
  rw [Nat.shiftRight_eq_div_pow]
  have hb : a.toNat / 4096 < 2 ^ 52 := by omega
  rw [Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]

/-- `split_on_page_boundary a w = (w, 0)` for a `w`-aligned address with `w ≤ 8`.
Width-generic. The `intra_page_access` comparison reduces (via `and_page_mask_toNat`)
to `a/4096 = (a+w-1)/4096`, which holds because a `w`-aligned window of ≤ 8 bytes
cannot cross a 4096-byte page. Only the *fact that it runs* matters downstream: its
value feeds `next_page_bytes`, which the Bare-path `do_split_access` ignores. -/
theorem split_on_page_boundary_data_w
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) (w : Nat)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096) :
    (split_on_page_boundary a w).run σ = .ok ((w : Int), 0) σ := by
  have hmask : (Sail.BitVec.updateSubrange ((ones (n := 64)) : BitVec 64)
      (Functions.pagesize_bits -i 1) 0 (zeros (n := ((12 -i 1) -i (0 -i 1))))) = 0xFFFFFFFFFFFFF000#64 := by
    apply BitVec.eq_of_toNat_eq; decide
  simp only [split_on_page_boundary, Sail.BitVec.length, hmask]
  have hai : BitVec.addInt a ((w : Nat) : Int) = a + BitVec.ofNat 64 w := by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.addInt]; rfl
  have hsi : BitVec.subInt (a + BitVec.ofNat 64 w) 1 = a + BitVec.ofNat 64 (w - 1) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.subInt, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.toNat_sub]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    have : (BitVec.ofInt 64 1).toNat = 1 := by decide
    omega
  have hintra : ((a &&& 0xFFFFFFFFFFFFF000#64)
      == (BitVec.subInt (BitVec.addInt a ((w : Nat) : Int)) 1 &&& 0xFFFFFFFFFFFFF000#64)) = true := by
    rw [hai, hsi]
    simp only [beq_iff_eq]
    apply BitVec.eq_of_toNat_eq
    rw [and_page_mask_toNat, and_page_mask_toNat]
    have h64 : a.toNat < 2 ^ 64 := a.isLt
    have haw : (a + BitVec.ofNat 64 (w - 1)).toNat = a.toNat + (w - 1) := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [haw, hpage]
  simp only [hintra, if_true, bind, EStateM.bind, EStateM.run, pure, EStateM.pure]

/-- The final `vmem_read_addr` reassembly is the identity on the non-split path:
writing the freshly-read `v` into bits `[0, 8*w)` of a `zeros` seed of width `8*w`
returns `v`. Width-generic; the `updateSubrange'` internals (`mask &&& 0 = 0`,
`0 ||| (v.zeroExtend (8w) <<< 0) = v`) collapse via a `toNat` computation with the
`w ≥ 1` width bound. The `8 *i w`/`(8*i w) -i 1` Int-vs-Nat forms in the model term
are *defeq* to `8*w`/`8*w-1` (`Int.toNat (Int.ofNat (8*w)) = 8*w`), so no width
rewrite is needed — `eq_of_toNat_eq` lands directly on a Nat goal. -/
theorem updateSubrange_zeros_load (w : Nat) (hw : 0 < w) (v : BitVec (8 * w)) :
    Sail.BitVec.updateSubrange (zeros (n := (8 * (↑w : Int)).toNat))
        ((8 * (↑w : Int) - 1).toNat) 0 v = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros,
    BitVec.shiftLeft_zero, BitVec.toNat_or, BitVec.toNat_and, BitVec.toNat_not,
    BitVec.toNat_setWidth, BitVec.toNat_allOnes]
  have hN : (8 * (↑w : Int)).toNat = 8 * w := by omega
  have hM : (8 * (↑w : Int) - 1).toNat - 0 + 1 = 8 * w := by omega
  simp only [hN, hM, BitVec.zero_eq, BitVec.toNat_ofNat, Nat.zero_mod]
  have hvlt : v.toNat < 2 ^ (8 * w) := BitVec.isLt _
  rw [Nat.and_zero, Nat.zero_or, Nat.mod_mod, Nat.mod_eq_of_lt hvlt]
  rfl

/-! ## `vmem_read_addr (Virtaddr a) width (Load Data) …` on the Bare hot path.

Composes: the alignment check (aligned ⇒ the `not is_aligned_vaddr` guard is
false ⇒ no exception), `split_on_page_boundary_data_w` (⇒ `next_page_bytes = 0`),
`effectivePrivilege = Machine` + `translationMode Machine = Bare` (⇒
`do_split_access = false`, so `access_width = width` and both split-read blocks are
skipped), `translate_and_read_value_data_*` (MemLoad), and the final
`updateSubrange (zeros (8*width)) (8*width-1) 0 v = v`. State unchanged.

The width-generic engine `vmem_read_addr_data_w` (below, before the per-width
corollaries) does the real work; `vmem_read_addr_data_eight` is retained as the
original width-8 proof but is *subsumed* by the generic version. -/
theorem vmem_read_addr_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 8 ≤ 0x100000000)
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 8 = 0)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4) (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6) (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (vmem_read_addr (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0)) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 8 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 8)) = Int.ofNat (a.toNat % 8) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (8 : Int) = Int.ofNat 8 from rfl, this, halign]; rfl
  have hpage : (a.toNat + (8 - 1)) / 4096 = a.toNat / 4096 := by omega
  have hsplit := split_on_page_boundary_data_w σ a 8 (by decide) (by decide) hpage
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  have htm := translationMode_machine σ
  have htrv := translate_and_read_value_data_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 vmstatus vpmpaddr
    hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign
    h0 h1 h2 h3 h4 h5 h6 h7
  have halignv : is_aligned_vaddr (virtaddr.Virtaddr a) 8 = true := by
    simp only [is_aligned_vaddr, beq_iff_eq]
    rw [show ((8 : Nat) : Int) = (8 : Int) from rfl] <;> exact htmod
  simp only [EStateM.run] at hsplit hep htm htrv
  unfold vmem_read_addr
  simp only [halignv, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure,
    bits_of_virtaddr, sys_misaligned_order_decreasing,
    Functions.not, Bool.not_true, Bool.false_and, Bool.and_false, if_false, if_true,
    Bool.false_eq_true]
  rw [hsplit]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.pure, liftM, monadLift,
    MonadLift.monadLift, Functor.map, pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [bne, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, htm,
    show (SATPMode.Bare == SATPMode.Bare) = true from by decide,
    Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false,
    gt_iff_lt, sys_misaligned_order_decreasing]
  rw [show (if (Bool.false = Bool.true) then ((8:Nat):Int) else ((8:Nat):Int)) = ((8:Nat):Int) from rfl]
  simp only [Int.toNat_natCast]
  rw [htrv]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map,
    Bool.false_eq_true, if_false]
  exact congrArg (fun x => EStateM.Result.ok (Result.Ok x) σ)
    (updateSubrange_zeros_load 8 (by decide)
      (((((((b7.append b6).append b5).append b4).append b3).append b2).append b1).append b0))

/-- **Width-generic `vmem_read_addr` engine.** For any `w` with `1 ≤ w ≤ 8`, an
aligned in-page (`hpage`) `Load Data` access on the Machine/Bare hot path returns
`Ok v`, where `v` is the value the `translate_and_read_value` leaf equation
(`htrv`) produces, with state unchanged. `halignv` is the alignment fact
(`is_aligned_vaddr (Virtaddr a) w = true`, discharged per width from the modular
alignment side condition). Everything after `split_on_page_boundary_data_w`
(`do_split_access = false`, both split-read blocks skipped, `access_width = w`,
`updateSubrange (zeros …) … 0 v = v`) is width-uniform. -/
theorem vmem_read_addr_data_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (paddr : physaddr) (v : BitVec (8 * w))
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hwpos : 0 < w) (hwle : w ≤ 8)
    (hpage : (a.toNat + (w - 1)) / 4096 = a.toNat / 4096)
    (halignv : is_aligned_vaddr (virtaddr.Virtaddr a) w = true)
    (htrv : (translate_and_read_value (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (paddr, v)) σ) :
    (vmem_read_addr (virtaddr.Virtaddr a) w
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok v) σ := by
  have hsplit := split_on_page_boundary_data_w σ a w hwpos hwle hpage
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  have htm := translationMode_machine σ
  simp only [EStateM.run] at hsplit hep htm htrv
  unfold vmem_read_addr
  simp only [halignv, LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure,
    bits_of_virtaddr, sys_misaligned_order_decreasing,
    Functions.not, Bool.not_true, Bool.false_and, Bool.and_false, if_false, if_true,
    Bool.false_eq_true]
  rw [hsplit]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map,
    bind, ExceptT.bind, ExceptT.mk, ExceptT.lift, ExceptT.pure, liftM, monadLift,
    MonadLift.monadLift, Functor.map, pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [bne, EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, htm,
    show (SATPMode.Bare == SATPMode.Bare) = true from by decide,
    Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, if_false,
    gt_iff_lt, sys_misaligned_order_decreasing]
  rw [show (if (Bool.false = Bool.true) then ((w:Nat):Int) else ((w:Nat):Int)) = ((w:Nat):Int) from rfl]
  simp only [Int.toNat_natCast]
  rw [htrv]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map,
    Bool.false_eq_true, if_false]
  exact congrArg (fun x => EStateM.Result.ok (Result.Ok x) σ)
    (updateSubrange_zeros_load w hwpos v)

/-- `is_aligned_vaddr (Virtaddr a) w = true` from the Nat modular fact
`a.toNat % w = 0`, bridging `Int.tmod (toNatInt a) w` through `Int.ofNat_tmod`
(the width-8 `htmod`/`halignv` step, factored out for the corollaries). -/
theorem is_aligned_vaddr_of_mod (a : BitVec 64) (w : Nat)
    (halign : a.toNat % w = 0) : is_aligned_vaddr (virtaddr.Virtaddr a) w = true := by
  have htmod : Int.tmod (BitVec.toNatInt a) ((w : Nat) : Int) = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat w)) = Int.ofNat (a.toNat % w) :=
      (Int.ofNat_tmod _ _).symm
    rw [show ((w : Nat) : Int) = Int.ofNat w from rfl, this, halign]; rfl
  simp only [is_aligned_vaddr, beq_iff_eq]
  exact htmod

/-! ## Thin per-width `vmem_read_addr` corollaries.

Each supplies the concrete MemLoad leaf (`translate_and_read_value_data_*`) as
`htrv`, discharges alignment (`is_aligned_vaddr_of_mod`) and the page-non-crossing
`hpage` (`omega` from `a.toNat % w = 0`), and instantiates `vmem_read_addr_data_w`.
`vmem_read_addr_data_eight` above is the same statement at width 8 (kept as the
original proof; subsumed by these). -/

/-- `vmem_read_addr (Virtaddr a) 4 (Load Data) …` (`lw`/`lwu`). -/
theorem vmem_read_addr_data_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhtif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 4 = 0)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (vmem_read_addr (virtaddr.Virtaddr a) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (((b3.append b2).append b1).append b0)) σ :=
  vmem_read_addr_data_w σ a 4 (physaddr.Physaddr (zero_extend (m := 64) a)) _
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 4 halign)
    (translate_and_read_value_data_four σ a b0 b1 b2 b3 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign h0 h1 h2 h3)

/-- `vmem_read_addr (Virtaddr a) 2 (Load Data) …` (`lh`/`lhu`). -/
theorem vmem_read_addr_data_two
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhtif : a.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (halign : a.toNat % 2 = 0)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1) :
    (vmem_read_addr (virtaddr.Virtaddr a) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (b1.append b0)) σ :=
  vmem_read_addr_data_w σ a 2 (physaddr.Physaddr (zero_extend (m := 64) a)) _
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 2 halign)
    (translate_and_read_value_data_two σ a b0 b1 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign h0 h1)

/-- `vmem_read_addr (Virtaddr a) 1 (Load Data) …` (`lbu`). Width 1 is trivially
aligned (`a.toNat % 1 = 0`). -/
theorem vmem_read_addr_data_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhiram : a.toNat + 1 ≤ 0x100000000)
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat)
    (h0 : σ.mem[a.toNat]? = some b0) :
    (vmem_read_addr (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok b0) σ :=
  vmem_read_addr_data_w σ a 1 (physaddr.Physaddr (zero_extend (m := 64) a)) _
    vmstatus hpriv hmstatus hmprv (by decide) (by decide) (by omega)
    (is_aligned_vaddr_of_mod a 1 (Nat.mod_one _))
    (translate_and_read_value_data_one σ a b0 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif h0)

/-! ## `vmem_read` composition (address resolution + `vmem_read_addr`).

`vmem_read rs offset width (Load Data) …` resolves the effective address via
`get_transformed_data_addr` (reads `rX_bits rs` = `v1`, adds `offset`, Bare-identity
transform ⇒ `Virtaddr (v1 + offset)`), then runs `vmem_read_addr` at that address.
The generic lemma threads the `vmem_read_addr` result (`hvra`, at `a := v1 + offset`)
abstractly; the per-width corollaries feed the concrete `vmem_read_addr_data_*`. -/

/-- **`vmem_read rs offset width (Load Data) …` composition**, generic over width,
with the `rX_bits rs` read (`hrs`) and the `vmem_read_addr` result (`hvra`, at the
resolved address `v1 + offset`) as hypotheses. Read-only. -/
theorem vmem_read_data_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (width : Nat) (r : Result (BitVec (8 * width)) ExecutionResult)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hvra : (vmem_read_addr (virtaddr.Virtaddr (v1 + offset)) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ = .ok r σ) :
    (vmem_read rs offset width (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok r σ := by
  have hgta := get_transformed_data_addr_data σ rs offset v1 width vmstatus
    hpriv hmstatus hmprv hmseccfg hrs
  simp only [EStateM.run] at hgta hvra
  unfold vmem_read
  simp only [LeanRV64DExecutable.SailME.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure, EStateM.pure]
  rw [hgta]
  simp only [EStateM.bind, EStateM.pure, ExceptT.bindCont, EStateM.map, Functor.map]
  rw [hvra]
  simp only [EStateM.pure]

/-- `vmem_read rs offset 8 (Load Data) …` (`ld`): resolves `a := v1 + offset`, reads
the eight bytes there. Thin composition of `vmem_read_data_w` +
`vmem_read_addr_data_eight`. -/
theorem vmem_read_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + 8 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 8 = 0)
    (h0 : σ.mem[(v1 + offset).toNat]? = some b0) (h1 : σ.mem[(v1 + offset).toNat + 1]? = some b1)
    (h2 : σ.mem[(v1 + offset).toNat + 2]? = some b2) (h3 : σ.mem[(v1 + offset).toNat + 3]? = some b3)
    (h4 : σ.mem[(v1 + offset).toNat + 4]? = some b4) (h5 : σ.mem[(v1 + offset).toNat + 5]? = some b5)
    (h6 : σ.mem[(v1 + offset).toNat + 6]? = some b6) (h7 : σ.mem[(v1 + offset).toNat + 7]? = some b7) :
    (vmem_read rs offset 8 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0)) σ :=
  vmem_read_data_w σ rs offset v1 8 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_eight σ (v1 + offset) b0 b1 b2 b3 b4 b5 b6 b7 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign
      h0 h1 h2 h3 h4 h5 h6 h7)

/-- `vmem_read rs offset 4 (Load Data) …` (`lw`/`lwu`). -/
theorem vmem_read_data_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + 4 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 4 = 0)
    (h0 : σ.mem[(v1 + offset).toNat]? = some b0) (h1 : σ.mem[(v1 + offset).toNat + 1]? = some b1)
    (h2 : σ.mem[(v1 + offset).toNat + 2]? = some b2) (h3 : σ.mem[(v1 + offset).toNat + 3]? = some b3) :
    (vmem_read rs offset 4 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (((b3.append b2).append b1).append b0)) σ :=
  vmem_read_data_w σ rs offset v1 4 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_four σ (v1 + offset) b0 b1 b2 b3 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign h0 h1 h2 h3)

/-- `vmem_read rs offset 2 (Load Data) …` (`lh`/`lhu`). -/
theorem vmem_read_data_two
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (b0 b1 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + 2 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (halign : (v1 + offset).toNat % 2 = 0)
    (h0 : σ.mem[(v1 + offset).toNat]? = some b0) (h1 : σ.mem[(v1 + offset).toNat + 1]? = some b1) :
    (vmem_read rs offset 2 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (b1.append b0)) σ :=
  vmem_read_data_w σ rs offset v1 2 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_two σ (v1 + offset) b0 b1 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif halign h0 h1)

/-- `vmem_read rs offset 1 (Load Data) …` (`lbu`). -/
theorem vmem_read_data_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (rs : regidx) (offset v1 : BitVec 64) (b0 : BitVec 8)
    (vmstatus : RegisterType Register.mstatus) (vpmpaddr : RegisterType Register.pmpaddr_n)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmseccfg : σ.regs.get? Register.mseccfg = some (0#64 : RegisterType Register.mseccfg))
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hcfg : σ.regs.get? Register.pmpcfg_n
      = some ((Vector.replicate 64 (0#8)) : RegisterType Register.pmpcfg_n))
    (haddr : σ.regs.get? Register.pmpaddr_n = some vpmpaddr)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hrs : (rX_bits rs).run σ = .ok v1 σ)
    (hlo : 0x80000000 ≤ (v1 + offset).toNat) (hhiram : (v1 + offset).toNat + 1 ≤ 0x100000000)
    (hhtif : (v1 + offset).toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (v1 + offset).toNat)
    (h0 : σ.mem[(v1 + offset).toNat]? = some b0) :
    (vmem_read rs offset 1 (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok b0) σ :=
  vmem_read_data_w σ rs offset v1 1 _ vmstatus hpriv hmstatus hmprv hmseccfg hrs
    (vmem_read_addr_data_one σ (v1 + offset) b0 vmstatus vpmpaddr
      hpriv hmstatus hmprv hpma hcfg haddr hbase hlo hhiram hhtif h0)

/-! ## `execute_LOAD` characterization (hypothesis-style, `ExecuteAlu` pattern).

The `execute` clause for `instruction.LOAD (imm, rs1, rd, is_unsigned, width)` calls
`execute_LOAD imm rs1 rd is_unsigned width`, which asserts `width ≤ xlen_bytes`
(discharged by `hwidth`), issues `vmem_read rs1 (sign_extend imm) width (Load Data)
false false false` (abstracted by `hread`, following the design brief), and on the
`.Ok data` path writes `wX_bits rd (extend_value is_unsigned data)` (the GPR write
`hwr`, whose post-state `σ'` the caller chooses — a real insert or the `x0` no-op),
tailing in `pure RETIRE_SUCCESS`. The vmem read is read-only, so it lands back at
`σ` (`hread`'s state is `σ`), giving the single-insert post-state StepAlu consumes.
Generic over `width`, `is_unsigned`, and the loaded `data`. -/

/-- **`execute (LOAD …)` characterization**, generic over width/signedness with the
`vmem_read` result supplied abstractly as `hread`. -/
theorem execute_load_char (imm : BitVec 12) (rs1 rd : regidx) (is_unsigned : Bool)
    (width : Nat) (data : BitVec (8 * width))
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwidth : (width ≤b Functions.xlen_bytes) = true)
    (hread : (vmem_read rs1 (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok data) σ)
    (hwr : (wX_bits rd (extend_value is_unsigned data)).run σ = .ok () σ') :
    (execute (instruction.LOAD (imm, rs1, rd, is_unsigned, width))).run σ
      = .ok RETIRE_SUCCESS σ' := by
  simp only [EStateM.run] at hread hwr ⊢
  rw [show (execute (instruction.LOAD (imm, rs1, rd, is_unsigned, width)))
      = execute_LOAD imm rs1 rd is_unsigned width from rfl]
  unfold execute_LOAD
  simp only [LeanRV64DExecutable.assert, PreSail.assert,
    hwidth, if_true, bind, EStateM.bind, pure, EStateM.pure, hread, hwr]

/-- **Signed load** (`is_unsigned = false`: `ld`/`lw`/`lh`). `extend_value false =
sign_extend`, so the GPR write value is `sign_extend data`. Thin corollary of
`execute_load_char`. -/
theorem execute_load_signed_char (imm : BitVec 12) (rs1 rd : regidx)
    (width : Nat) (data : BitVec (8 * width))
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwidth : (width ≤b Functions.xlen_bytes) = true)
    (hread : (vmem_read rs1 (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok data) σ)
    (hwr : (wX_bits rd (sign_extend (m := 64) data)).run σ = .ok () σ') :
    (execute (instruction.LOAD (imm, rs1, rd, false, width))).run σ
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_char imm rs1 rd false width data σ σ' hwidth hread
    (by simpa only [extend_value, if_false] using hwr)

/-- **Unsigned load** (`is_unsigned = true`: `lwu`/`lhu`/`lbu`). `extend_value true =
zero_extend`, so the GPR write value is `zero_extend data`. Thin corollary of
`execute_load_char`. -/
theorem execute_load_unsigned_char (imm : BitVec 12) (rs1 rd : regidx)
    (width : Nat) (data : BitVec (8 * width))
    (σ σ' : SequentialState RegisterType trivialChoiceSource)
    (hwidth : (width ≤b Functions.xlen_bytes) = true)
    (hread : (vmem_read rs1 (sign_extend (m := 64) imm) width
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok data) σ)
    (hwr : (wX_bits rd (zero_extend (m := 64) data)).run σ = .ok () σ') :
    (execute (instruction.LOAD (imm, rs1, rd, true, width))).run σ
      = .ok RETIRE_SUCCESS σ' :=
  execute_load_char imm rs1 rd true width data σ σ' hwidth hread
    (by simpa only [extend_value, if_true] using hwr)

end Vsa.Sim
