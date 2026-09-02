import Vsa.Sim.Hooks
import Vsa.Sim.Pmp
import Vsa.Sim.MemRead
import Vsa.Sim.Fetch

/-!
# M2 — Data-load characterization on the M-mode / Bare / naturally-aligned RV64I hot path

The analogue of the fetch chain (`Vsa/Sim/Fetch.lean`) for `Load Data` accesses,
sized for the binary's load instructions (`ld`=8, `lw`/`lwu`=4, `lh`/`lhu`=2,
`lb`/`lbu`=1).

The `execute_LOAD` clause (`InstsEnd.lean:6779`) calls
`vmem_read rs offset width (Load Data) false false false`, which resolves the
effective address (reading `rs`), then calls
`vmem_read_addr → translate_and_read_value → translateAddr (Load Data) + mem_read (Load Data)`.
The `mem_read` chain is *identical* to fetch except the access type is
`Load Data`, which changes three things:

* `effectivePrivilege` — for a *data* access the MPRV guard
  `bne (Load Data) (InstructionFetch ())` is **true**, so the privilege depends
  on `mstatus.MPRV`; under the hot path `MPRV = 0` ⇒ privilege unchanged (Machine).
* `pmaCheck` — for `Load Data` the `canAccess` bit is `attributes.readable`
  (not `.executable`), which is `true` in the RAM region; and it asserts
  `not res_or_con` (res = false, ok).
* `translateAddr` — `is_shadow_stack_access (Load .Data) = false` (same net
  effect as fetch: Bare identity translation).

### Honest address-range side conditions for data loads

Data lives *above* `tohost` (heap/stack are above `0x8001ad00`), so the fetch
constraint `a + w ≤ tohostAddr` is WRONG here. The real constraint is that the
`[a, a+w)` window must:

* lie in the executable RAM PMA region `[0x80000000, 0x100000000)` (`pmaCheck`);
* avoid the MMIO-*readable* windows the `within_mmio_readable` check excludes —
  the CLINT `[0x2000000, 0x20c0000)`, SIG `[0xc000000, 0xc000020)`, and the
  HTIF `tohost`/`fromhost` mailbox pair. The CLINT/SIG windows are *below*
  `0x80000000` so any RAM address clears them automatically; the only live
  constraint is `a ∉ [tohost, tohost+16)` (the 8-byte `tohost` + 8-byte
  `fromhost` doublewords). We take the honest hypothesis
  `a.toNat + w ≤ tohostAddr ∨ tohostAddr + 16 ≤ a.toNat` — i.e. the load either
  sits below `tohost` (like code/rodata) or strictly above the mailbox pair
  (heap/stack). Both discharge `within_mmio_readable = false`.

So data in `[0x8001ad10, 0x100000000)` (above the mailbox) passes, as does data
in `[0x80000000, 0x8001ad00)` (below it).

Every link is read-only: `σ' = σ` syntactically throughout.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `read_ram` at widths 8/2/1 (the `read_ram_four` analogues).

`read_ram_four` (width 4) lives in `Vsa/Sim/Fetch.lean`; here are the 8/2/1
siblings, bottoming out in `readBytes_eight`/`readBytes_two`/`readByte`. -/

/-- `read_ram Read_plain (Physaddr a) 8 false` reads the eight little-endian
bytes at `a.toNat + 0..7` into a `BitVec 64`, unchanged state. -/
theorem read_ram_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2) (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4) (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6) (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 8 false).run σ
      = .ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0, ()) σ := by
  have e2 : a.toNat + 1 + 1 = a.toNat + 2 := by omega
  have e3 : a.toNat + 1 + 1 + 1 = a.toNat + 3 := by omega
  have e4 : a.toNat + 1 + 1 + 1 + 1 = a.toNat + 4 := by omega
  have e5 : a.toNat + 1 + 1 + 1 + 1 + 1 = a.toNat + 5 := by omega
  have e6 : a.toNat + 1 + 1 + 1 + 1 + 1 + 1 = a.toNat + 6 := by omega
  have e7 : a.toNat + 1 + 1 + 1 + 1 + 1 + 1 + 1 = a.toNat + 7 := by omega
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true,
    e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6, h7]

/-- `read_ram Read_plain (Physaddr a) 2 false` reads the two little-endian
bytes at `a.toNat + 0..1` into a `BitVec 16`, unchanged state. -/
theorem read_ram_two
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 : BitVec 8)
    (h0 : σ.mem[a.toNat]? = some b0) (h1 : σ.mem[a.toNat + 1]? = some b1) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 2 false).run σ
      = .ok (b1.append b0, ()) σ := by
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, h0, h1]

/-- `read_ram Read_plain (Physaddr a) 1 false` reads one byte at `a.toNat` into
a `BitVec 8`, unchanged state. -/
theorem read_ram_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
    (h0 : σ.mem[a.toNat]? = some b0) :
    (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 1 false).run σ
      = .ok (b0, ()) σ := by
  simp only [Functions.read_ram, PreSail.sail_mem_read, PreSail.readBytes,
    PreSail.readByte, default_meta]
  simp [bind, EStateM.bind, pure, EStateM.pure, EStateM.run,
    get, getThe, MonadStateOf.get, EStateM.get, Bool.false_eq_true, h0]

/-! ### `within_mmio_readable = false` at the load widths.

The CLINT `[0x2000000,0x20c0000)` and SIG `[0xc000000,0xc000020)` windows are
below `0x80000000`, so any RAM address clears them. The HTIF-readable window is
the 8-byte `tohost` mailbox `[tohostAddr, tohostAddr+8)`; a load's `[a, a+w)`
avoids it iff it sits entirely below (`a + w ≤ tohostAddr`, code/rodata) or at/
above the mailbox (`tohostAddr + 8 ≤ a`, heap/stack) — the honest disjunctive
side condition `hhtif`. `get_config_rvfi () = false`. Proved per width (the
`addr + width` BitVec arithmetic wants the concrete `w#64`), following the
width-4 `within_mmio_readable_ram_false` in `Vsa/Sim/Hooks.lean` verbatim, with
the disjunctive `hhtif` in place of the fetch `a + 4 ≤ tohost`. -/

/-- `within_mmio_readable a 8 = false` for a RAM `ld`. -/
theorem within_mmio_readable_ram_false_eight
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + 8 ≤ 0x100000000)
    (hhtif : a.toNat + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) 8).run σ = .ok false σ := by
  simp only [within_mmio_readable, within_clint, within_sig, within_htif_readable,
    within_htif_writable, get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhtif
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, BitVec.toNatInt, htif_tohost_size]
  simp only [tohostAddr] at *
  have hadd : (a + 8#64).toNat = a.toNat + 8 := by
    have hw : ((8#64 : BitVec 64)).toNat = 8 := by decide
    rw [BitVec.toNat_add, hw, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  rename_i hx
  -- `hx : a.toNat < (tohost + 8)` (the readable HTIF mailbox end); `hhtif` then
  -- forces the load window below `tohost`. The mailbox-end value is a closed
  -- `BitVec` term at the symbolic `physaddrbits` width, so bridge it by defeq
  -- (`Nat.lt_of_lt_of_eq`) rather than `rw`, which the width mismatch defeats.
  have hxlt : a.toNat < 2147593480 := by
    have hxv : (2147593472#64 + 8#64).toNat = 2147593480 := by decide
    exact Nat.lt_of_lt_of_eq hx hxv
  have hle : (a + 8#64).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616
      = ((2147593472 : Nat) : Int) := by decide
  rw [hrhs]
  exact_mod_cast hle

/-- `within_mmio_readable a 4 = false` for a RAM `lw`/`lwu`. -/
theorem within_mmio_readable_ram_false_four'
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + 4 ≤ 0x100000000)
    (hhtif : a.toNat + 4 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) 4).run σ = .ok false σ := by
  simp only [within_mmio_readable, within_clint, within_sig, within_htif_readable,
    within_htif_writable, get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhtif
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, BitVec.toNatInt, htif_tohost_size]
  simp only [tohostAddr] at *
  have hadd : (a + 4#64).toNat = a.toNat + 4 := by
    have hw : ((4#64 : BitVec 64)).toNat = 4 := by decide
    rw [BitVec.toNat_add, hw, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  rename_i hx
  -- `hx : a.toNat < (tohost + 8)` (the readable HTIF mailbox end); `hhtif` then
  -- forces the load window below `tohost`. The mailbox-end value is a closed
  -- `BitVec` term at the symbolic `physaddrbits` width, so bridge it by defeq
  -- (`Nat.lt_of_lt_of_eq`) rather than `rw`, which the width mismatch defeats.
  have hxlt : a.toNat < 2147593480 := by
    have hxv : (2147593472#64 + 8#64).toNat = 2147593480 := by decide
    exact Nat.lt_of_lt_of_eq hx hxv
  have hle : (a + 4#64).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616
      = ((2147593472 : Nat) : Int) := by decide
  rw [hrhs]
  exact_mod_cast hle

/-- `within_mmio_readable a 2 = false` for a RAM `lh`/`lhu`. -/
theorem within_mmio_readable_ram_false_two
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + 2 ≤ 0x100000000)
    (hhtif : a.toNat + 2 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) 2).run σ = .ok false σ := by
  simp only [within_mmio_readable, within_clint, within_sig, within_htif_readable,
    within_htif_writable, get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhtif
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, BitVec.toNatInt, htif_tohost_size]
  simp only [tohostAddr] at *
  have hadd : (a + 2#64).toNat = a.toNat + 2 := by
    have hw : ((2#64 : BitVec 64)).toNat = 2 := by decide
    rw [BitVec.toNat_add, hw, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  rename_i hx
  -- `hx : a.toNat < (tohost + 8)` (the readable HTIF mailbox end); `hhtif` then
  -- forces the load window below `tohost`. The mailbox-end value is a closed
  -- `BitVec` term at the symbolic `physaddrbits` width, so bridge it by defeq
  -- (`Nat.lt_of_lt_of_eq`) rather than `rw`, which the width mismatch defeats.
  have hxlt : a.toNat < 2147593480 := by
    have hxv : (2147593472#64 + 8#64).toNat = 2147593480 := by decide
    exact Nat.lt_of_lt_of_eq hx hxv
  have hle : (a + 2#64).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616
      = ((2147593472 : Nat) : Int) := by decide
  rw [hrhs]
  exact_mod_cast hle

/-- `within_mmio_readable a 1 = false` for a RAM `lb`/`lbu`. -/
theorem within_mmio_readable_ram_false_one
    (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (hbase : σ.regs.get? Register.htif_tohost_base
      = some (some (BitVec.ofNat 64 tohostAddr) : RegisterType Register.htif_tohost_base))
    (hlo : 0x80000000 ≤ a.toNat) (hhiram : a.toNat + 1 ≤ 0x100000000)
    (hhtif : a.toNat + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (within_mmio_readable (physaddr.Physaddr a) 1).run σ = .ok false σ := by
  simp only [within_mmio_readable, within_clint, within_sig, within_htif_readable,
    within_htif_writable, get_config_rvfi, plat_have_clint, plat_have_sig,
    zopz0zI_u, zopz0zK_u, LeanRV64DExecutable.Functions.not]
  simp only [tohostAddr] at hhtif
  have hcb : BitVec.toNat plat_clint_base = 33554432 := by decide
  have hcs : BitVec.toNat plat_clint_size = 786432 := by decide
  have hsb : BitVec.toNat plat_sig_base = 201326592 := by decide
  have hss : BitVec.toNat plat_sig_size = 32 := by decide
  simp_all [simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg, get, getThe, MonadStateOf.get,
    EStateM.get, BitVec.toNatInt, htif_tohost_size]
  simp only [tohostAddr] at *
  have hadd : (a + 1#64).toNat = a.toNat + 1 := by
    have hw : ((1#64 : BitVec 64)).toNat = 1 := by decide
    rw [BitVec.toNat_add, hw, Nat.mod_eq_of_lt (by omega)]
  refine ⟨fun _ => by omega, fun _ => by omega, fun _ => ?_⟩
  rename_i hx
  -- `hx : a.toNat < (tohost + 8)` (the readable HTIF mailbox end); `hhtif` then
  -- forces the load window below `tohost`. The mailbox-end value is a closed
  -- `BitVec` term at the symbolic `physaddrbits` width, so bridge it by defeq
  -- (`Nat.lt_of_lt_of_eq`) rather than `rw`, which the width mismatch defeats.
  have hxlt : a.toNat < 2147593480 := by
    have hxv : (2147593472#64 + 8#64).toNat = 2147593480 := by decide
    exact Nat.lt_of_lt_of_eq hx hxv
  have hle : (a + 1#64).toNat ≤ 2147593472 := by rw [hadd]; omega
  have hrhs : ((2147593472 : Nat) : Int) % 18446744073709551616
      = ((2147593472 : Nat) : Int) := by decide
  rw [hrhs]
  exact_mod_cast hle

/-! ## Control-plane clones for the `Load Data` access type. -/

/-- `effectivePrivilege (Load Data) m p = p` when `mstatus.MPRV = 0`. Unlike the
fetch case, the MPRV guard `bne (Load Data) (InstructionFetch ())` is *true* for
a data access, so the second conjunct `mstatus.MPRV == 1` is what decides;
`MPRV = 0` ⇒ the guard is false ⇒ privilege unchanged. Reused by `translateAddr`
and `mem_read` on the load path. -/
theorem effectivePrivilege_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (m : BitVec 64) (p : Privilege)
    (hmprv : _get_Mstatus_MPRV m = 0#1) :
    (effectivePrivilege (MemoryAccessType.Load mem_payload.Data) m p).run σ
      = .ok p σ := by
  simp only [effectivePrivilege, bne]
  have hc : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by
    decide
  simp only [hc, Bool.not_false, hmprv, Bool.true_and]
  have hz : (0#1 == 1#1) = false := by decide
  simp [simp_sail, EStateM.run, pure, EStateM.pure, hz]

open MemoryRegionType AtomicSupport Reservability misaligned_exception in
/-- `pmaCheck (Physaddr a) w (Load Data) PBMT_PMA false` succeeds with
`Ok { splittable := CannotSplit, granule_size_exp := 0 }` for a naturally-aligned
`[a, a+w)` window inside the RAM region `[0x80000000, 0x100000000)`. The
`Load Data` `canAccess` branch asserts `not false` and returns
`attributes.readable = true`. Width-generic: the region-walk width appears only
as `to_bits w`, supplied reduced by `htb`; the `range_subset` comparisons are
`bv_omega` over `a.toNat + w ≤ 0x100000000`; `is_aligned_paddr` closes from
`halign`. `SailME.run` boundary. -/
theorem pmaCheck_ram_read
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat)
    (htb : (to_bits (l := 64) w : BitVec 64) = BitVec.ofNat 64 w)
    (hpma : σ.regs.get? Register.pma_regions
      = some (initPmaRegions : RegisterType Register.pma_regions))
    (hlo : 0x80000000 ≤ a.toNat)
    (hhi : a.toNat + w ≤ 0x100000000)
    (halign : Int.tmod (BitVec.toNatInt a) w = 0) :
    (pmaCheck (physaddr.Physaddr a) w (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA false).run σ
      = .ok (.Ok { splittable := Splittability.CannotSplit, granule_size_exp := 0 }) σ := by
  have hmatch : matching_pma_region_bits_range initPmaRegions
      (zero_extend (bits_of_physaddr (physaddr.Physaddr a))) (to_bits w)
      = some ({ base := 0x80000000#64
                size := 0x80000000#64
                attributes := { mem_type := MainMemory
                                cacheable := true
                                coherent := true
                                executable := true
                                readable := true
                                writable := true
                                read_idempotent := true
                                write_idempotent := true
                                misaligned_exceptions := { load_store := none
                                                           vector := none
                                                           amo := AccessFault }
                                atomic_support := AMOCASQ
                                reservability := RsrvEventual
                                supports_cbo_zero := true
                                supports_pte_read := true
                                supports_pte_write := true
                                misaligned_atomicity_granule_size_exp := 4
                                vector_misaligned_atomicity_granule_size_exp := 4 }
                include_in_device_tree := true } : PMA_Region) := by
    have hz : (zero_extend (bits_of_physaddr (physaddr.Physaddr a)) : BitVec 64) = a :=
      BitVec.setWidth_eq a
    rw [hz, htb]
    simp only [initPmaRegions, matching_pma_region_bits_range, range_subset,
      zopz0zIzJ_u, BitVec.toNatInt]
    rw [if_neg, if_neg, if_pos]
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨?_, ?_, ?_⟩ <;> · apply Int.ofNat_le.mpr; bv_omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
    · simp only [Bool.and_eq_true, decide_eq_true_eq]
      rintro ⟨h1, _⟩; have := Int.ofNat_le.mp h1; bv_omega
  unfold pmaCheck
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpma]
  simp only [pure, EStateM.pure, matching_pma_region, hmatch, override_PMA,
    Functions.not, mag_pma_check, is_mag_applicable_access, is_aligned_paddr,
    LeanRV64DExecutable.assert, PreSail.assert, BitVec.toNatInt,
    ExceptT.pure, ExceptT.bindCont, ExceptT.mk,
    EStateM.map, EStateM.bind, bind, Bind.bind,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, if_true,
    if_false]
  rw [if_pos]
  · rfl
  · simp only [Bool.or_eq_true, beq_iff_eq]
    exact Or.inl (by exact_mod_cast halign)

/-! ## Width-generic `split_misaligned` collapse.

`split_misaligned_aligned` in `Vsa/Sim/Hooks.lean` is hardcoded to width 4.
The load widths need 8/2/1, so here is the width-generic clone (same proof,
`w` as a parameter). For a `w`-aligned address `do_not_split` is `true` via the
alignment disjunct, collapsing the `untilFuelM` loop to a single iteration. -/

/-- `split_misaligned addr w e s = (1, w)` for a `w`-aligned address. -/
theorem split_misaligned_aligned_w
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (w : Nat) (e : Nat) (s : Splittability)
    (ha : Int.tmod (BitVec.toNatInt a) w = 0) :
    (split_misaligned (physaddr.Physaddr a) w e s).run σ
      = .ok (1, (w : Int)) σ := by
  simp only [split_misaligned]
  split
  · simp [simp_sail, EStateM.run, pure, EStateM.pure]
  · rename_i hneg
    exfalso
    apply hneg
    simp only [Bool.or_eq_true, beq_iff_eq]
    refine Or.inr (Or.inl ?_)
    exact_mod_cast ha

/-! ## `checked_mem_read` on the `Load Data` RAM path.

Clones of `checked_mem_read_four` (`Vsa/Sim/Fetch.lean`) for the `Load Data`
access type, composing `pmaCheck_ram_read`, `split_misaligned_aligned` (⇒ N=1),
`pmp_allows`, the width-`w` `within_mmio_readable_ram_false_*`, and `read_ram_*`.
Proved per width (the `to_bits w`, the loop-offset/word arithmetic, and the
final `updateSubrange` reassembly are all width-specific). -/

/-- Width-8 `checked_mem_read` on the RAM `Load Data` path, **parametric in the
value the RAM leaf returns**.  Byte-level information enters ONLY through
`hram`, so this single proof serves both the presence-hypothesis leaf
(`read_ram_eight`) and the TOTAL leaf (`read_ram_eight_total`,
`Vsa/Sim/MemLoadTotal.lean`) — the Sail model reads memory totally
(`readByte = getD 0`), so presence is never a semantic requirement of a load. -/
theorem checked_mem_read_data_eight_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 64)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 8 false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ
      = .ok (.Ok (v, ())) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 8 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 8)) = Int.ofNat (a.toNat % 8) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (8 : Int) = Int.ofNat 8 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_read σ a 8 (by decide) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 8
    (MemoryAccessType.Load mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false_eight σ a hbase hlo hhiram hhtif
  have hsplit : (split_misaligned (physaddr.Physaddr a) 8 0 Splittability.CannotSplit).run σ
      = .ok (1, (8 : Int)) σ := by
    have h := split_misaligned_aligned_w σ a 8 0 Splittability.CannotSplit htmod
    rw [h, show ((8 : Nat) : Int) = (8 : Int) from rfl]
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]
  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl, show Int.toNat 8 = 8 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (8 : Int)) = (0 : Int) from by decide, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  have hram' : Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) (Int.toNat 8) false σ
      = EStateM.Result.ok (v, ()) σ := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * 8 - 1 : Int).toNat = 63 := by decide
  have e2 : (8 * ((0:Nat):Int) * 8 : Int).toNat = 0 := by decide
  rw [e1, e2]
  congr 3
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  have key : (0#64 ||| v <<< 0) = v := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.shiftLeft_zero]
  exact key

/-- `checked_mem_read (Load Data) PBMT_PMA Machine (Physaddr a) 8 …` reads the
eight code/data bytes into a `BitVec 64`, unchanged state. -/
theorem checked_mem_read_data_eight
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4)
    (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6)
    (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ
      = .ok (.Ok ((((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0), ())) σ :=
  checked_mem_read_data_eight_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 h0 h1 h2 h3 h4 h5 h6 h7)

/-- Width-4 `checked_mem_read` on the RAM `Load Data` path, **parametric in the
value the RAM leaf returns**.  Byte-level information enters ONLY through
`hram`, so this single proof serves both the presence-hypothesis leaf
(`read_ram_four`) and the TOTAL leaf (`read_ram_four_total`,
`Vsa/Sim/MemLoadTotal.lean`) — the Sail model reads memory totally
(`readByte = getD 0`), so presence is never a semantic requirement of a load. -/
theorem checked_mem_read_data_four_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 32)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 4 false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        4 false false false false).run σ
      = .ok (.Ok (v, ())) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 4 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 4)) = Int.ofNat (a.toNat % 4) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (4 : Int) = Int.ofNat 4 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_read σ a 4 (by decide) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 4
    (MemoryAccessType.Load mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false_four' σ a hbase hlo hhiram hhtif
  have hsplit : (split_misaligned (physaddr.Physaddr a) 4 0 Splittability.CannotSplit).run σ
      = .ok (1, (4 : Int)) σ := by
    have h := split_misaligned_aligned_w σ a 4 0 Splittability.CannotSplit htmod
    rw [h, show ((4 : Nat) : Int) = (4 : Int) from rfl]
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]
  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl, show Int.toNat 4 = 4 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (4 : Int)) = (0 : Int) from by decide, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  have hram' : Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) (Int.toNat 4) false σ
      = EStateM.Result.ok (v, ()) σ := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * 4 - 1 : Int).toNat = 31 := by decide
  have e2 : (8 * ((0:Nat):Int) * 4 : Int).toNat = 0 := by decide
  rw [e1, e2]
  congr 3
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  have key : (0#32 ||| v <<< 0) = v := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.shiftLeft_zero]
  exact key

/-- `checked_mem_read (Load Data) PBMT_PMA Machine (Physaddr a) 4 …` reads the
four data bytes into a `BitVec 32`, unchanged state. Width-4 clone of
`checked_mem_read_data_eight`. -/
theorem checked_mem_read_data_four
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 b2 b3 : BitVec 8)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        4 false false false false).run σ
      = .ok (.Ok (((((b3.append b2).append b1).append b0)), ())) σ :=
  checked_mem_read_data_four_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_four σ a b0 b1 b2 b3 h0 h1 h2 h3)

/-- Width-2 `checked_mem_read` on the RAM `Load Data` path, **parametric in the
value the RAM leaf returns**.  Byte-level information enters ONLY through
`hram`, so this single proof serves both the presence-hypothesis leaf
(`read_ram_two`) and the TOTAL leaf (`read_ram_two_total`,
`Vsa/Sim/MemLoadTotal.lean`) — the Sail model reads memory totally
(`readByte = getD 0`), so presence is never a semantic requirement of a load. -/
theorem checked_mem_read_data_two_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 16)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 2 false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        2 false false false false).run σ
      = .ok (.Ok (v, ())) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 2 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 2)) = Int.ofNat (a.toNat % 2) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (2 : Int) = Int.ofNat 2 from rfl, this, halign]; rfl
  have hpmaC := pmaCheck_ram_read σ a 2 (by decide) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 2
    (MemoryAccessType.Load mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false_two σ a hbase hlo hhiram hhtif
  have hsplit : (split_misaligned (physaddr.Physaddr a) 2 0 Splittability.CannotSplit).run σ
      = .ok (1, (2 : Int)) σ := by
    have h := split_misaligned_aligned_w σ a 2 0 Splittability.CannotSplit htmod
    rw [h, show ((2 : Nat) : Int) = (2 : Int) from rfl]
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]
  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl, show Int.toNat 2 = 2 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (2 : Int)) = (0 : Int) from by decide, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  have hram' : Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) (Int.toNat 2) false σ
      = EStateM.Result.ok (v, ()) σ := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * 2 - 1 : Int).toNat = 15 := by decide
  have e2 : (8 * ((0:Nat):Int) * 2 : Int).toNat = 0 := by decide
  rw [e1, e2]
  congr 3
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  have key : (0#16 ||| v <<< 0) = v := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.shiftLeft_zero]
  exact key

/-- `checked_mem_read (Load Data) PBMT_PMA Machine (Physaddr a) 2 …` reads the
two data bytes into a `BitVec 16`, unchanged state. Width-2 clone of
`checked_mem_read_data_eight`. -/
theorem checked_mem_read_data_two
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 b1 : BitVec 8)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        2 false false false false).run σ
      = .ok (.Ok (((b1.append b0)), ())) σ :=
  checked_mem_read_data_two_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif halign (read_ram_two σ a b0 b1 h0 h1)

/-- Width-1 `checked_mem_read` on the RAM `Load Data` path, **parametric in the
value the RAM leaf returns**.  Byte-level information enters ONLY through
`hram`, so this single proof serves both the presence-hypothesis leaf
(`read_ram_one`) and the TOTAL leaf (`read_ram_one_total`,
`Vsa/Sim/MemLoadTotal.lean`) — the Sail model reads memory totally
(`readByte = getD 0`), so presence is never a semantic requirement of a load. -/
theorem checked_mem_read_data_one_of_ram
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 8)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (hram : (Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) 1 false).run σ
      = .ok (v, ()) σ) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ
      = .ok (.Ok (v, ())) σ := by
  have htmod : Int.tmod (BitVec.toNatInt a) 1 = 0 := by
    simp only [BitVec.toNatInt]
    have : ((Int.ofNat a.toNat).tmod (Int.ofNat 1)) = Int.ofNat (a.toNat % 1) :=
      (Int.ofNat_tmod _ _).symm
    rw [show (1 : Int) = Int.ofNat 1 from rfl, this, Nat.mod_one]; rfl
  have hpmaC := pmaCheck_ram_read σ a 1 (by decide) hpma hlo hhiram htmod
  have hpmp := pmp_allows σ (physaddr.Physaddr a) 1
    (MemoryAccessType.Load mem_payload.Data) vpmpaddr hcfg haddr
  have hmmio := within_mmio_readable_ram_false_one σ a hbase hlo hhiram hhtif
  have hsplit : (split_misaligned (physaddr.Physaddr a) 1 0 Splittability.CannotSplit).run σ
      = .ok (1, (1 : Int)) σ := by
    have h := split_misaligned_aligned_w σ a 1 0 Splittability.CannotSplit htmod
    rw [h, show ((1 : Nat) : Int) = (1 : Int) from rfl]
  simp only [EStateM.run] at hpmaC hpmp hmmio hsplit hram
  unfold checked_mem_read
  simp only [check_pma_with_pmp_priority, read_kind_of_flags, misaligned_order,
    sys_misaligned_order_decreasing, bits_of_physaddr,
    LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, pure]
  rw [hpmaC]
  simp only [EStateM.pure, ExceptT.bindCont, EStateM.map, EStateM.bind]
  rw [hsplit]
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont, EStateM.map]
  simp only [Int.reduceNeg, Bool.false_eq_true, if_false,
    show ((1 : Int) - 1) = 0 from by decide,
    show Int.toNat 1 = 1 from rfl,
    show Int.toNat 0 = 0 from rfl]
  rw [untilFuelM]
  simp only [untilFuelM.go]
  simp only [ExceptT.bind, ExceptT.bindCont, ExceptT.mk, ExceptT.pure,
    EStateM.map, EStateM.bind, EStateM.pure, bind, pure, Pure.pure,
    LeanRV64DExecutable.assert, PreSail.assert, if_true,
    show (↑(0 : Nat) * (1 : Int)) = (0 : Int) from by decide, addInt_zero_pa,
    hpmp, hmmio, Bool.false_eq_true, if_false]
  have hram' : Functions.read_ram read_kind.Read_plain (physaddr.Physaddr a) (Int.toNat 1) false σ
      = EStateM.Result.ok (v, ()) σ := hram
  rw [hram']
  simp only [EStateM.pure, EStateM.bind, ExceptT.bindCont,
    beq_self_eq_true, if_true, default_meta]
  have e1 : (8 * (((0:Nat):Int) + 1) * 1 - 1 : Int).toNat = 7 := by decide
  have e2 : (8 * ((0:Nat):Int) * 1 : Int).toNat = 0 := by decide
  rw [e1, e2]
  congr 3
  simp only [BitVec.updateSubrange, Sail.BitVec.updateSubrange', Functions.zeros]
  have key : (0#8 ||| v <<< 0) = v := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.shiftLeft_zero]
  exact key

/-- `checked_mem_read (Load Data) PBMT_PMA Machine (Physaddr a) 1 …` reads one
data byte into a `BitVec 8`, unchanged state. Width-1 clone of
`checked_mem_read_data_eight`. -/
theorem checked_mem_read_data_one
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (b0 : BitVec 8)
    (vpmpaddr : RegisterType Register.pmpaddr_n)
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
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ
      = .ok (.Ok ((b0), ())) σ :=
  checked_mem_read_data_one_of_ram σ a _ vpmpaddr hpma hcfg haddr hbase
    hlo hhiram hhtif (read_ram_one σ a b0 h0)

/-! ## `mem_read` on the `Load Data` RAM path.

Clones of `mem_read_four` (`Vsa/Sim/Fetch.lean`) for the `Load Data` access
type. Resolves the effective privilege via `effectivePrivilege_data`
(MPRV = 0 ⇒ Machine unchanged), threads `mem_read_priv`/`mem_read_priv_meta`
(dropping metadata via `MemoryOpResult_drop_meta`, firing the no-op
`mem_read_callback`) down to the width-`w` `checked_mem_read_data_*`. The
`(aq,rl,res) = (false,false,false)` tuple lands on the `(_,_,_)` catch-all.
Requires `mstatus.MPRV = 0` (the extra data-path hypothesis absent for fetch). -/

/-- Width-8 `mem_read` on the `Load Data` RAM path, parametric in the value the
`checked_mem_read` layer returns (see `checked_mem_read_data_eight_of_ram`). -/
theorem mem_read_data_eight_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        8 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok v) σ := by
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

/-- `mem_read (Load Data) PBMT_PMA (Physaddr a) 8 …` returns `Ok w`, unchanged. -/
theorem mem_read_data_eight
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4)
    (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6)
    (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0)) σ :=
  mem_read_data_eight_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)

/-- Width-4 `mem_read` on the `Load Data` RAM path, parametric in the value the
`checked_mem_read` layer returns (see `checked_mem_read_data_four_of_ram`). -/
theorem mem_read_data_four_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 32)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        4 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok v) σ := by
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

/-- `mem_read (Load Data) PBMT_PMA (Physaddr a) 4 …` returns `Ok w`, unchanged. -/
theorem mem_read_data_four
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok ((((b3.append b2).append b1).append b0))) σ :=
  mem_read_data_four_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_four σ a b0 b1 b2 b3 vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign h0 h1 h2 h3)

/-- Width-2 `mem_read` on the `Load Data` RAM path, parametric in the value the
`checked_mem_read` layer returns (see `checked_mem_read_data_two_of_ram`). -/
theorem mem_read_data_two_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 16)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        2 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 2 false false false).run σ
      = .ok (.Ok v) σ := by
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

/-- `mem_read (Load Data) PBMT_PMA (Physaddr a) 2 …` returns `Ok w`, unchanged. -/
theorem mem_read_data_two
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 2 false false false).run σ
      = .ok (.Ok ((b1.append b0))) σ :=
  mem_read_data_two_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_two σ a b0 b1 vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif halign h0 h1)

/-- Width-1 `mem_read` on the `Load Data` RAM path, parametric in the value the
`checked_mem_read` layer returns (see `checked_mem_read_data_one_of_ram`). -/
theorem mem_read_data_one_of_cmr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hcmr : (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
        1 false false false false).run σ = .ok (.Ok (v, ())) σ) :
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok v) σ := by
  have hep := effectivePrivilege_data σ vmstatus Privilege.Machine hmprv
  simp only [EStateM.run] at hcmr hep
  unfold mem_read mem_read_priv mem_read_priv_meta
  simp only [EStateM.run, bind, EStateM.bind, pure, EStateM.pure,
    LeanRV64DExecutable.readReg, Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hmstatus, hpriv]
  rw [hep]
  simp only [MemoryOpResult_drop_meta]
  rw [hcmr]

/-- `mem_read (Load Data) PBMT_PMA (Physaddr a) 1 …` returns `Ok w`, unchanged. -/
theorem mem_read_data_one
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
    (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok (b0)) σ :=
  mem_read_data_one_of_cmr σ a _ vmstatus hpriv hmstatus hmprv
    (checked_mem_read_data_one σ a b0 vpmpaddr hpma hcfg haddr hbase
      hlo hhiram hhtif h0)

/-! ## `translateAddr` and `translate_and_read_value` on the `Load Data` path. -/

/-- `translateAddr (Virtaddr a) (Load Data)` on the Machine/Bare data path
returns `Ok (Physaddr (zero_extend a), PBMT_PMA, ())` reading only `mstatus`
(MPRV = 0) and `cur_privilege` (= Machine). Data clone of
`translateAddr_machine_fetch`: `effectivePrivilege` MPRV guard is live for a
data access but `MPRV = 0` ⇒ priv unchanged; `translationMode Machine = Bare`
(`satp` unread); `is_shadow_stack_access (Load Data) = false`; `mode == Bare` ⇒
identity translation. -/
theorem translateAddr_machine_data
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1) :
    (translateAddr (virtaddr.Virtaddr a) (MemoryAccessType.Load mem_payload.Data)).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          page_based_mem_type.PBMT_PMA, ())) σ := by
  unfold translateAddr
  simp only [LeanRV64DExecutable.SailME.run, LeanRV64DExecutable.SailME.throw,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.run, ExceptT.run,
    Sail.ConcurrencyInterfaceV1.PreSail.PreSailME.throw,
    bind, ExceptT.bind, ExceptT.mk, liftM, monadLift, MonadLift.monadLift,
    ExceptT.lift, ExceptT.bindCont, ExceptT.pure, Functor.map, EStateM.map,
    EStateM.run, EStateM.bind, EStateM.pure, LeanRV64DExecutable.readReg,
    Sail.ConcurrencyInterfaceV1.PreSail.readReg,
    get, getThe, MonadStateOf.get, EStateM.get, hpriv, hmstatus,
    effectivePrivilege, translationMode, is_shadow_stack_access, bne,
    bits_of_virtaddr, init_ext_ptw, pure]
  have hda : (MemoryAccessType.Load mem_payload.Data ==
      (MemoryAccessType.InstructionFetch () : MemoryAccessType mem_payload)) = false := by
    decide
  have hmprv0 : (_get_Mstatus_MPRV vmstatus == 1#1) = false := by
    rw [hmprv]; decide
  have hpm : (Privilege.Machine == Privilege.Machine) = true := by decide
  have hb : (SATPMode.Bare == SATPMode.Bare) = true := by decide
  simp only [hda, hmprv0, hpm, hb, EStateM.pure, EStateM.map, EStateM.bind,
    ExceptT.bindCont, Bool.not_false, Bool.and_false,
    if_false, if_true, Bool.false_eq_true]

/-- Width-8 `translate_and_read_value` on the `Load Data` RAM path, parametric
in the value the `mem_read` layer returns (see `mem_read_data_eight_of_cmr`). -/
theorem translate_and_read_value_data_eight_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 64)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 8 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ := by
  have htr := translateAddr_machine_data σ a vmstatus hpriv hmstatus hmprv
  simp only [EStateM.run] at htr hmr
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, EStateM.run, pure]
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  rw [htr]
  simp only [EStateM.bind, hze]
  rw [hmr]
  simp only [EStateM.pure]

/-- `translate_and_read_value (Virtaddr a) 8 (Load Data) …` returns
`Ok (Physaddr (zero_extend a), w)`, unchanged state. Composes
`translateAddr_machine_data` (Bare identity ⇒ `Physaddr (zero_extend a)`) with
`mem_read_data_eight`. -/
theorem translate_and_read_value_data_eight
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3)
    (h4 : σ.mem[a.toNat + 4]? = some b4)
    (h5 : σ.mem[a.toNat + 5]? = some b5)
    (h6 : σ.mem[a.toNat + 6]? = some b6)
    (h7 : σ.mem[a.toNat + 7]? = some b7) :
    (translate_and_read_value (virtaddr.Virtaddr a) 8
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          (((((((b7.append b6).append b5).append b4).append b3).append
          b2).append b1).append b0))) σ :=
  translate_and_read_value_data_eight_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_eight σ a b0 b1 b2 b3 b4 b5 b6 b7 vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign h0 h1 h2 h3 h4 h5 h6 h7)

/-- Width-4 `translate_and_read_value` on the `Load Data` RAM path, parametric
in the value the `mem_read` layer returns (see `mem_read_data_four_of_cmr`). -/
theorem translate_and_read_value_data_four_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 32)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 4 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ := by
  have htr := translateAddr_machine_data σ a vmstatus hpriv hmstatus hmprv
  simp only [EStateM.run] at htr hmr
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, EStateM.run, pure]
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  rw [htr]
  simp only [EStateM.bind, hze]
  rw [hmr]
  simp only [EStateM.pure]

/-- `translate_and_read_value (Virtaddr a) 4 (Load Data) …`. Width-4 clone. -/
theorem translate_and_read_value_data_four
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1)
    (h2 : σ.mem[a.toNat + 2]? = some b2)
    (h3 : σ.mem[a.toNat + 3]? = some b3) :
    (translate_and_read_value (virtaddr.Virtaddr a) 4
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          ((((b3.append b2).append b1).append b0)))) σ :=
  translate_and_read_value_data_four_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_four σ a b0 b1 b2 b3 vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign h0 h1 h2 h3)

/-- Width-2 `translate_and_read_value` on the `Load Data` RAM path, parametric
in the value the `mem_read` layer returns (see `mem_read_data_two_of_cmr`). -/
theorem translate_and_read_value_data_two_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 16)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 2 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ := by
  have htr := translateAddr_machine_data σ a vmstatus hpriv hmstatus hmprv
  simp only [EStateM.run] at htr hmr
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, EStateM.run, pure]
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  rw [htr]
  simp only [EStateM.bind, hze]
  rw [hmr]
  simp only [EStateM.pure]

/-- `translate_and_read_value (Virtaddr a) 2 (Load Data) …`. Width-2 clone. -/
theorem translate_and_read_value_data_two
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
    (h0 : σ.mem[a.toNat]? = some b0)
    (h1 : σ.mem[a.toNat + 1]? = some b1) :
    (translate_and_read_value (virtaddr.Virtaddr a) 2
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          ((b1.append b0)))) σ :=
  translate_and_read_value_data_two_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_two σ a b0 b1 vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif halign h0 h1)

/-- Width-1 `translate_and_read_value` on the `Load Data` RAM path, parametric
in the value the `mem_read` layer returns (see `mem_read_data_one_of_cmr`). -/
theorem translate_and_read_value_data_one_of_mr
    (σ : SequentialState RegisterType trivialChoiceSource)
    (a : BitVec 64) (v : BitVec 8)
    (vmstatus : RegisterType Register.mstatus)
    (hpriv : σ.regs.get? Register.cur_privilege
      = some (Privilege.Machine : RegisterType Register.cur_privilege))
    (hmstatus : σ.regs.get? Register.mstatus = some vmstatus)
    (hmprv : _get_Mstatus_MPRV vmstatus = 0#1)
    (hmr : (mem_read (MemoryAccessType.Load mem_payload.Data)
        page_based_mem_type.PBMT_PMA (physaddr.Physaddr a) 1 false false false).run σ
      = .ok (.Ok v) σ) :
    (translate_and_read_value (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a), v)) σ := by
  have htr := translateAddr_machine_data σ a vmstatus hpriv hmstatus hmprv
  simp only [EStateM.run] at htr hmr
  unfold translate_and_read_value
  simp only [bind, EStateM.bind, EStateM.run, pure]
  have hze : (zero_extend (m := 64) a : BitVec 64) = a := BitVec.setWidth_eq a
  rw [htr]
  simp only [EStateM.bind, hze]
  rw [hmr]
  simp only [EStateM.pure]

/-- `translate_and_read_value (Virtaddr a) 1 (Load Data) …`. Width-1 clone. -/
theorem translate_and_read_value_data_one
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
    (translate_and_read_value (virtaddr.Virtaddr a) 1
        (MemoryAccessType.Load mem_payload.Data) false false false).run σ
      = .ok (.Ok (physaddr.Physaddr (zero_extend (m := 64) a),
          (b0))) σ :=
  translate_and_read_value_data_one_of_mr σ a _ vmstatus hpriv hmstatus hmprv
    (mem_read_data_one σ a b0 vmstatus vpmpaddr hpriv hmstatus hmprv hpma hcfg
      haddr hbase hlo hhiram hhtif h0)

end Vsa.Sim
