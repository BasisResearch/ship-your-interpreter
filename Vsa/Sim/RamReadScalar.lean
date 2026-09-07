import Vsa.Sim.CheckedSplitRead
import Vsa.Sim.SplitReadAssembly

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register Sail.ConcurrencyInterfaceV1.PreSail
namespace Vsa.Sim

/-- Actual chunk calls plus exact width coverage supply the total byte result. -/
theorem checked_mem_read_split_total (σ : Vsa.Machine.MState) (a : BitVec 64)
    (w n d : Nat) (info : Phys_Mem_Access_Info) (hd : 0 < d) (he : n * d = w)
    (hp : SplitReadPlan σ a w n d info)
    (hc : ∀ i, i < n → SplitReadChunk σ a d i (bytesT σ.mem (a.toNat + i * d) d)) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
      w false false false false).run σ = .ok (.Ok (bytesT σ.mem a.toNat w, ())) σ := by
  subst w
  have h := checked_mem_read_of_split σ a (n * d) n d info
    (fun i => bytesT σ.mem (a.toNat + i * d) d) hp hc
  rw [splitReadAccum_bytesT σ.mem a.toNat n d hd _ (fun _ _ => rfl)] at h
  exact h

/-- Sail's integer chunk address equals the nonwrapping scalar-plan address. -/
theorem ramChunkAddress_scalar (a : BitVec 64) (k i : Nat) :
    ramChunkAddress a (2 ^ scalarChunkExp a k) i =
      physaddr.Physaddr (scalarChunkAddress a k i) := by
  simp only [ramChunkAddress, scalarChunkAddress, Sail.BitVec.addInt,
    ← Int.natCast_mul, BitVec.ofInt_natCast]
  rfl

/-- GoodState and the original RAM window supply every actual chunk check. -/
theorem SplitReadChunk.of_scalar {σ : Vsa.Machine.MState} (hg : GoodState σ)
    (a : BitVec 64) (k i : Nat) (hi : i < 2 ^ (k - scalarChunkExp a k))
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : a.toNat + 2 ^ k ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    SplitReadChunk σ a (2 ^ scalarChunkExp a k) i
      (bytesT σ.mem (a.toNat + i * 2 ^ scalarChunkExp a k) (2 ^ scalarChunkExp a k)) := by
  have hf := scalarChunkFacts a k i hi hlo hhi hhtif
  refine ⟨?_, ?_, ?_⟩
  · rw [ramChunkAddress_scalar]
    exact pmp_allows σ _ _ _ initPmpaddr hg.pmpcfg_n hg.pmpaddr_n
  · rw [ramChunkAddress_scalar]
    exact within_mmio_readable_ram_false_width σ _ _ hg.htif_tohost_base
      hf.ram_lo hf.ram_hi hf.htif
  · rw [ramChunkAddress_scalar]
    have h := read_ram_total σ (scalarChunkAddress a k i) (2 ^ scalarChunkExp a k)
    rw [hf.address] at h
    exact h

/-- Every scalar RAM read succeeds with its total bytes, including misaligned
and granule-crossing addresses. No data-alignment premise is required. -/
theorem checked_mem_read_ram_scalar {σ : Vsa.Machine.MState} (hg : GoodState σ)
    (a : BitVec 64) (k : Nat) (hk : k ≤ 3)
    (hlo : 0x80000000 ≤ a.toNat) (hhi : a.toNat + 2 ^ k ≤ 0x100000000)
    (hhtif : a.toNat + 2 ^ k ≤ tohostAddr ∨ tohostAddr + 8 ≤ a.toNat) :
    (checked_mem_read (MemoryAccessType.Load mem_payload.Data)
      page_based_mem_type.PBMT_PMA Privilege.Machine (physaddr.Physaddr a)
      (2 ^ k) false false false false).run σ = .ok (.Ok (bytesT σ.mem a.toNat (2 ^ k), ())) σ := by
  have hw : 2 ^ k ≤ 8 := Nat.le_trans (Nat.pow_le_pow_right (by decide) hk) (by decide)
  by_cases hs : ramReadSingle a (2 ^ k) = true
  · exact checked_mem_read_single_of_ram σ a (2 ^ k) _ (Nat.two_pow_pos _)
      (RamReadChecks.of_good hg a (2 ^ k) hlo hhi hhtif hw hs) (read_ram_total σ a (2 ^ k))
  · have hf := scalarSplitFacts a k
    apply checked_mem_read_split_total σ a (2 ^ k) (2 ^ (k - scalarChunkExp a k))
      (2 ^ scalarChunkExp a k) (ramReadInfo a (2 ^ k)) hf.chunk_pos hf.complete
    · refine ⟨hf.count_pos, pmaCheck_ram_scalar σ a (2 ^ k) hg.pma_regions hlo hhi hw, ?_⟩
      have hp := split_misaligned_ram σ a (2 ^ k)
      simp only [hs] at hp
      rw [hp]
      exact split_access_scalar σ a k hk
    · intro i hi
      exact SplitReadChunk.of_scalar hg a k i hi hlo hhi hhtif

#print axioms checked_mem_read_split_total
#print axioms ramChunkAddress_scalar
#print axioms SplitReadChunk.of_scalar
#print axioms checked_mem_read_ram_scalar
end Vsa.Sim
