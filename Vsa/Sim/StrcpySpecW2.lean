import Vsa.Sim.StrcpySpecW

/-!
# Layer 3 — `strcpy` aligned word-path composition (`strcpy_word_spec`, `strcpy_full_spec`)

Builds on the verified infrastructure in `StrcpySpecW.lean`.  Composes the word-loop
body (`iterCpw`), the loop branch (`0xe20 beq a5,a6`), the one-time magic setup +
entry test (`0xdd0…0xdfc`), the `Triple.loop` rule, the ≤7-byte byte tail, and the
top-level specs.

## Note on the loop state predicates

`StrcpySpecW.WHeadCpw` / `WStoreMid` (as provided) pin `c.σ.mem = m0` while ALSO
asserting `MemInv … m0 c.σ.mem` — consistent only when memory never changes, which
fails after the word `sd`.  We therefore define our own `WHead2Cpy` / `WMid2` that track
the *pristine* ghost `m0` through the `memcpy`-style `MemInv dst src (len+1) bs i m0
mem` (copied prefix / outside untouched / source intact), exactly like the byte-head
path's `CpyInv`.  The loaded word `a4` is phrased against the ghost `m0`; that the
current-memory word agrees is recovered from `MemInv.src_intact`.

## Word loop control flow

```
e00: addi a1,a1,8         ; a1 = src+8(j+1)
e04: sd   a4,0(a2)        ; store current NUL-free word a4 at a2 = dst+8j
e08: ld   a4,0(a1)        ; a4 = next source word (cwordAtW m0 (src+8(j+1)))
e0c: addi a2,a2,8         ; a2 = dst+8(j+1)
e10..e1c: a5 = strlenWordVal a4   (recompute magic on the NEW word)
e20: beq  a5,a6,0x80006e00 ; a6 = allOnes throughout; loop iff next word NUL-free
```
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr (CStr CString Mem)
open Vsa.Sim.Code (StrcpyLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## `StrcpyLoaded` preserved by an 8-byte `sdMem8` insert chain outside the code -/

/-- Code stays loaded across the 8-byte `sdMem8` insert chain at address `a`
(each of the 8 keys lies outside the `strcpy` code region). -/
theorem strcpy_loaded_sdMem8 (mem : Std.ExtHashMap Nat (BitVec 8)) (a : BitVec 64)
    (word : BitVec 64)
    (hcode : ∀ k, k < 8 → a.toNat + k < 0x80006dc4 ∨ 0x80006ea0 ≤ a.toNat + k)
    (h : StrcpyLoaded mem) :
    StrcpyLoaded (sdMem8 mem a word) := by
  simp only [sdMem8]
  exact
    strcpy_loaded_insert _ _ _ (hcode 7 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 6 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 5 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 4 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 3 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 2 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 1 (by omega))
    (strcpy_loaded_insert _ _ _ (hcode 0 (by omega)) h)))))))

/-! ## The current-memory word equals the ghost word (source intact) -/

/-- Under `MemInv … (8j) m0 mem` (source disjoint from dst via `CpwRegions`) with
`8j ≤ len`, the CURRENT-memory source word at `src+8j` equals the ghost word
`cwordAtW m0 (src+8j)`.  Each byte `q = 8j+k`: for `q ≤ len` the source is intact
(`src_intact`); for `q > len` the address is outside `[dst,dst+len]` (disjoint), so
`outside` gives agreement with `m0`. -/
theorem cwordAtW_meminv (dst src : BitVec 64) (len : Nat) (m0 mem : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (j : Nat) (hstrb : StrBytes m0 src len bs) (hnf : 8*j ≤ len)
    (hreg : CpwRegions dst src len)
    (hinv : MemInv dst src (len + 1) bs (8*j) m0 mem) :
    strlenWordAt mem (src.toNat + 8*j) = cwordAtW m0 (src.toNat + 8*j) := by
  have hkey : ∀ k, k < 8 → (mem[src.toNat + 8*j + k]?).getD 0 = (m0[src.toNat + 8*j + k]?).getD 0 := by
    intro k hk
    by_cases hq : 8*j + k ≤ len
    · have hm : mem[(src.toNat + (8*j + k))]? = some (bs (8*j + k)) :=
        hinv.src_intact (8*j + k) (by omega) (by omega)
      have h0 : m0[(src.toNat + (8*j + k))]? = some (bs (8*j + k)) := by
        rcases Nat.lt_or_ge (8*j + k) len with h | h
        · exact (hstrb.chars (8*j + k) h).1
        · have : 8*j + k = len := by omega
          rw [this]; exact hstrb.nul
      rw [show src.toNat + 8*j + k = src.toNat + (8*j + k) from by omega, hm, h0]
    · -- q = 8j+k > len: address src+q is outside [dst, dst+len] (disjoint regions)
      have hout : mem[(src.toNat + (8*j + k))]? = m0[(src.toNat + (8*j + k))]? := by
        apply hinv.outside
        have hd := hreg.disjoint
        rcases hd with hd | hd
        · right; omega
        · left; omega
      rw [show src.toNat + 8*j + k = src.toNat + (8*j + k) from by omega, hout]
  have hkey0 : (mem[src.toNat + 8*j]?).getD 0 = (m0[src.toNat + 8*j]?).getD 0 := by
    have := hkey 0 (by omega); simpa using this
  show strlenWordAt mem (src.toNat + 8*j) = strlenWordAt m0 (src.toNat + 8*j)
  simp only [strlenWordAt]
  rw [hkey0, hkey 1 (by omega), hkey 2 (by omega), hkey 3 (by omega),
      hkey 4 (by omega), hkey 5 (by omega), hkey 6 (by omega), hkey 7 (by omega)]

/-! ## Per-iteration bounds for the word loop -/

/-- The `sd a4,0(a2)` store at `a2 = dst+8j`: effective address `dst+8j`, in RAM,
above the HTIF window, 8-aligned. -/
theorem cpw_dst_store_bounds (dst src : BitVec 64) (len j : Nat) (hreg : CpwRegions dst src len)
    (hj : 8 * j + 8 ≤ len + 1) :
    (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j ∧
    0x80000000 ≤ ((dst + BitVec.ofNat 64 (8 * j)) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((dst + BitVec.ofNat 64 (8 * j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    tohostAddr + 16 ≤ ((dst + BitVec.ofNat 64 (8 * j)) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((dst + BitVec.ofNat 64 (8 * j)) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have htn : (dst + BitVec.ofNat 64 (8 * j)).toNat = dst.toNat + 8 * j :=
    ptrCpw_toNat dst j (by have := hreg.dst_nowrap; omega)
  have hsb : ((dst + BitVec.ofNat 64 (8 * j)) + sign_extend (m := 64) (0x000#12)).toNat
      = dst.toNat + 8 * j := by rw [addCpw_sext0]; exact htn
  have hlo := hreg.dst_lo; have hhi := hreg.dst_hi; have hwin := hreg.dst_win
  have hda := hreg.dst_align
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, by rw [hsb]; omega, by rw [hsb]; omega, by rw [hsb]; omega, by rw [hsb]; omega⟩

/-- The `ld a4,0(a1)` load at `a1 = src+8(j+1)`: effective address `src+8(j+1)`, in
RAM, HTIF-disjoint, 8-aligned. -/
theorem cpw_src_load_bounds (dst src : BitVec 64) (len j : Nat) (hreg : CpwRegions dst src len)
    (hj : 8 * (j + 1) ≤ len) :
    (src + BitVec.ofNat 64 (8 * (j + 1))).toNat = src.toNat + 8 * (j + 1) ∧
    0x80000000 ≤ ((src + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((src + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    (((src + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨
       tohostAddr + 8 ≤ ((src + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0x000#12)).toNat) ∧
    ((src + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have htn : (src + BitVec.ofNat 64 (8 * (j + 1))).toNat = src.toNat + 8 * (j + 1) :=
    ptrCpw_toNat src (j + 1) (by have := hreg.src_nowrap; omega)
  have hsb : ((src + BitVec.ofNat 64 (8 * (j + 1))) + sign_extend (m := 64) (0x000#12)).toNat
      = src.toNat + 8 * (j + 1) := by rw [addCpw_sext0]; exact htn
  have hlo := hreg.src_lo; have hhi := hreg.src_hi; have hwin := hreg.src_win
  have hsa := hreg.src_align
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, by rw [hsb]; omega, by rw [hsb]; omega, Or.inr (by rw [hsb]; omega), by rw [hsb]; omega⟩

/-! ## Loop state predicates (pristine-`m0` tracking)

`WHead2Cpy` (at `0xe00`, word iteration `j`, CURRENT word `a4` already known NUL-free so
`8j+8 ≤ len`): `a1 = src+8j`, `a2 = dst+8j`, `a3 = magic7f`, `a4 = ghost word`,
`a6 = allOnes`, copied prefix `MemInv … (8j) m0 mem`.

`WMid2` (at `0xe20`, pre-`beq`): pointers at `8(j+1)`, NEXT word loaded into `a4`,
`a5 = strlenWordVal (next word)`, `MemInv … (8(j+1))`, and `8(j+1) ≤ len`. -/
structure WHead2Cpy (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006e00#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*j))
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*j))
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (cwordAtW m0 (src.toNat + 8*j))
  a6 : c.σ.regs.get? Register.x16 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  nulfree : 8*j + 8 ≤ len
  meminv : MemInv dst src (len + 1) bs (8*j) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

structure WMid2 (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006e20#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*(j+1)))
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*(j+1)))
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (cwordAtW m0 (src.toNat + 8*(j+1)))
  a5 : c.σ.regs.get? Register.x15 = some (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1))))
  a6 : c.σ.regs.get? Register.x16 = some (BitVec.allOnes 64)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  jle : 8*(j+1) ≤ len
  meminv : MemInv dst src (len + 1) bs (8*(j+1)) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-! ## One word-loop body iteration (`0x80006e00 → 0x80006e20`) : `iterCpw` -/
theorem iterCpw (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (j : Nat)
    (hnext : 8 * (j + 1) ≤ len) :
    Triple (WHead2Cpy g r dst src len m0 bs j) (WMid2 g r dst src len m0 bs j) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha6, hra, ⟨vmi, hmi⟩, htick,
    hreg, hstrb, hnulfree, hminv, hframe⟩ := hSt
  obtain ⟨hstn, hslo, hshi, hshtif, hsalign⟩ := cpw_src_load_bounds dst src len j hreg (by omega)
  obtain ⟨hdtn, hdlo, hdhi, hdwin, hdalign⟩ := cpw_dst_store_bounds dst src len j hreg (by omega)
  -- current word (a4) as ghost ldData8
  have hword_ghost : cwordAtW m0 (src.toNat + 8 * j)
      = ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
                (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7)) :=
    loadedWord_eq_ghost m0 src len bs hstrb j hnulfree
  -- === e00: addi a1,a1,8 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006e00 c.σ c.tick c.steps (0x80006e00#64) vmi (src + BitVec.ofNat 64 (8*j))
      hgood hpc hmi ha1 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006e04#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006e00#64) 4 = (0x80006e04#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha2_1 := obs_alu_other hobs1 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2
  have ha3_1 := obs_alu_other hobs1 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3
  have ha4_1 := obs_alu_other hobs1 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4
  have ha6_1 := obs_alu_other hobs1 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha1_1 : σ1.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*(j+1))) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptrCpw_word_succ src j] at this
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === e04: sd a4,0(a2) === (a2 = dst+8j, a4 = current word)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006e04 σ1 i1 (c.steps + 1) (0x80006e04#64) vmi1 (dst + BitVec.ofNat 64 (8*j))
      (cwordAtW m0 (src.toNat + 8*j))
      hG1 hpc1 hmi1' ha2_1 ha4_1 (by rw [hmem1]; exact hloaded) rfl hdlo hdhi hdwin hdalign hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006e08#64 : BitVec 64) := by
    have := obs_store_pc hobs2; rwa [show BitVec.addInt (0x80006e04#64) 4 = (0x80006e08#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_store_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_store_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have ha2_2 := obs_store_other hobs2 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_1
  have ha3_2 := obs_store_other hobs2 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_1
  have ha4_2 := obs_store_other hobs2 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_1
  have ha6_2 := obs_store_other hobs2 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_1
  have hra_2 := obs_store_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  obtain ⟨vmi2, hmi2'⟩ := obs_store_minstret hobs2
  -- the store's post map, as sdMem8 at dst+8j
  have hstore_mem : σ2.mem
      = sdMem8 c.σ.mem (dst + BitVec.ofNat 64 (8*j)) (cwordAtW m0 (src.toNat + 8*j)) := by
    rw [hmem2, mem_afterNextPC, hmem1, sdMemCpy_eq_sdMem8, addCpw_sext0]
  -- code stays loaded across the store
  have hloaded2 : StrcpyLoaded σ2.mem := by
    rw [hstore_mem]
    refine strcpy_loaded_sdMem8 c.σ.mem _ _ ?_ hloaded
    intro k hk
    have hcode := hreg.code_disjoint
    rw [hdtn]; omega
  -- the store extends the copied prefix to 8(j+1)
  have hminv2 : MemInv dst src (len + 1) bs (8*(j+1)) m0 σ2.mem := by
    rw [hstore_mem]
    have hbridge : sdMem8 c.σ.mem (dst + BitVec.ofNat 64 (8*j)) (cwordAtW m0 (src.toNat + 8*j))
        = sdMem8 c.σ.mem (dst + BitVec.ofNat 64 (8*j))
            (sign_extend (m := 64)
              (ldData8 (bs (8*j)) (bs (8*j+1)) (bs (8*j+2)) (bs (8*j+3))
                       (bs (8*j+4)) (bs (8*j+5)) (bs (8*j+6)) (bs (8*j+7)))) := by
      rw [hword_ghost, sext64_self]
    rw [hbridge]
    exact cpw_store8 dst src len bs j m0 c.σ.mem hreg (by omega) hdtn hminv
  -- === e08: ld a4,0(a1) === (a1 = src+8(j+1))
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006e08 σ2 i2 (c.steps + 1 + 1) (0x80006e08#64) vmi2 (src + BitVec.ofNat 64 (8*(j+1)))
      hG2 hpc2 hmi2' ha1_2 hloaded2 rfl hslo hshi hshtif hsalign hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006e0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006e08#64) 4 = (0x80006e0c#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha2_3 := obs_alu_other hobs3 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_2
  have ha3_3 := obs_alu_other hobs3 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_2
  have ha6_3 := obs_alu_other hobs3 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  -- newly loaded a4 = ghost next word
  have ha4_next : σ3.regs.get? Register.x14 = some (cwordAtW m0 (src.toNat + 8*(j+1))) := by
    have hrd := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hrd, sext64_self, addCpw_sext0, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hstn]
    exact congrArg some (cwordAtW_meminv dst src len m0 σ2.mem bs (j+1) hstrb hnext hreg hminv2)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === e0c: addi a2,a2,8 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006e0c σ3 i3 (c.steps + 1 + 1 + 1) (0x80006e0c#64) vmi3 (dst + BitVec.ofNat 64 (8*j))
      hG3 hpc3 hmi3' ha2_3 (by rw [hmem3]; exact hloaded2) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006e10#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006e0c#64) 4 = (0x80006e10#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have ha3_4 := obs_alu_other hobs4 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_3
  have ha4_4 := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_next
  have ha6_4 := obs_alu_other hobs4 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have ha2_4 : σ4.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*(j+1))) := by
    have := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [ptrCpw_word_succ dst j] at this
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === e10: and a5,a4,a3 ===
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006e10 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006e10#64) vmi4
      (cwordAtW m0 (src.toNat + 8*(j+1))) magic7f
      hG4 hpc4 hmi4' ha4_4 ha3_4 (by rw [hmem4, hmem3]; exact hloaded2) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006e14#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006e10#64) 4 = (0x80006e14#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have ha2_5 := obs_alu_other hobs5 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_4
  have ha3_5 := obs_alu_other hobs5 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_4
  have ha4_5 := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_4
  have ha6_5 := obs_alu_other hobs5 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_4
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have ha5_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === e14: add a5,a5,a3 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006e14 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006e14#64) vmi5
      (cwordAtW m0 (src.toNat + 8*(j+1)) &&& magic7f) magic7f
      hG5 hpc5 hmi5' ha5_5 ha3_5 (by rw [hmem5, hmem4, hmem3]; exact hloaded2) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006e18#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006e14#64) 4 = (0x80006e18#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have ha1_6 := obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_5
  have ha2_6 := obs_alu_other hobs6 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_5
  have ha3_6 := obs_alu_other hobs6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_5
  have ha4_6 := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_5
  have ha6_6 := obs_alu_other hobs6 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_5
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have ha5_6 := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  -- === e18: or a5,a5,a4 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006e18 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006e18#64) vmi6
      ((cwordAtW m0 (src.toNat + 8*(j+1)) &&& magic7f) + magic7f) (cwordAtW m0 (src.toNat + 8*(j+1)))
      hG6 hpc6 hmi6' ha5_6 ha4_6 (by rw [hmem6, hmem5, hmem4, hmem3]; exact hloaded2) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006e1c#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006e18#64) 4 = (0x80006e1c#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have ha1_7 := obs_alu_other hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_6
  have ha2_7 := obs_alu_other hobs7 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_6
  have ha3_7 := obs_alu_other hobs7 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_6
  have ha4_7 := obs_alu_other hobs7 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_6
  have ha6_7 := obs_alu_other hobs7 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_6
  have hra_7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have ha5_7 := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  -- === e1c: or a5,a5,a3 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006e1c σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006e1c#64) vmi7
      (((cwordAtW m0 (src.toNat + 8*(j+1)) &&& magic7f) + magic7f) ||| cwordAtW m0 (src.toNat + 8*(j+1))) magic7f
      hG7 hpc7 hmi7' ha5_7 ha3_7 (by rw [hmem7, hmem6, hmem5, hmem4, hmem3]; exact hloaded2) rfl hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006e20#64 : BitVec 64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006e1c#64) 4 = (0x80006e20#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_alu_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7
  have ha1_8 := obs_alu_other hobs8 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_7
  have ha2_8 := obs_alu_other hobs8 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_7
  have ha3_8 := obs_alu_other hobs8 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_7
  have ha4_8 := obs_alu_other hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_7
  have ha6_8 := obs_alu_other hobs8 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_7
  have hra_8 := obs_alu_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7
  have ha5_8 : σ8.regs.get? Register.x15 = some (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1)))) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, strcpyWordVal_eq]
  obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
  have hmem8eq : σ8.mem = σ2.mem := by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3]
  have hsteps : Steps c ⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    ((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8))
  refine ⟨⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩, hsteps,
    hG8, by rw [hmem8eq]; exact hloaded2, hpc8, ha0_8, ha1_8, ha2_8, ha3_8, ha4_8, ha5_8, ha6_8,
    hra_8, ⟨vmi8, hmi8'⟩, hi8, hreg, hstrb, by omega, by rw [hmem8eq]; exact hminv2, ?_⟩
  -- frame: thread g through all 8 body steps
  intro R hR
  have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_cpw hobs1 R hR.x11 hR
  have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_store_cpw hobs2 R hR
  have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_cpw hobs3 R hR.x14 hR
  have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_alu_cpw hobs4 R hR.x12 hR
  have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_alu_cpw hobs5 R hR.x15 hR
  have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_cpw hobs6 R hR.x15 hR
  have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_alu_cpw hobs7 R hR.x15 hR
  have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_alu_cpw hobs8 R hR.x15 hR
  rw [e8, e7, e6, e5, e4, e3, e2, e1]; exact hframe R hR

/-! ## Byte-tail entry state `WTailCpw` (at `0x80006e24`)

Reached either from the entry test `bne a6,a5` at `0xdfc` (word 0 has a NUL) or from
the loop branch `beq a5,a6` not-taken at `0xe20` (word `p` has a NUL).  Word iteration
`p`: `a1 = src+8p`, `a2 = dst+8p`, `a4 = word` (`= cwordAtW m0 (src+8p)`, containing the
NUL), copied prefix `MemInv … (8p)`, and `8p ≤ len < 8p+8` (the NUL is at offset
`t = len - 8p ∈ [0,7]`).  `a3 = magic7f`, `a6 = allOnes`, `a5 = strlenWordVal word` (≠
allOnes). -/
structure WTailCpw (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (p : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006e24#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some (src + BitVec.ofNat 64 (8*p))
  a2 : c.σ.regs.get? Register.x12 = some (dst + BitVec.ofNat 64 (8*p))
  a4 : c.σ.regs.get? Register.x14 = some (cwordAtW m0 (src.toNat + 8*p))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  plo : 8*p ≤ len
  phi : len < 8*p + 8
  meminv : MemInv dst src (len + 1) bs (8*p) m0 c.σ.mem
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-! ## The loop branch `beq a5,a6` at `0x80006e20`

`a5 = strlenWordVal (next word)`, `a6 = allOnes`.  Taken iff the next word is NUL-free
(`8(j+1)+8 ≤ len`) → back to `WHead2Cpy (j+1)`.  Not-taken iff the next word has the NUL
(`8(j+1) ≤ len < 8(j+1)+8`) → byte tail `WTailCpw (j+1)`. -/

/-- Loop branch taken: next word NUL-free, back-edge to `WHead2Cpy (j+1)`. -/
theorem tr_beq_back (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (j : Nat)
    (hnf : 8*(j+1) + 8 ≤ len) :
    Triple (WMid2 g r dst src len m0 bs j) (WHead2Cpy g r dst src len m0 bs (j+1)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hra, ⟨vmi, hmi⟩, htick,
    hreg, hstrb, hjle, hminv, hframe⟩ := hSt
  -- a5 = allOnes (next word NUL-free)
  have hnfree : strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1))) = BitVec.allOnes 64 :=
    wordW_nul_free m0 src len bs hstrb (j+1) hnf
  have hv : (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1))) == BitVec.allOnes 64) = true := by
    rw [hnfree]; simp
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006e20_taken c.σ c.tick c.steps (0x80006e20#64) vmi
      (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1)))) (BitVec.allOnes 64)
      hgood hpc hmi ha5 ha6 hloaded rfl hv htick
  have hpceq : (0x80006e20#64 : BitVec 64) + sign_extend (m := 64) (0x1fe0#13) = (0x80006e00#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, ?_,
    obs_btaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_btaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_btaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2,
    obs_btaken_other hobs Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3,
    obs_btaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_btaken_other hobs Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6,
    obs_btaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, hstrb, by omega, by rw [hmem']; exact hminv,
    fun R hR => (frame_btaken_cpw hobs R hR).trans (hframe R hR)⟩
  rw [obs_btaken_pc hobs, hpceq]

/-- Loop branch not-taken: next word has the NUL, exit to byte tail `WTailCpw (j+1)`. -/
theorem tr_beq_tail (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (j : Nat)
    (hlo : 8*(j+1) ≤ len) (hhi : len < 8*(j+1) + 8) :
    Triple (WMid2 g r dst src len m0 bs j) (WTailCpw g r dst src len m0 bs (j+1)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, ha2, ha3, ha4, ha5, ha6, hra, ⟨vmi, hmi⟩, htick,
    hreg, hstrb, hjle, hminv, hframe⟩ := hSt
  have hhasnul : strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1))) ≠ BitVec.allOnes 64 :=
    wordW_has_nul m0 src len bs hstrb (j+1) hlo hhi
  have hv : (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1))) == BitVec.allOnes 64) = false := by
    rw [beq_eq_false_iff_ne]; exact hhasnul
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006e20_nottaken c.σ c.tick c.steps (0x80006e20#64) vmi
      (strlenWordVal (cwordAtW m0 (src.toNat + 8*(j+1)))) (BitVec.allOnes 64)
      hgood hpc hmi ha5 ha6 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006e24#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006e20#64) 4 = (0x80006e24#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, hpc',
    obs_bnottaken_other hobs Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0,
    obs_bnottaken_other hobs Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1,
    obs_bnottaken_other hobs Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2,
    obs_bnottaken_other hobs Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4,
    obs_bnottaken_other hobs Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, hstrb, hjle, by omega, by rw [hmem']; exact hminv,
    fun R hR => (frame_bnottaken_cpw hobs R hR).trans (hframe R hR)⟩

/-! ## One-time entry: magic setup `0xdd0…0xdf8` + entry test `bne a6,a5` at `0xdfc`

`PreWord` is the word-path entry at `0x80006dd0`: `a0 = dst`, `a1 = src`, `mem = m0`
(nothing copied yet).  The straight-line magic block builds `a3 = magic7f`, loads word
0 into `a4`, sets `a5 = allOnes`, `a6 = strlenWordVal word0`, `a2 = dst`.  Then
`bne a6,a5` at `0xdfc`: not-taken (word 0 NUL-free) → `WHead2Cpy 0`; taken (word 0 has a
NUL) → byte tail `WTailCpw 0`. -/
structure PreWord (g : (R : Register) → Option (RegisterType R))
    (r dst src : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (bs : Nat → BitVec 8) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrcpyLoaded c.σ.mem
  pc : c.σ.regs.get? Register.PC = some (0x80006dd0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some dst
  a1 : c.σ.regs.get? Register.x11 = some src
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : CpwRegions dst src len
  strbytes : StrBytes m0 src len bs
  memeq : c.σ.mem = m0
  hframe : ∀ R : Register, NotWrittenCpw R → c.σ.regs.get? R = g R

/-- `MemInv … 0 m0 m0`: at the entry nothing is copied, `mem = m0`.  `src_intact`
follows from `StrBytes` (byte `k ≤ len` reads `bs k`). -/
theorem meminv_entry (dst src : BitVec 64) (len : Nat) (bs : Nat → BitVec 8)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hstrb : StrBytes m0 src len bs) :
    MemInv dst src (len + 1) bs 0 m0 m0 :=
  ⟨fun k hk => absurd hk (Nat.not_lt_zero k), fun _ _ => rfl,
    fun k _ hkn => by
      rcases Nat.lt_or_ge k len with h | h
      · exact (hstrb.chars k h).1
      · have : k = len := by omega
        rw [this]; exact hstrb.nul⟩

/-- Src-load bounds at word 0 (`a1 = src`). -/
theorem cpw_src0_bounds (dst src : BitVec 64) (len : Nat) (hreg : CpwRegions dst src len) :
    0x80000000 ≤ (src + sign_extend (m := 64) (0x000#12)).toNat ∧
    (src + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    ((src + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr ∨
       tohostAddr + 8 ≤ (src + sign_extend (m := 64) (0x000#12)).toNat) ∧
    (src + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have hsb : (src + sign_extend (m := 64) (0x000#12)).toNat = src.toNat := by rw [addCpw_sext0]
  have hlo := hreg.src_lo; have hhi := hreg.src_hi; have hwin := hreg.src_win
  have hsa := hreg.src_align
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by rw [hsb]; omega, by rw [hsb]; omega, Or.inr (by rw [hsb]; omega), by rw [hsb]; omega⟩

/-- The magic setup + entry test, producing the word-0 dispatch disjunction. -/
theorem entry_wordCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreWord g r dst src len m0 bs)
      (fun c => (8 ≤ len ∧ WHead2Cpy g r dst src len m0 bs 0 c) ∨
                (len < 8 ∧ WTailCpw g r dst src len m0 bs 0 c)) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hpc, ha0, ha1, hra, ⟨vmi, hmi⟩, htick, hreg, hstrb, hmemeq, hframe⟩ := hPre
  obtain ⟨hs0lo, hs0hi, hs0htif, hs0align⟩ := cpw_src0_bounds dst src len hreg
  -- === dd0: lui a5 ===
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006dd0 c.σ c.tick c.steps (0x80006dd0#64) vmi hgood hpc hmi hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006dd4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006dd0#64) 4 = (0x80006dd4#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other hobs1 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0
  have ha1_1 := obs_alu_other hobs1 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1
  have hra_1 := obs_alu_other hobs1 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  rw [magicCpw_lui] at ha5_1
  -- === dd4: addi a5,a5,-129 ===
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006dd4 σ1 i1 (c.steps + 1) (0x80006dd4#64) vmi1 (0x7f7f8000#64)
      hG1 hpc1 hmi1' ha5_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006dd8#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006dd4#64) 4 = (0x80006dd8#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other hobs2 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_1
  have ha1_2 := obs_alu_other hobs2 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_1
  have hra_2 := obs_alu_other hobs2 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [magicCpw_addi] at ha5_2
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === dd8: ld a4,0(a1) ===  a1 = src
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006dd8 σ2 i2 (c.steps + 1 + 1) (0x80006dd8#64) vmi2 src
      hG2 hpc2 hmi2' ha1_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hs0lo hs0hi hs0htif hs0align hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006ddc#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006dd8#64) 4 = (0x80006ddc#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other hobs3 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_2
  have ha1_3 := obs_alu_other hobs3 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_2
  have ha5_3 := obs_alu_other hobs3 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_2
  have hra_3 := obs_alu_other hobs3 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_2
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  have ha4_3 : σ3.regs.get? Register.x14 = some (cwordAtW m0 src.toNat) := by
    have hrd := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [hrd, sext64_self, addCpw_sext0, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem2, hmem1, hmemeq]
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === ddc: slli a3,a5,0x20 ===
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006ddc σ3 i3 (c.steps + 1 + 1 + 1) (0x80006ddc#64) vmi3 (0x7f7f7f7f#64)
      hG3 hpc3 hmi3' ha5_3 (by rw [hmem3eq]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006de0#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006ddc#64) 4 = (0x80006de0#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other hobs4 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_3
  have ha1_4 := obs_alu_other hobs4 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_3
  have ha4_4 := obs_alu_other hobs4 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_3
  have ha5_4 := obs_alu_other hobs4 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_3
  have hra_4 := obs_alu_other hobs4 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_3
  have ha3_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [magicCpw_slli] at ha3_4
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === de0: add a3,a3,a5 ===  a3 = magic7f
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006de0 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006de0#64) vmi4
      (0x7f7f7f7f00000000#64) (0x7f7f7f7f#64)
      hG4 hpc4 hmi4' ha3_4 ha5_4 (by rw [hmem4, hmem3eq]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006de4#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006de0#64) 4 = (0x80006de4#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other hobs5 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_4
  have ha1_5 := obs_alu_other hobs5 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_4
  have ha4_5 := obs_alu_other hobs5 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_4
  have hra_5 := obs_alu_other hobs5 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_4
  have ha3_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  rw [magicCpw_add] at ha3_5
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === de4: and a6,a4,a3 ===
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006de4 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006de4#64) vmi5
      (cwordAtW m0 src.toNat) magic7f
      hG5 hpc5 hmi5' ha4_5 ha3_5 (by rw [hmem5, hmem4, hmem3eq]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006de8#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006de4#64) 4 = (0x80006de8#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other hobs6 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_5
  have ha1_6 := obs_alu_other hobs6 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_5
  have ha3_6 := obs_alu_other hobs6 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_5
  have ha4_6 := obs_alu_other hobs6 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_5
  have hra_6 := obs_alu_other hobs6 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_5
  have ha6_6 := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  -- === de8: add a6,a6,a3 ===
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006de8 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006de8#64) vmi6
      (cwordAtW m0 src.toNat &&& magic7f) magic7f
      hG6 hpc6 hmi6' ha6_6 ha3_6 (by rw [hmem6, hmem5, hmem4, hmem3eq]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006dec#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006de8#64) 4 = (0x80006dec#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other hobs7 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_6
  have ha1_7 := obs_alu_other hobs7 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_6
  have ha3_7 := obs_alu_other hobs7 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_6
  have ha4_7 := obs_alu_other hobs7 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_6
  have hra_7 := obs_alu_other hobs7 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_6
  have ha6_7 := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  -- === dec: or a6,a6,a4 ===
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006dec σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006dec#64) vmi7
      ((cwordAtW m0 src.toNat &&& magic7f) + magic7f) (cwordAtW m0 src.toNat)
      hG7 hpc7 hmi7' ha6_7 ha4_7 (by rw [hmem7, hmem6, hmem5, hmem4, hmem3eq]; exact hloaded) rfl hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006df0#64 : BitVec 64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006dec#64) 4 = (0x80006df0#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_alu_other hobs8 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_7
  have ha1_8 := obs_alu_other hobs8 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_7
  have ha3_8 := obs_alu_other hobs8 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_7
  have ha4_8 := obs_alu_other hobs8 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_7
  have hra_8 := obs_alu_other hobs8 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_7
  have ha6_8 := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
  -- === df0: or a6,a6,a3 ===  a6 = strlenWordVal word0
  obtain ⟨σ9, i9, hs9, hi9, hG9, hmem9, hobs9⟩ :=
    site_80006df0 σ8 i8 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006df0#64) vmi8
      (((cwordAtW m0 src.toNat &&& magic7f) + magic7f) ||| cwordAtW m0 src.toNat) magic7f
      hG8 hpc8 hmi8' ha6_8 ha3_8 (by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3eq]; exact hloaded) rfl hi8
  have hpc9 : σ9.regs.get? Register.PC = some (0x80006df4#64 : BitVec 64) := by
    have := obs_alu_pc hobs9; rwa [show BitVec.addInt (0x80006df0#64) 4 = (0x80006df4#64 : BitVec 64) from by decide] at this
  have ha0_9 := obs_alu_other hobs9 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_8
  have ha1_9 := obs_alu_other hobs9 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_8
  have ha3_9 := obs_alu_other hobs9 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_8
  have ha4_9 := obs_alu_other hobs9 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_8
  have hra_9 := obs_alu_other hobs9 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_8
  have ha6_9 : σ9.regs.get? Register.x16 = some (strlenWordVal (cwordAtW m0 src.toNat)) := by
    have := obs_alu_rd hobs9 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this]
  obtain ⟨vmi9, hmi9'⟩ := obs_alu_minstret hobs9
  -- === df4: li a5,-1 ===  a5 = allOnes
  obtain ⟨σ10, i10, hs10, hi10, hG10, hmem10, hobs10⟩ :=
    site_80006df4 σ9 i9 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006df4#64) vmi9
      hG9 hpc9 hmi9' (by rw [hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3eq]; exact hloaded) rfl hi9
  have hpc10 : σ10.regs.get? Register.PC = some (0x80006df8#64 : BitVec 64) := by
    have := obs_alu_pc hobs10; rwa [show BitVec.addInt (0x80006df4#64) 4 = (0x80006df8#64 : BitVec 64) from by decide] at this
  have ha0_10 := obs_alu_other hobs10 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_9
  have ha1_10 := obs_alu_other hobs10 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_9
  have ha3_10 := obs_alu_other hobs10 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_9
  have ha4_10 := obs_alu_other hobs10 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_9
  have ha6_10 := obs_alu_other hobs10 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_9
  have hra_10 := obs_alu_other hobs10 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_9
  have ha5_10 : σ10.regs.get? Register.x15 = some (BitVec.allOnes 64) := by
    have := obs_alu_rd hobs10 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, liCpw_allOnes]
  obtain ⟨vmi10, hmi10'⟩ := obs_alu_minstret hobs10
  -- === df8: mv a2,a0 ===  a2 = dst
  obtain ⟨σ11, i11, hs11, hi11, hG11, hmem11, hobs11⟩ :=
    site_80006df8 σ10 i10 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006df8#64) vmi10 dst
      hG10 hpc10 hmi10' ha0_10 (by rw [hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3eq]; exact hloaded) rfl hi10
  have hpc11 : σ11.regs.get? Register.PC = some (0x80006dfc#64 : BitVec 64) := by
    have := obs_alu_pc hobs11; rwa [show BitVec.addInt (0x80006df8#64) 4 = (0x80006dfc#64 : BitVec 64) from by decide] at this
  have ha0_11 := obs_alu_other hobs11 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_10
  have ha1_11 := obs_alu_other hobs11 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_10
  have ha3_11 := obs_alu_other hobs11 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_10
  have ha4_11 := obs_alu_other hobs11 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_10
  have ha5_11 := obs_alu_other hobs11 Register.x15 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha5_10
  have ha6_11 := obs_alu_other hobs11 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_10
  have hra_11 := obs_alu_other hobs11 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_10
  have ha2_11 : σ11.regs.get? Register.x12 = some dst := by
    have := obs_alu_rd hobs11 (by decide) (by decide) (by decide) (by decide) (by decide)
    rw [this, addCpw_sext0]
  obtain ⟨vmi11, hmi11'⟩ := obs_alu_minstret hobs11
  have hmem11eq : σ11.mem = c.σ.mem := by
    rw [hmem11, hmem10, hmem9, hmem8, hmem7, hmem6, hmem5, hmem4, hmem3eq]
  have hframe11 : ∀ R : Register, NotWrittenCpw R → σ11.regs.get? R = g R := by
    intro R hR
    have e1 : σ1.regs.get? R = c.σ.regs.get? R := frame_alu_cpw hobs1 R hR.x15 hR
    have e2 : σ2.regs.get? R = σ1.regs.get? R := frame_alu_cpw hobs2 R hR.x15 hR
    have e3 : σ3.regs.get? R = σ2.regs.get? R := frame_alu_cpw hobs3 R hR.x14 hR
    have e4 : σ4.regs.get? R = σ3.regs.get? R := frame_alu_cpw hobs4 R hR.x13 hR
    have e5 : σ5.regs.get? R = σ4.regs.get? R := frame_alu_cpw hobs5 R hR.x13 hR
    have e6 : σ6.regs.get? R = σ5.regs.get? R := frame_alu_cpw hobs6 R hR.x16 hR
    have e7 : σ7.regs.get? R = σ6.regs.get? R := frame_alu_cpw hobs7 R hR.x16 hR
    have e8 : σ8.regs.get? R = σ7.regs.get? R := frame_alu_cpw hobs8 R hR.x16 hR
    have e9 : σ9.regs.get? R = σ8.regs.get? R := frame_alu_cpw hobs9 R hR.x16 hR
    have e10 : σ10.regs.get? R = σ9.regs.get? R := frame_alu_cpw hobs10 R hR.x15 hR
    have e11 : σ11.regs.get? R = σ10.regs.get? R := frame_alu_cpw hobs11 R hR.x12 hR
    rw [e11, e10, e9, e8, e7, e6, e5, e4, e3, e2, e1]; exact hframe R hR
  have hsteps11 : Steps c ⟨σ11, i11, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩ :=
    ((((((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8)).trans (Steps.single hs9)).trans
      (Steps.single hs10)).trans (Steps.single hs11)
  -- === dfc: bne a6,a5 ===  a6 = strlenWordVal word0, a5 = allOnes
  by_cases hnf0 : strlenWordVal (cwordAtW m0 src.toNat) = BitVec.allOnes 64
  · -- word 0 NUL-free → not-taken → WHead2Cpy 0
    have hlen : 8 ≤ len := by
      rcases Nat.lt_or_ge len 8 with hlt | hge
      · exfalso
        have hne := wordW_has_nul m0 src len bs hstrb 0 (by omega) (by omega)
        rw [Nat.mul_zero, Nat.add_zero] at hne
        exact hne hnf0
      · exact hge
    have hv : (strlenWordVal (cwordAtW m0 src.toNat) != BitVec.allOnes 64) = false := by
      rw [bne_eq_false_iff_eq]; exact hnf0
    obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
      site_80006dfc_nottaken σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (0x80006dfc#64) vmi11 (BitVec.allOnes 64) (strlenWordVal (cwordAtW m0 src.toNat))
        hG11 hpc11 hmi11' ha5_11 ha6_11 (by rw [hmem11eq]; exact hloaded) rfl hv hi11
    have hpc12 : σ12.regs.get? Register.PC = some (0x80006e00#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs12
      rwa [show BitVec.addInt (0x80006dfc#64) 4 = (0x80006e00#64 : BitVec 64) from by decide] at this
    refine ⟨⟨σ12, i12, _⟩, hsteps11.trans (Steps.single hs12), Or.inl ⟨by omega, ?_⟩⟩
    refine ⟨hG12, by rw [hmem12, hmem11eq]; exact hloaded, hpc12,
      obs_bnottaken_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_11,
      ?_, ?_, ?_, ?_, ?_,
      obs_bnottaken_other hobs12 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_11,
      obs_bnottaken_minstret hobs12, hi12, hreg, hstrb, by omega,
      by rw [hmem12, hmem11eq, hmemeq]; exact meminv_entry dst src len bs m0 hstrb,
      fun R hR => (frame_bnottaken_cpw hobs12 R hR).trans (hframe11 R hR)⟩
    · have h := obs_bnottaken_other hobs12 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_11
      rwa [show src = src + BitVec.ofNat 64 (8*0) from by simp] at h
    · have h := obs_bnottaken_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_11
      rwa [show dst = dst + BitVec.ofNat 64 (8*0) from by simp] at h
    · exact obs_bnottaken_other hobs12 Register.x13 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha3_11
    · have h := obs_bnottaken_other hobs12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_11
      rwa [show src.toNat = src.toNat + 8*0 from by omega] at h
    · have h := obs_bnottaken_other hobs12 Register.x16 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha6_11
      rwa [hnf0] at h
  · -- word 0 has the NUL → taken → WTailCpw 0
    have hlen : len < 8 := by
      rcases Nat.lt_or_ge len 8 with hlt | hge
      · exact hlt
      · exfalso
        have hfree := wordW_nul_free m0 src len bs hstrb 0 (by omega)
        rw [Nat.mul_zero, Nat.add_zero] at hfree
        exact hnf0 hfree
    have hv : (strlenWordVal (cwordAtW m0 src.toNat) != BitVec.allOnes 64) = true := by
      rw [bne_iff_ne]; exact hnf0
    obtain ⟨σ12, i12, hs12, hi12, hG12, hmem12, hobs12⟩ :=
      site_80006dfc_taken σ11 i11 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)
        (0x80006dfc#64) vmi11 (BitVec.allOnes 64) (strlenWordVal (cwordAtW m0 src.toNat))
        hG11 hpc11 hmi11' ha5_11 ha6_11 (by rw [hmem11eq]; exact hloaded) rfl hv hi11
    have hpc12 : σ12.regs.get? Register.PC = some (0x80006e24#64 : BitVec 64) := by
      rw [obs_btaken_pc hobs12]; apply congrArg; apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ12, i12, _⟩, hsteps11.trans (Steps.single hs12), Or.inr ⟨hlen, ?_⟩⟩
    refine ⟨hG12, by rw [hmem12, hmem11eq]; exact hloaded, hpc12,
      obs_btaken_other hobs12 Register.x10 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha0_11,
      ?_, ?_, ?_,
      obs_btaken_other hobs12 Register.x1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) hra_11,
      obs_btaken_minstret hobs12, hi12, hreg, hstrb, by omega, by omega,
      by rw [hmem12, hmem11eq, hmemeq]; exact meminv_entry dst src len bs m0 hstrb,
      fun R hR => (frame_btaken_cpw hobs12 R hR).trans (hframe11 R hR)⟩
    · have h := obs_btaken_other hobs12 Register.x11 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha1_11
      rwa [show src = src + BitVec.ofNat 64 (8*0) from by simp] at h
    · have h := obs_btaken_other hobs12 Register.x12 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha2_11
      rwa [show dst = dst + BitVec.ofNat 64 (8*0) from by simp] at h
    · have h := obs_btaken_other hobs12 Register.x14 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) ha4_11
      rwa [show src.toNat = src.toNat + 8*0 from by omega] at h

/-! ## Word-loop total-correctness rule (`Triple.loop`)

Loop invariant `LoopIWCpy`: at a NUL-free head `WHead2Cpy j` (`8j+8 ≤ len`) or at the byte
tail entry `WTailCpw p` (`8p ≤ len < 8p+8`).  Guard `LoopBWCpy`: at a head.  Measure
`LoopMuW = if PC = 0xe00 then len + 1 - 8j else 0` — PC-guarded so it is `0` at the
tail (not-taken) exit and `len+1-8j` at the head, strictly decreasing each iteration. -/

def AtHeadWCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  ∃ j, 8*j + 8 ≤ len ∧ WHead2Cpy g r dst src len m0 bs j c

def AtTailW (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  ∃ p, 8*p ≤ len ∧ len < 8*p + 8 ∧ WTailCpw g r dst src len m0 bs p c

def LoopIWCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadWCpy g r dst src len m0 bs c ∨ AtTailW g r dst src len m0 bs c

def LoopBWCpy (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64) (len : Nat)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (c : Config) : Prop :=
  AtHeadWCpy g r dst src len m0 bs c

/-- PC-guarded measure: `2^64 - a1.toNat` at the head (`a1 = src+8j` increments by 8
each iteration, no wrap, so strictly decreasing), `0` off the head (at the tail exit). -/
def LoopMuJ (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006e00#64 : BitVec 64)
  then 2^64 - (((c.σ.regs.get? Register.x11).getD (0#64)).toNat)
  else 0

/-- Loop body: from a guarded head `WHead2Cpy j` (`8j+8 ≤ len`), one iteration + branch
re-establishes `LoopIWCpy` strictly decreasing `LoopMuJ`.  The next word is NUL-free
(`8(j+1)+8 ≤ len`) → head `j+1`; else it holds the NUL (`8(j+1) ≤ len < 8(j+1)+8`) →
tail `j+1`. -/
theorem loop_body_w (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) (k : Nat) :
    Triple (fun c => LoopIWCpy g r dst src len m0 bs c ∧ LoopBWCpy g r dst src len m0 bs c ∧ LoopMuJ c = k)
           (fun c => LoopIWCpy g r dst src len m0 bs c ∧ LoopMuJ c < k) := by
  intro c hc
  obtain ⟨_, ⟨j, hjle, hHead⟩, hmu⟩ := hc
  have hreg := hHead.regions
  have hnw := hreg.src_nowrap
  -- measure at head j: a1 = src+8j, toNat = src.toNat + 8j
  have ha1tn : ((c.σ.regs.get? Register.x11).getD (0#64)).toNat = src.toNat + 8*j := by
    rw [hHead.a1]; simp only [Option.getD_some]
    exact ptrCpw_toNat src j (by omega)
  have hmu_eq : LoopMuJ c = 2^64 - (src.toNat + 8*j) := by
    simp only [LoopMuJ, hHead.pc, ha1tn, reduceIte]
  rw [hmu_eq] at hmu
  -- run iterCpw to WMid2 j
  obtain ⟨c1, hs1, hMid⟩ := iterCpw g r dst src len m0 bs j hjle c hHead
  -- dispatch on next word
  by_cases hnf : 8*(j+1) + 8 ≤ len
  · obtain ⟨c2, hs2, hHead2⟩ := tr_beq_back g r dst src len m0 bs j hnf c1 hMid
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨j+1, hnf, hHead2⟩, ?_⟩
    have ha1tn2 : ((c2.σ.regs.get? Register.x11).getD (0#64)).toNat = src.toNat + 8*(j+1) := by
      rw [hHead2.a1]; simp only [Option.getD_some]
      exact ptrCpw_toNat src (j+1) (by have := hHead2.regions.src_nowrap; omega)
    have hnw2 := hHead2.regions.src_nowrap
    have : LoopMuJ c2 = 2^64 - (src.toNat + 8*(j+1)) := by
      simp only [LoopMuJ, hHead2.pc, ha1tn2, reduceIte]
    rw [this]; omega
  · have hlo : 8*(j+1) ≤ len := hMid.jle
    have hhi : len < 8*(j+1) + 8 := by omega
    obtain ⟨c2, hs2, hTail⟩ := tr_beq_tail g r dst src len m0 bs j hlo hhi c1 hMid
    refine ⟨c2, hs1.trans hs2, Or.inr ⟨j+1, hlo, hhi, hTail⟩, ?_⟩
    -- tail PC is 0xe24, so measure = 0 < k
    have hz : LoopMuJ c2 = 0 := by
      simp only [LoopMuJ, hTail.pc]; rfl
    rw [hz]; omega

/-- The word loop runs to the byte-tail entry `AtTailW` (some `WTailCpw p`). -/
theorem loop_to_tail_w (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (LoopIWCpy g r dst src len m0 bs) (AtTailW g r dst src len m0 bs) := by
  have hloop := Triple.loop (I := LoopIWCpy g r dst src len m0 bs) (B := LoopBWCpy g r dst src len m0 bs)
    (LoopMuJ) (loop_body_w g r dst src len m0 bs)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hTail
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hTail⟩

/-! ## Word-path entry-to-tail composition

From the word-path entry `PreWord` (`0x80006dd0`), the machine reaches the byte-tail
entry `AtTailW` (some `WTailCpw p` at `0x80006e24`): the magic setup + entry test
either jumps straight to the tail (word 0 has the NUL, `len < 8`, `p = 0`) or enters
the word loop (word 0 NUL-free), which runs to the tail.  This is the full verified
prefix of the aligned path up to the ≤7-byte byte-copy tail. -/
theorem entry_to_tail (g : (R : Register) → Option (RegisterType R)) (r dst src : BitVec 64)
    (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (bs : Nat → BitVec 8) :
    Triple (PreWord g r dst src len m0 bs) (AtTailW g r dst src len m0 bs) := by
  refine (entry_wordCpy g r dst src len m0 bs).seq ?_
  intro c hc
  rcases hc with ⟨hlen, hHead⟩ | ⟨hlen, hTail⟩
  · -- word 0 NUL-free: enter the loop at head 0, run to tail
    exact loop_to_tail_w g r dst src len m0 bs c (Or.inl ⟨0, by omega, hHead⟩)
  · -- word 0 has the NUL: already at the tail (p = 0)
    exact ⟨c, .refl c, 0, by omega, by omega, hTail⟩

end Vsa.Sim
