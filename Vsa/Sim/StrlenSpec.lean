import Vsa.Sim.StrlenSites
import Vsa.Sim.StrlenMagic
import Vsa.Sim.Muldi3Spec
import Vsa.MemRepr
import Vsa.Triple
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strlen` total-correctness spec (`strlen_spec`)

Config-level (`Vsa.Logic.Triple`) composition of the per-site observational steps
(`Vsa/Sim/StrlenSites.lean`) and the magic-constant zero-byte detection arithmetic
(`Vsa/Sim/StrlenMagic.lean`) into a total-correctness triple for newlib `strlen`
(`[0x80006cf0, 0x80006dc4)`).

## Control flow (from the disassembly)

* entry `0xcf0..0xcfc`: `andi a5,a0,7; mv a4,a0; bnez a5,d78`.  Aligned ⇒ set up
  the magic mask and fall to the word loop; unaligned ⇒ jump to the head peel.
* magic setup `0xd00..0xd0c`: builds `a3 = 0x7f7f…7f`, `a1 = -1 = allOnes`.
* word loop `0xd10..0xd28`: `ld a2,0(a4); addi a4,a4,8;` compute
  `a5 = strlenWordVal a2`; `beq a5,a1,d10` (loop while no zero byte).
* byte tail `0xd2c..0xd70`: `lbu`/`beqz` ladder locating the NUL in the hit word.
* head peel `0xd74..0xd90`: byte-at-a-time until 8-aligned (own back-edge).
* exit blocks `0xd94..0xdc0`: `addi a0,a3,imm; ret` computing the length.

This file proves the pieces bottom-up.  See the end-of-file summary for exactly
what lands.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrlenLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## CStr byte facts

From `CStr m p cs`, the byte at `p + k` (`k < cs.length`) is the (nonzero) char,
and the byte at `p + cs.length` is `0`.  These bridge the string predicate to the
per-address `m[·]?` values the load chain consumes. -/

/-- The byte at offset `k < cs.length` in `CStr m p cs` is nonzero. -/
theorem cstr_byte_ne (m : Mem) : ∀ {p : Nat} {cs : List Char}, CStr m p cs →
    ∀ k, k < cs.length → ∃ b : BitVec 8, m[p + k]? = some b ∧ b ≠ 0 := by
  intro p cs h
  induction h with
  | @nil a hnil => intro k hk; simp at hk
  | @cons a b cs hb hbne hblt hrest ih =>
    intro k hk
    match k with
    | 0 => exact ⟨b, by simpa using hb, hbne⟩
    | k + 1 =>
      have hk' : k < cs.length := by simpa using hk
      obtain ⟨b', hb', hb'ne⟩ := ih k hk'
      exact ⟨b', by rw [show a + (k + 1) = (a + 1) + k from by omega]; exact hb', hb'ne⟩

/-- The byte at offset `cs.length` in `CStr m p cs` is the NUL terminator. -/
theorem cstr_byte_nul (m : Mem) : ∀ {p : Nat} {cs : List Char}, CStr m p cs →
    m[p + cs.length]? = some 0 := by
  intro p cs h
  induction h with
  | @nil a hnil => simpa using hnil
  | @cons a b cs hb hbne hblt hrest ih =>
    have : a + (cs.length + 1) = (a + 1) + cs.length := by omega
    simp only [List.length_cons]
    rw [this]; exact ih

/-- `CString m p s` gives a `cs` with `CStr m p cs` and `s.length = cs.length`. -/
theorem cstring_length (m : Mem) (p : Nat) (s : String) (h : CString m p s) :
    ∃ cs, CStr m p cs ∧ s.length = cs.length := by
  obtain ⟨cs, hcs, hs⟩ := h
  exact ⟨cs, hcs, by rw [hs, String.length_ofList]⟩

/-! ## Loaded-word byte extraction

The word-loop `ld` produces `sign_extend (ldBytesT σ a)`, which — since
`sign_extend (m := 64)` is identity on a `BitVec 64` — is exactly `ldBytesT σ a`.
Byte `k` of that word (`extractLsb' (8k) 8`) is the total (`getD 0`) memory byte
at `a + k`.  This bridges the loaded word to the per-address memory bytes that the
`CStr` facts describe, so `detect_all_ones` can fire on the string content. -/

/-- `sign_extend (m := 64)` is the identity on a `BitVec 64`. -/
theorem sext64_self (x : BitVec 64) : sign_extend (m := 64) x = x := by
  simp only [sign_extend, Sail.BitVec.signExtend, BitVec.signExtend_eq]

/-- Byte `k` (`k < 8`) of the totally-loaded word `ldBytesT σ a` is the memory byte
at `a.toNat + k` (`getD 0`).  Bitwise via `getLsbD` of `extractLsb'`/`append`. -/
theorem ldBytesT_byte (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64)
    (k : Nat) (hk : k < 8) :
    (ldBytesT σ a).extractLsb' (8*k) 8 = (σ.mem[a.toNat + k]?).getD 0 := by
  have hshow : ldBytesT σ a =
    ((((((((σ.mem[a.toNat + 7]?).getD 0) +++ ((σ.mem[a.toNat + 6]?).getD 0)) +++
     ((σ.mem[a.toNat + 5]?).getD 0)) +++ ((σ.mem[a.toNat + 4]?).getD 0)) +++
     ((σ.mem[a.toNat + 3]?).getD 0)) +++ ((σ.mem[a.toNat + 2]?).getD 0)) +++
     ((σ.mem[a.toNat + 1]?).getD 0)) +++ ((σ.mem[a.toNat]?).getD 0) := rfl
  rw [hshow]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append]
  rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    repeat' first | rw [if_pos (by omega)] | rw [if_neg (by omega)]
    congr 1 <;> omega

/-! ## Region / string side conditions

`StrRegions p len` bundles the disjointness / no-wrap side facts for the string
`[p, p+len]` (`len+1` bytes: `len` chars plus the NUL): the region lives in RAM,
disjoint from the `strlen` code `[0x80006cf0, 0x80006dc4)` and the HTIF window, and
does not wrap.  The word loop reads 8-aligned words that may extend up to 7 bytes
past `p+len`; those still lie in RAM (we require `p+len` far enough below the RAM
top), and their trailing content is read `getD 0` — never asserted. -/
structure StrRegions (p : BitVec 64) (len : Nat) : Prop where
  /-- the whole scanned area (string + up to 7 trailing bytes of the NUL word) is in RAM -/
  lo : 0x80000000 ≤ p.toNat
  hi : p.toNat + len + 8 ≤ 0x100000000
  nowrap : p.toNat + len + 8 < 2^64
  /-- disjoint from the strlen code region -/
  code : p.toNat + len + 8 ≤ 0x80006cf0 ∨ 0x80006dc4 ≤ p.toNat
  /-- disjoint from the HTIF tohost window (`tohostAddr = 0x8001ad00`, ± 8) -/
  htif : p.toNat + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p.toNat

/-- `tohostAddr` is the concrete HTIF address. -/
theorem tohost_val : tohostAddr = 0x8001ad00 := rfl

/-- Exact pointer arithmetic under no-wrap: `(base + ofNat k).toNat = base.toNat + k`. -/
theorem ptrN (base : BitVec 64) (k : Nat) (h : base.toNat + k < 2^64) :
    (base + BitVec.ofNat 64 k).toNat = base.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show k < 2^64 from by omega),
    Nat.mod_eq_of_lt h]

/-! ## The magic-test detection bridge

At the word-loop guard `beq a5,a1` (`a5 = strlenWordVal a2`, `a1 = allOnes`), with
`a2 = ldBytesT σ pos` and `pos = p + 8j` (`8j ≤ len`), the branch is **taken** (no
zero byte in the word) iff `8j + 8 ≤ len`.

* Taken (`8j+8 ≤ len`): every byte `p+8j+k` (`k<8`) is a string char (`< len`), hence
  nonzero — `detect_all_ones` gives `strlenWordVal a2 = allOnes`.
* Not taken (`8j ≤ len < 8j+8`): byte `p+len` is the NUL, at word offset `len-8j < 8`,
  so `detect_all_ones` fails and `strlenWordVal a2 ≠ allOnes`. -/

/-- Word at `pos = p + 8j`, `8j+8 ≤ len`, has no zero byte: guard taken. -/
theorem detect_taken (σ : SequentialState RegisterType trivialChoiceSource) (p : BitVec 64)
    (len j : Nat) (cs : List Char) (hcs : CStr σ.mem p.toNat cs) (hlen : cs.length = len)
    (hpos : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j)
    (hle : 8*(j+1) ≤ len) :
    strlenWordVal (ldBytesT σ (p + BitVec.ofNat 64 (8*j))) = BitVec.allOnes 64 := by
  rw [detect_all_ones]
  intro k hk
  rw [ldBytesT_byte σ _ k hk, hpos]
  -- byte at p.toNat + 8j + k, with 8j+k < len ⇒ nonzero (a string char)
  obtain ⟨b, hb, hbne⟩ := cstr_byte_ne σ.mem hcs (8*j + k) (by omega)
  rw [show p.toNat + 8*j + k = p.toNat + (8*j + k) from by omega, hb]
  simpa using hbne

/-- Word at `pos = p + 8j`, `8j ≤ len < 8j+8`, contains the NUL: guard not taken. -/
theorem detect_nottaken (σ : SequentialState RegisterType trivialChoiceSource) (p : BitVec 64)
    (len j : Nat) (cs : List Char) (hcs : CStr σ.mem p.toNat cs) (hlen : cs.length = len)
    (hlo : 8*j ≤ len) (hhi : len < 8*(j+1))
    (hpos : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j) :
    strlenWordVal (ldBytesT σ (p + BitVec.ofNat 64 (8*j))) ≠ BitVec.allOnes 64 := by
  intro hall
  rw [detect_all_ones] at hall
  -- the NUL byte at offset (len - 8j) < 8 is zero, contradicting hall
  have hk : len - 8*j < 8 := by omega
  have := hall (len - 8*j) hk
  rw [ldBytesT_byte σ _ _ hk, hpos] at this
  apply this
  have hnul : σ.mem[p.toNat + cs.length]? = some 0 := cstr_byte_nul σ.mem hcs
  rw [hlen] at hnul
  rw [show p.toNat + 8*j + (len - 8*j) = p.toNat + len from by omega, hnul]
  rfl

/-! ## The word-scan loop (`0xd10 … 0xd28`)

Ghosts: `p` (the 8-aligned scan base — for the aligned entry path, `p = a0`),
`len` (the string length, `= cs.length`), `cs`/`r`/`m0`; `hword : p.toNat % 8 = 0`.

Loop-head state `WSt j`, iteration `j` (`8j ≤ len`): PC at `0xd10`, `a4 = p+8j`,
`a3 = magic7f`, `a1 = allOnes`, `a0 = p`, `x1 = r`, `mem = m0`, string facts, region
bounds, `minstret` defined, `tick < 2`.  The body loads the word at `a4`, advances
`a4 += 8`, computes `a5 = strlenWordVal(word)`, and the `beq a5,a1` at `0xd28` loops
(`8(j+1) ≤ len`) or exits to the byte tail at `0xd2c` (`len < 8(j+1)`, NUL in word). -/

/-- Loop-head observation at `0xd10`, word-scan iteration `j`. -/
structure WSt (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d10#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some p
  a1 : c.σ.regs.get? Register.x11 = some (BitVec.allOnes 64)
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (8*j))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions p len
  align : p.toNat % 8 = 0
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len
  jle : 8*j ≤ len

/-- Post-loop "tail entry" observation at `0xd2c` (the byte tail): the word at
`a4-8 = p+8j` (the just-loaded word) contains the NUL (`8j ≤ len < 8(j+1)`).
`a4 = p+8(j+1)`, `a0 = p`, `a3` = magic7f (about to be overwritten by `sub a3,a4,a0`). -/
structure WTail (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d2c#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some p
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (8*(j+1)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions p len
  align : p.toNat % 8 = 0
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len
  jlo : 8*j ≤ len
  jhi : len < 8*(j+1)

/-- `v + sext 0 = v`. -/
theorem sext0_add (v : BitVec 64) : v + sign_extend (m := 64) (0x000#12) = v := by
  rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_zero]

/-- `strlenWordVal w` matches the site-level composition `(((w & m)+m)|w)|m`. -/
theorem strlenWordVal_eq (w : BitVec 64) :
    ((w &&& magic7f) + magic7f ||| w) ||| magic7f = strlenWordVal w := rfl

/-- `(p + 8j) + sext 8 = p + 8(j+1)` (the `addi a4,a4,8` increment), via BitVec group
algebra (`ofNat_add`) to avoid the `2^64`-literal omega kernel blowup. -/
theorem a4_incr (p : BitVec 64) (j : Nat) :
    (p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x008#12)
      = p + BitVec.ofNat 64 (8*(j+1)) := by
  rw [show (sign_extend (m := 64) (0x008#12) : BitVec 64) = BitVec.ofNat 64 8 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2

/-! ### Bounds for the load at `a4 = p + 8j` -/

/-- At iteration `j` (`8j ≤ len`), the scan pointer `p+8j` sits in RAM, is 8-aligned,
and is disjoint from the HTIF window — the side facts the total `ld` needs. -/
theorem wload_bounds (p : BitVec 64) (len j : Nat) (hreg : StrRegions p len)
    (halign : p.toNat % 8 = 0) (hj : 8*j ≤ len) :
    (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j ∧
    0x80000000 ≤ ((p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ 0x100000000 ∧
    (((p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x000#12)).toNat + 8 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x000#12)).toNat) ∧
    ((p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x000#12)).toNat % 8 = 0 := by
  have htn : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j :=
    ptrN p (8*j) (by have := hreg.nowrap; omega)
  have hlo := hreg.lo
  have hhi := hreg.hi
  have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨htn, ?_, ?_, ?_, ?_⟩
  all_goals rw [sext0_add, htn]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega
  · omega

/-- The word `strlen` loads at scan position `p+8j` (total `getD 0` bytes, as a
`BitVec 64`).  Depends only on `m0` (via the address bytes). -/
def strlenWordAt (m0 : Std.ExtHashMap Nat (BitVec 8)) (a : Nat) : BitVec 64 :=
  ((((((((m0[a + 7]?).getD 0).append ((m0[a + 6]?).getD 0)).append
    ((m0[a + 5]?).getD 0)).append ((m0[a + 4]?).getD 0)).append
    ((m0[a + 3]?).getD 0)).append ((m0[a + 2]?).getD 0)).append
    ((m0[a + 1]?).getD 0)).append ((m0[a]?).getD 0)

/-- `ldBytesT σ a = strlenWordAt σ.mem a.toNat` (both are the `getD 0` little-endian word). -/
theorem ldBytesT_wordAt (σ : SequentialState RegisterType trivialChoiceSource) (a : BitVec 64) :
    ldBytesT σ a = strlenWordAt σ.mem a.toNat := rfl

/-- State at `0xd28` (`beq a5,a1`) after the straight-line body of iteration `j`:
`a5 = strlenWordVal(word@(p+8j))`, `a4 = p+8(j+1)`, `a1 = allOnes`, `a0 = p`, `x1 = r`.
The scanned word is the ghost `strlenWordAt m0 (p.toNat + 8j)` (memory is unchanged). -/
structure W28 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d28#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some p
  a1 : c.σ.regs.get? Register.x11 = some (BitVec.allOnes 64)
  a3 : c.σ.regs.get? Register.x13 = some magic7f
  a5 : c.σ.regs.get? Register.x15 = some (strlenWordVal (strlenWordAt m0 (p.toNat + 8*j)))
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (8*(j+1)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions p len
  align : p.toNat % 8 = 0
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len
  jle : 8*j ≤ len

/-- One straight-line body (`0xd10 → 0xd28`): load, advance `a4`, compute
`a5 = strlenWordVal(word)`.  The load uses the total (`getD 0`) chain, so trailing
bytes of the NUL word may be unmapped. -/
theorem wloop_straight (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) :
    Triple (WSt p r len cs m0 j) (W28 p r len cs m0 j) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha3, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halign, hcstr, hlen, hjle⟩ := hSt
  obtain ⟨htn, hlo, hhi, hhtif, halgn⟩ := wload_bounds p len j hreg halign hjle
  -- === d10: ld a2,0(a4) === (total load)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d10 c.σ c.tick c.steps (0x80006d10#64) vmi (p + BitVec.ofNat 64 (8*j))
      hgood hpc hmi ha4 hloaded rfl hlo hhi hhtif halgn htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d14#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006d10#64) 4 = (0x80006d14#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
  have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  -- a2 = sign_extend (ldBytesT σ₂ …) = strlenWordAt m0 (p.toNat + 8j) (mem unchanged; sext identity)
  have hword : (sign_extend (m := 64)
        (ldBytesT (afterNextPC (afterPrelude c.σ) (0x80006d10#64))
          ((p + BitVec.ofNat 64 (8*j)) + sign_extend (m := 64) (0x000#12))))
      = strlenWordAt m0 (p.toNat + 8*j) := by
    rw [sext64_self, sext0_add, ldBytesT_wordAt, mem_afterNextPC, mem_afterPrelude, hmem, htn]
  have ha2_1 : σ1.regs.get? Register.x12 = some (strlenWordAt m0 (p.toNat + 8*j)) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [hword] at this
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- === d14: addi a4,a4,8 ===  a4 := (p+8j) + 8 = p + 8(j+1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d14 σ1 i1 (c.steps + 1) (0x80006d14#64) vmi1 (p + BitVec.ofNat 64 (8*j))
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d18#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d14#64) 4 = (0x80006d18#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha1_2 := obs_alu_other' hobs2 Register.x11 (by decide) ha1_1
  have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (8*(j+1))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [a4_incr p j] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- === d18: and a5,a2,a3 ===  a5 := a2 & a3 = word & magic7f
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d18 σ2 i2 (c.steps + 1 + 1) (0x80006d18#64) vmi2 (strlenWordAt m0 (p.toNat + 8*j)) magic7f
      hG2 hpc2 hmi2' ha2_2 ha3_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d1c#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d18#64) 4 = (0x80006d1c#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha1_3 := obs_alu_other' hobs3 Register.x11 (by decide) ha1_2
  have ha2_3 := obs_alu_other' hobs3 Register.x12 (by decide) ha2_2
  have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha5_3 := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- === d1c: add a5,a5,a3 ===  a5 := (word&m) + m
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006d1c σ3 i3 (c.steps + 1 + 1 + 1) (0x80006d1c#64) vmi3 (strlenWordAt m0 (p.toNat + 8*j) &&& magic7f) magic7f
      hG3 hpc3 hmi3' ha5_3 ha3_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006d20#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006d1c#64) 4 = (0x80006d20#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have ha1_4 := obs_alu_other' hobs4 Register.x11 (by decide) ha1_3
  have ha2_4 := obs_alu_other' hobs4 Register.x12 (by decide) ha2_3
  have ha3_4 := obs_alu_other' hobs4 Register.x13 (by decide) ha3_3
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha5_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- === d20: or a5,a5,a2 ===  a5 := ((word&m)+m) | word
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006d20 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006d20#64) vmi4
      ((strlenWordAt m0 (p.toNat + 8*j) &&& magic7f) + magic7f) (strlenWordAt m0 (p.toNat + 8*j))
      hG4 hpc4 hmi4' ha5_4 ha2_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d24#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006d20#64) 4 = (0x80006d24#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have ha1_5 := obs_alu_other' hobs5 Register.x11 (by decide) ha1_4
  have ha3_5 := obs_alu_other' hobs5 Register.x13 (by decide) ha3_4
  have ha4_5 := obs_alu_other' hobs5 Register.x14 (by decide) ha4_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha5_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- === d24: or a5,a5,a3 ===  a5 := (((word&m)+m)|word) | m = strlenWordVal word
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006d24 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006d24#64) vmi5
      (((strlenWordAt m0 (p.toNat + 8*j) &&& magic7f) + magic7f) ||| strlenWordAt m0 (p.toNat + 8*j)) magic7f
      hG5 hpc5 hmi5' ha5_5 ha3_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006d28#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006d24#64) 4 = (0x80006d28#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have ha1_6 := obs_alu_other' hobs6 Register.x11 (by decide) ha1_5
  have ha3_6 := obs_alu_other' hobs6 Register.x13 (by decide) ha3_5
  have ha4_6 := obs_alu_other' hobs6 Register.x14 (by decide) ha4_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha5_6 : σ6.regs.get? Register.x15 = some (strlenWordVal (strlenWordAt m0 (p.toNat + 8*j))) := by
    have := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [strlenWordVal_eq] at this
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  have hmem6eq : σ6.mem = c.σ.mem := by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  refine ⟨⟨σ6, i6, c.steps + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6),
    hG6, by rw [hmem6eq]; exact hloaded, by rw [hmem6eq]; exact hmem, hpc6, ha0_6, ha1_6, ha3_6,
    ha5_6, ha4_6, hra_6, ⟨vmi6, hmi6'⟩, hi6, hreg, halign, hcstr, hlen, hjle⟩

/-- `strlenWordAt m0 (p.toNat + 8j) = ldBytesT c.σ (p + 8j)` when `c.σ.mem = m0` and
`(p+8j).toNat = p.toNat+8j`, so the detection lemmas apply to the ghost word. -/
theorem wordAt_eq_ldBytesT (c : Config) (m0 : Std.ExtHashMap Nat (BitVec 8)) (p : BitVec 64)
    (j : Nat) (hmem : c.σ.mem = m0) (hpos : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j) :
    strlenWordAt m0 (p.toNat + 8*j) = ldBytesT c.σ (p + BitVec.ofNat 64 (8*j)) := by
  rw [ldBytesT_wordAt, hmem, hpos]

/-- Word-loop back-edge (`0xd28 → 0xd10`, `beq a5,a1` taken): `8(j+1) ≤ len` (no NUL
in the word), loop back to iteration `j+1`. -/
theorem wloop_back (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hle : 8*(j+1) ≤ len) :
    Triple (W28 p r len cs m0 j) (WSt p r len cs m0 (j+1)) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halign, hcstr, hlen, hjle⟩ := hSt
  have hpos : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j :=
    ptrN p (8*j) (by have := hreg.nowrap; omega)
  -- a5 = allOnes: word has no zero byte
  have hdet : strlenWordVal (strlenWordAt m0 (p.toNat + 8*j)) = BitVec.allOnes 64 := by
    rw [wordAt_eq_ldBytesT c m0 p j hmem hpos]
    exact detect_taken c.σ p len j cs (by rw [hmem]; exact hcstr) hlen hpos hle
  have hv : ((strlenWordVal (strlenWordAt m0 (p.toNat + 8*j))) == (BitVec.allOnes 64)) = true := by
    rw [hdet]; simp
  have htgt : ((0x80006d28#64 : BitVec 64) + sign_extend (m := 64) (0x1fe8#13)).toNat % 4 = 0 := by decide
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d28_taken c.σ c.tick c.steps (0x80006d28#64) vmi
      (strlenWordVal (strlenWordAt m0 (p.toNat + 8*j))) (BitVec.allOnes 64)
      hgood hpc hmi ha5 ha1 hloaded rfl hv htick
  have hpceq : (0x80006d28#64 : BitVec 64) + sign_extend (m := 64) (0x1fe8#13) = (0x80006d10#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc'' : σ'.regs.get? Register.PC = some (0x80006d10#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs, hpceq]
  -- a4 at j+1: p + 8((j+1)) — W28's a4 is already p + 8(j+1)
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc'',
    obs_btaken_other' hobs Register.x10 (by decide) ha0,
    obs_btaken_other' hobs Register.x11 (by decide) ha1,
    obs_btaken_other' hobs Register.x13 (by decide) ha3,
    obs_btaken_other' hobs Register.x14 (by decide) ha4,
    obs_btaken_other' hobs Register.x1 (by decide) hra,
    obs_btaken_minstret hobs, hi', hreg, halign, hcstr, hlen, by omega⟩

/-- Word-loop exit (`0xd28 → 0xd2c`, `beq a5,a1` not taken): `8j ≤ len < 8(j+1)` (the
loaded word contains the NUL), fall through to the byte tail. -/
theorem wloop_exit (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlo : 8*j ≤ len) (hhi : len < 8*(j+1)) :
    Triple (W28 p r len cs m0 j) (WTail p r len cs m0 j) := by
  apply Triple.of_step
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha1, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halign, hcstr, hlen, hjle⟩ := hSt
  have hpos : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j :=
    ptrN p (8*j) (by have := hreg.nowrap; omega)
  -- a5 ≠ allOnes: word has a zero byte (the NUL)
  have hdet : strlenWordVal (strlenWordAt m0 (p.toNat + 8*j)) ≠ BitVec.allOnes 64 := by
    rw [wordAt_eq_ldBytesT c m0 p j hmem hpos]
    exact detect_nottaken c.σ p len j cs (by rw [hmem]; exact hcstr) hlen hlo hhi hpos
  have hv : ((strlenWordVal (strlenWordAt m0 (p.toNat + 8*j))) == (BitVec.allOnes 64)) = false := by
    rw [beq_eq_false_iff_ne]; exact hdet
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d28_nottaken c.σ c.tick c.steps (0x80006d28#64) vmi
      (strlenWordVal (strlenWordAt m0 (p.toNat + 8*j))) (BitVec.allOnes 64)
      hgood hpc hmi ha5 ha1 hloaded rfl hv htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006d2c#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs
    rwa [show BitVec.addInt (0x80006d28#64) 4 = (0x80006d2c#64 : BitVec 64) from by decide] at this
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc',
    obs_bnottaken_other' hobs Register.x10 (by decide) ha0,
    obs_bnottaken_other' hobs Register.x14 (by decide) ha4,
    obs_bnottaken_other' hobs Register.x1 (by decide) hra,
    obs_bnottaken_minstret hobs, hi', hreg, halign, hcstr, hlen, hlo, hhi⟩

/-! ### Word-loop assembly (`Triple.loop`)

Invariant `WLoopI`: either at the head `0xd10` (some iteration `j`, `8j ≤ len`) or
done at the byte-tail entry `0xd2c` (`WTail`).  Guard `WLoopB`: at the head.  Measure
`WLoopMu = len + 1 - 8j` **at the head `0xd10`**, else `0` — the PC guard drops the
measure to `0` on the exit edge (to `0xd2c`), and the back-edge advances `j`. -/

/-- Head disjunct: at `0xd10`, iteration `j ≤ len/8`. -/
def WAtHead (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ j, WSt p r len cs m0 j c

/-- Done disjunct: at `0xd2c` (byte tail), the NUL word's iteration `j`. -/
def WAtTail (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  ∃ j, WTail p r len cs m0 j c

def WLoopI (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  WAtHead p r len cs m0 c ∨ WAtTail p r len cs m0 c

def WLoopB (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop :=
  WAtHead p r len cs m0 c

/-- Measure: `len + 1 - a4.toNat's word-offset` at the head, else `0`.  We compute
`len + 1 - (a4.toNat - p.toNat)`; at the head `a4 = p + 8j` so this is `len + 1 - 8j`. -/
def WLoopMu (p : BitVec 64) (len : Nat) (c : Config) : Nat :=
  if c.σ.regs.get? Register.PC = some (0x80006d10#64)
  then len + 1 - (((c.σ.regs.get? Register.x14).getD (0#64)).toNat - p.toNat)
  else 0

/-- At the head, `WLoopMu = len + 1 - 8j`. -/
theorem wloopmu_head (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (c : Config) (hSt : WSt p r len cs m0 j c) :
    WLoopMu p len c = len + 1 - 8*j := by
  simp only [WLoopMu, hSt.pc, hSt.a4, Option.getD_some, if_pos]
  have h4 : (p + BitVec.ofNat 64 (8*j)).toNat = p.toNat + 8*j :=
    ptrN p (8*j) (by have := hSt.regions.nowrap; have := hSt.jle; omega)
  rw [h4]; omega

/-- **Word-loop body**: one iteration re-establishes `WLoopI`, strictly decreasing
`WLoopMu`.  Back-edge (`8(j+1) ≤ len`): `WSt (j+1)`, measure `len+1-8(j+1) < len+1-8j`.
Exit (`len < 8(j+1)`): `WTail`, measure `0`. -/
theorem wloop_body (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (k : Nat) :
    Triple (fun c => WLoopI p r len cs m0 c ∧ WLoopB p r len cs m0 c ∧ WLoopMu p len c = k)
           (fun c => WLoopI p r len cs m0 c ∧ WLoopMu p len c < k) := by
  intro c hc
  obtain ⟨_, ⟨j, hSt⟩, hmu⟩ := hc
  have hmu_eq : WLoopMu p len c = len + 1 - 8*j := wloopmu_head p r len cs m0 j c hSt
  rw [hmu_eq] at hmu
  have hjle := hSt.jle
  -- straight-line body to 0xd28
  obtain ⟨c1, hs1, hSt28⟩ := wloop_straight p r len cs m0 j c hSt
  by_cases hdone : 8*(j+1) ≤ len
  · -- back-edge: WSt (j+1), measure drops
    obtain ⟨c2, hs2, hSt2⟩ := wloop_back p r len cs m0 j hdone c1 hSt28
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨j+1, hSt2⟩, ?_⟩
    have hmu2 : WLoopMu p len c2 = len + 1 - 8*(j+1) := wloopmu_head p r len cs m0 (j+1) c2 hSt2
    rw [hmu2, ← hmu]; omega
  · -- exit: WTail, measure 0 (PC ≠ d10)
    have hhi : len < 8*(j+1) := by omega
    obtain ⟨c2, hs2, hTail⟩ := wloop_exit p r len cs m0 j hjle hhi c1 hSt28
    refine ⟨c2, hs1.trans hs2, Or.inr ⟨j, hTail⟩, ?_⟩
    have hmu2 : WLoopMu p len c2 = 0 := by
      simp only [WLoopMu, hTail.pc]
      rw [if_neg (by intro h; injection h with h; exact absurd h (by decide))]
    rw [hmu2]; omega

/-- The word loop runs from `WLoopI` to `WAtTail` (byte-tail entry `0xd2c`). -/
theorem wloop_to_tail (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (WLoopI p r len cs m0) (WAtTail p r len cs m0) := by
  have hloop := Triple.loop (I := WLoopI p r len cs m0) (B := WLoopB p r len cs m0)
    (WLoopMu p len) (wloop_body p r len cs m0)
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hTail
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hTail⟩

/-! ## Entry + magic-constant setup (`0xcf0 … 0xd0c`), aligned path

Entry precondition `Pre`: PC at `0x80006cf0`, `a0 = p` (`p.toNat % 8 = 0`, the aligned
fast path), `x1 = r`, `mem = m0`, the `CStr` facts, regions.  The entry runs
`andi a5,a0,7` (`a5 = 0`), `mv a4,a0`, `bnez a5` (not taken, since aligned), then the
magic setup, landing at the word-loop head `0xd10` with `WSt 0`.

We isolate the aligned path here; the unaligned head-peel path (`bnez` taken) is a
separate (lower-priority) segment. -/

/-- Entry precondition at `0x80006cf0` (aligned fast path: `p.toNat % 8 = 0`). -/
structure Pre (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some p
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions p len
  align : p.toNat % 8 = 0
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len

/-- For an 8-aligned `p`, `p &&& sext(0x007) = 0` (low 3 bits clear). -/
theorem andi7_aligned (p : BitVec 64) (halign : p.toNat % 8 = 0) :
    (p &&& sign_extend (m := 64) (0x007#12)) = 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
    show (7:Nat) = 2^3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    show (2:Nat)^3 = 8 from rfl, halign]
  rfl

/-- `bnez a5` (`a5 = 0`) is not taken. -/
theorem bnez_zero_false : (((0#64 : BitVec 64)) != (0#64)) = false := by simp

/-- `p + ofNat 0 = p`. -/
theorem ptr_zero (p : BitVec 64) : p + BitVec.ofNat 64 (8*0) = p := by
  rw [show (BitVec.ofNat 64 (8*0) : BitVec 64) = 0#64 from rfl, BitVec.add_zero]

/-- The magic-mask value `a3` built by `lui/addi/slli/add` equals `magic7f`. -/
theorem magic_build :
    (shift_bits_left (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      (Sail.BitVec.extractLsb (0x20#6) 5 0)
      + (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12)))
      = magic7f := by
  apply BitVec.eq_of_toNat_eq; decide

/-- The `a1 = -1` value equals `allOnes 64`. -/
theorem allOnes_build : ((0#64) + sign_extend (m := 64) (0xfff#12)) = BitVec.allOnes 64 := by
  apply BitVec.eq_of_toNat_eq; decide

/-- **Aligned entry** (`0xcf0 → 0xd10`): establishes the word-loop head `WSt 0`.
`andi a5,a0,7` yields `0` (aligned), `mv a4,a0` sets `a4 = p`, `bnez a5` falls through,
and the magic setup builds `a3 = magic7f`, `a1 = allOnes`. -/
theorem entry_aligned (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (Pre p r len cs m0) (WAtHead p r len cs m0) := by
  intro c hPre
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, hra, ⟨vmi, hmi⟩, htick, hreg, halign, hcstr, hlen⟩ := hPre
  -- cf0: andi a5,a0,7  → a5 = p & 7 = 0
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006cf0 c.σ c.tick c.steps (0x80006cf0#64) vmi p hgood hpc hmi ha0 hloaded rfl htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006cf4#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006cf0#64) 4 = (0x80006cf4#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 : σ1.regs.get? Register.x15 = some (0#64) := by
    have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [andi7_aligned p halign] at this
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- cf4: mv a4,a0  → a4 = p
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006cf4 σ1 i1 (c.steps + 1) (0x80006cf4#64) vmi1 p hG1 hpc1 hmi1' ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006cf8#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006cf4#64) 4 = (0x80006cf8#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
  have ha4_2 : σ2.regs.get? Register.x14 = some p := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sext0_add] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- cf8: bnez a5  (a5 = 0) not taken → cfc
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006cf8_nottaken σ2 i2 (c.steps + 1 + 1) (0x80006cf8#64) vmi2 (0#64)
      hG2 hpc2 hmi2' ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl bnez_zero_false hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006cfc#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs3; rwa [show BitVec.addInt (0x80006cf8#64) 4 = (0x80006cfc#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_bnottaken_other' hobs3 Register.x10 (by decide) ha0_2
  have hra_3 := obs_bnottaken_other' hobs3 Register.x1 (by decide) hra_2
  have ha4_3 := obs_bnottaken_other' hobs3 Register.x14 (by decide) ha4_2
  obtain ⟨vmi3, hmi3'⟩ := obs_bnottaken_minstret hobs3
  -- cfc: lui a5,0x7f7f8  → a5 = sext(0x7f7f8000)
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006cfc σ3 i3 (c.steps + 1 + 1 + 1) (0x80006cfc#64) vmi3 hG3 hpc3 hmi3' (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006d00#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006cfc#64) 4 = (0x80006d00#64 : BitVec 64) from by decide] at this
  have ha0_4 := obs_alu_other' hobs4 Register.x10 (by decide) ha0_3
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha4_4 := obs_alu_other' hobs4 Register.x14 (by decide) ha4_3
  have ha5_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- d00: addi a5,a5,-129  → a5 = sext(0x7f7f8000) + sext(0xf7f) = 0x7f7f7f7f
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006d00 σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006d00#64) vmi4
      (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)))
      hG4 hpc4 hmi4' ha5_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d04#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006d00#64) 4 = (0x80006d04#64 : BitVec 64) from by decide] at this
  have ha0_5 := obs_alu_other' hobs5 Register.x10 (by decide) ha0_4
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha4_5 := obs_alu_other' hobs5 Register.x14 (by decide) ha4_4
  have ha5_5 := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  -- d04: slli a3,a5,0x20  → a3 = a5 << 32
  obtain ⟨σ6, i6, hs6, hi6, hG6, hmem6, hobs6⟩ :=
    site_80006d04 σ5 i5 (c.steps + 1 + 1 + 1 + 1 + 1) (0x80006d04#64) vmi5
      (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      hG5 hpc5 hmi5' ha5_5 (by rw [hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi5
  have hpc6 : σ6.regs.get? Register.PC = some (0x80006d08#64 : BitVec 64) := by
    have := obs_alu_pc hobs6; rwa [show BitVec.addInt (0x80006d04#64) 4 = (0x80006d08#64 : BitVec 64) from by decide] at this
  have ha0_6 := obs_alu_other' hobs6 Register.x10 (by decide) ha0_5
  have hra_6 := obs_alu_other' hobs6 Register.x1 (by decide) hra_5
  have ha4_6 := obs_alu_other' hobs6 Register.x14 (by decide) ha4_5
  have ha5_6 := obs_alu_other' hobs6 Register.x15 (by decide) ha5_5
  have ha3_6 := obs_alu_rd hobs6 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi6, hmi6'⟩ := obs_alu_minstret hobs6
  -- d08: add a3,a3,a5  → a3 = (a5<<32) + a5 = magic7f
  obtain ⟨σ7, i7, hs7, hi7, hG7, hmem7, hobs7⟩ :=
    site_80006d08 σ6 i6 (c.steps + 1 + 1 + 1 + 1 + 1 + 1) (0x80006d08#64) vmi6
      (shift_bits_left (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12)) (Sail.BitVec.extractLsb (0x20#6) 5 0))
      (sign_extend (m := 64) ((0x7f7f8#20) +++ (0x000#12)) + sign_extend (m := 64) (0xf7f#12))
      hG6 hpc6 hmi6' ha3_6 ha5_6 (by rw [hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi6
  have hpc7 : σ7.regs.get? Register.PC = some (0x80006d0c#64 : BitVec 64) := by
    have := obs_alu_pc hobs7; rwa [show BitVec.addInt (0x80006d08#64) 4 = (0x80006d0c#64 : BitVec 64) from by decide] at this
  have ha0_7 := obs_alu_other' hobs7 Register.x10 (by decide) ha0_6
  have hra_7 := obs_alu_other' hobs7 Register.x1 (by decide) hra_6
  have ha4_7 := obs_alu_other' hobs7 Register.x14 (by decide) ha4_6
  have ha3_7 : σ7.regs.get? Register.x13 = some magic7f := by
    have := obs_alu_rd hobs7 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [magic_build] at this
  obtain ⟨vmi7, hmi7'⟩ := obs_alu_minstret hobs7
  -- d0c: li a1,-1  → a1 = allOnes
  obtain ⟨σ8, i8, hs8, hi8, hG8, hmem8, hobs8⟩ :=
    site_80006d0c σ7 i7 (c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1) (0x80006d0c#64) vmi7
      hG7 hpc7 hmi7' (by rw [hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi7
  have hpc8 : σ8.regs.get? Register.PC = some (0x80006d10#64 : BitVec 64) := by
    have := obs_alu_pc hobs8; rwa [show BitVec.addInt (0x80006d0c#64) 4 = (0x80006d10#64 : BitVec 64) from by decide] at this
  have ha0_8 := obs_alu_other' hobs8 Register.x10 (by decide) ha0_7
  have hra_8 := obs_alu_other' hobs8 Register.x1 (by decide) hra_7
  have ha4_8 := obs_alu_other' hobs8 Register.x14 (by decide) ha4_7
  have ha3_8 := obs_alu_other' hobs8 Register.x13 (by decide) ha3_7
  have ha1_8 : σ8.regs.get? Register.x11 = some (BitVec.allOnes 64) := by
    have := obs_alu_rd hobs8 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [allOnes_build] at this
  obtain ⟨vmi8, hmi8'⟩ := obs_alu_minstret hobs8
  have hmem8eq : σ8.mem = c.σ.mem := by rw [hmem8, hmem7, hmem6, hmem5, hmem4, hmem3, hmem2, hmem1]
  refine ⟨⟨σ8, i8, c.steps + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1⟩,
    (((((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
      (Steps.single hs4)).trans (Steps.single hs5)).trans (Steps.single hs6)).trans
      (Steps.single hs7)).trans (Steps.single hs8), 0, ?_⟩
  refine ⟨hG8, by rw [hmem8eq]; exact hloaded, by rw [hmem8eq]; exact hmem, hpc8, ha0_8, ha1_8,
    ha3_8, ?_, hra_8, ⟨vmi8, hmi8'⟩, hi8, hreg, halign, hcstr, hlen, by omega⟩
  · rw [ptr_zero]; exact ha4_8

/-! ## Byte tail (`0xd2c … 0xd70`) and exit blocks (`0xd94 … 0xdc0`)

From `WTail j` (at `0xd2c`, `8j ≤ len < 8(j+1)`, `a4 = p+8(j+1)`, `a0 = p`): the tail
probes bytes `p+8j … p+8j+7` with `lbu`/`beqz`, and on hitting the NUL (at offset
`i₀ = len - 8j`) jumps to the exit block computing `a0 = a3 + (i₀ - 8) = 8(j+1) - 8 +
i₀ = 8j + i₀ = len`.  `d30 sub a3,a4,a0` sets `a3 = 8(j+1)`.

The final observation `Done`: PC at `r`, `a0 = ofNat len`, `x1 = r`, `GoodState`, mem
unchanged.  This is the strlen postcondition. -/

/-- Final `strlen` observation: returned to `r` with `a0 = len`. -/
structure Done (p r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop where
  good : GoodState c.σ
  pc : c.σ.regs.get? Register.PC = some r
  a0 : c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 len)
  ra : c.σ.regs.get? Register.x1 = some r
  mem : c.σ.mem = m0

/-- The byte at word-offset `k` of the NUL word (`k < i₀ = len - 8j`) is a nonzero
string char; at `k = i₀` it is the NUL.  Bridges `CStr` to the tail `lbu` reads. -/
theorem tail_byte (p : BitVec 64) (len j k : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 p.toNat cs) (hlen : cs.length = len)
    (hlo : 8*j ≤ len) (hk : 8*j + k ≤ len) :
    (k < len - 8*j → ∃ b : BitVec 8, m0[p.toNat + 8*j + k]? = some b ∧ b ≠ 0) ∧
    (k = len - 8*j → m0[p.toNat + 8*j + k]? = some 0) := by
  refine ⟨fun hklt => ?_, fun hkeq => ?_⟩
  · obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m0 hcstr (8*j + k) (by omega)
    exact ⟨b, by rw [show p.toNat + 8*j + k = p.toNat + (8*j + k) from by omega]; exact hb, hbne⟩
  · have hnul := cstr_byte_nul m0 hcstr
    rw [hlen] at hnul
    rw [show p.toNat + 8*j + k = p.toNat + len from by omega]; exact hnul

/-- `ofNat a - ofNat b = ofNat (a-b)` for `b ≤ a` (via add-cancel; no `2^64` omega). -/
theorem ofNat_sub (a b : Nat) (h : b ≤ a) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 b = BitVec.ofNat 64 (a - b) := by
  have : (BitVec.ofNat 64 (a-b)) + BitVec.ofNat 64 b = BitVec.ofNat 64 a := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [← this, BitVec.add_sub_cancel]

/-- `sub a3,a4,a0` value: `(p + ofNat m) - p = ofNat m`. -/
theorem sub_a4_a0_val (p : BitVec 64) (m : Nat) :
    (p + BitVec.ofNat 64 m) - p = BitVec.ofNat 64 m := by
  rw [BitVec.add_comm, BitVec.add_sub_cancel]

/-- The tail `lbu a5,off(a4)` effective address, offset `k` (`imm` sign-extends to
`-(8-k)`, `k ≤ 8`): `a4 + sext imm = (p+8(j+1)) - (8-k) = p + (8j+k)`. -/
theorem lbu_addr (p : BitVec 64) (j k : Nat) (hk : k ≤ 8) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8-k))) :
    (p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) imm
      = p + BitVec.ofNat 64 (8*j + k) := by
  rw [himm, BitVec.add_assoc, BitVec.add_neg_eq_sub, ofNat_sub (8*(j+1)) (8-k) (by omega)]
  congr 2; omega

/-- Exit-block `addi a0,a3,imm` value: with `a3 = ofNat(8(j+1))` and `imm` encoding
`-(8-k)` (`k ≤ 8`), the result is `ofNat len` (`= ofNat(8j+k)`). -/
theorem exit_addi_val (j len k : Nat) (imm : BitVec 12)
    (hk : k ≤ 8) (hlen : 8*j + k = len)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8 - k))) :
    (BitVec.ofNat 64 (8*(j+1)) + sign_extend (m := 64) imm) = BitVec.ofNat 64 len := by
  rw [himm, BitVec.add_neg_eq_sub, ofNat_sub (8*(j+1)) (8-k) (by omega)]
  congr 1; omega

/-- The `ret` bytes `67 80 00 00` are loaded at every exit-block ret PC (from
`StrlenLoaded`, whose `strlenChunk*` cover `[0xcf0, 0xdc4)`).  Provided per-PC below. -/
def RetBytes (mem : Std.ExtHashMap Nat (BitVec 8)) (pc : Nat) : Prop :=
  mem[pc]? = some (0x67#8) ∧ mem[pc+1]? = some (0x80#8) ∧
  mem[pc+2]? = some (0x00#8) ∧ mem[pc+3]? = some (0x00#8)

/-- At a ret PC with `a0 = ofNat len`, `x1 = r` (4-aligned), `mem = m0`: the `ret`
returns to `r`, preserving `a0`, reaching `Done`.  `retpc`'s `ret` bytes come from
`StrlenLoaded` via `hret`. -/
theorem ret_to_done (p r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (retpc : BitVec 64)
    (hret : ∀ (mem : Std.ExtHashMap Nat (BitVec 8)), StrlenLoaded mem → RetBytes mem retpc.toNat)
    (hlo : 0x80000000 ≤ retpc.toNat) (hhi : retpc.toNat + 4 ≤ tohostAddr)
    (halgn : retpc.toNat % 4 = 0) (halign : r.toNat % 4 = 0) :
    Triple (fun c => GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
        c.σ.regs.get? Register.PC = some retpc ∧
        c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 len) ∧
        c.σ.regs.get? Register.x1 = some r ∧
        (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2)
      (Done p r len m0) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha0, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨hb0, hb1, hb2, hb3⟩ := hret c.σ.mem hloaded
  have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
    rw [ret_tgt r halign]; exact halign
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_exit_ret c.σ c.tick c.steps retpc vmi r hgood hpc hmi hra hb0 hb1 hb2 hb3
      hlo hhi halgn htgt htick
  have hpc' : σ'.regs.get? Register.PC = some r := by
    rw [obs_jr_pc hobs, ret_tgt r halign]
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG', hpc',
    obs_jr_other' hobs Register.x10 (by decide) ha0,
    obs_jr_other' hobs Register.x1 (by decide) hra,
    by rw [hmem']; exact hmem⟩

/-! ### Tail cursor states and the ladder

`TDec k` observes the config at the `beqz` (for `k ≤ 5`) / at `0xd60` (`k = 6`) decision
point for byte offset `k`, having found no NUL in offsets `0..k-1` (so `8j + k ≤ len`).
`a5 = byte@(p+8j+k)`, `a3 = ofNat(8(j+1))`, `a0 = p`, `x1 = r`, the string/region facts.

Byte-offset → `beqz`-PC map (from disasm): 0↦d34, 1↦d3c, 2↦d44, 3↦d4c, 4↦d54, 5↦d5c;
`beqz`-target (exit-addi PC) for offset `k` is the block computing `a0 = a3 - (8-k)`:
0↦d9c, 1↦d94, 2↦dac, 3↦da4, 4↦db4, 5↦dbc. Offsets 6,7 use the `snez` path at d60. -/

/-- Config at the offset-`k` decision (`k ≤ 6`): `a5 = byte@(p+8j+k)` (zext), `a3 =
ofNat(8(j+1))`, `a0 = p`, `x1 = r`, no NUL in `[p+8j, p+8j+k)` (so `8j+k ≤ len`). -/
structure TDec (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j k : Nat) (decpc : BitVec 64) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some decpc
  a0 : c.σ.regs.get? Register.x10 = some p
  a3 : c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (8*(j+1)))
  a5 : c.σ.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + k]?).getD 0))
  a4 : c.σ.regs.get? Register.x14 = some (p + BitVec.ofNat 64 (8*(j+1)))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions p len
  align : p.toNat % 8 = 0
  cstr : CStr m0 p.toNat cs
  hlen : cs.length = len
  jlo : 8*j ≤ len
  jhi : len < 8*(j+1)
  kle : 8*j + k ≤ len

/-- RAM/window/byte facts for the tail `lbu` at offset `k` (`k ≤ 7`): the address
`p+8j+k` is in RAM, above the HTIF window, and (via `StrRegions`) reads the memory
byte there. -/
theorem tail_lbu_bounds (p : BitVec 64) (len j k : Nat) (hreg : StrRegions p len)
    (hj : 8*j ≤ len) (hk : k ≤ 7) :
    0x80000000 ≤ (p.toNat + 8*j + k) ∧
    (p.toNat + 8*j + k) + 1 ≤ 0x100000000 ∧
    ((p.toNat + 8*j + k) + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ (p.toNat + 8*j + k)) := by
  have hlo := hreg.lo
  have hhi := hreg.hi
  have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  refine ⟨by omega, by omega, ?_⟩
  rcases hh with h | h
  · left; omega
  · right; omega

/-- The tail byte at offset `k ≤ i₀` (`8j+k ≤ len`) is mapped: `m0[p+8j+k]? = some b`.
For `8j+k < len` it is a nonzero char; for `8j+k = len` it is the NUL. -/
theorem tail_byte_some (p : BitVec 64) (len j k : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 p.toNat cs) (hlen : cs.length = len)
    (hk : 8*j + k ≤ len) :
    ∃ b : BitVec 8, m0[p.toNat + 8*j + k]? = some b ∧ (b = 0 ↔ 8*j + k = len) := by
  by_cases heq : 8*j + k = len
  · refine ⟨0, ?_, by simp [heq]⟩
    have hnul := cstr_byte_nul m0 hcstr
    rw [hlen] at hnul
    rw [show p.toNat + 8*j + k = p.toNat + len from by omega]; exact hnul
  · obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m0 hcstr (8*j + k) (by omega)
    refine ⟨b, by rw [show p.toNat + 8*j + k = p.toNat + (8*j+k) from by omega]; exact hb, ?_⟩
    constructor
    · intro h; exact absurd h hbne
    · intro h; omega

/-- `imm` sign-extension for tail `lbu` offset `k`: `-(8-k)`.  Concrete per-`k`. -/
theorem tail_imm (k : Nat) (imm : BitVec 12)
    (himm : (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8-k))) :
    (sign_extend (m := 64) imm : BitVec 64) = -(BitVec.ofNat 64 (8-k)) := himm

/-- `zext b == 0` iff `b == 0` (the `beqz a5` guard reads the loaded byte). -/
theorem zext_beqz (b : BitVec 8) : ((zero_extend (m := 64) b) == (0#64)) = (b == 0#8) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
  constructor
  · intro h
    have : (zero_extend (m := 64) b).toNat = 0 := by rw [h]; rfl
    apply BitVec.eq_of_toNat_eq
    simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using this
  · intro h; rw [h]; rfl

/-- Tail entry (`0xd2c → 0xd34`): `lbu a5,-8(a4)` (byte offset 0) then
`sub a3,a4,a0` (`a3 = ofNat(8(j+1))`).  Reaches the offset-0 decision `TDec j 0 d34`. -/
theorem tail_entry (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) :
    Triple (WTail p r len cs m0 j) (TDec p r len cs m0 j 0 (0x80006d34#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halign, hcstr, hlen, hjlo, hjhi⟩ := hSt
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 0 hreg hjlo (by omega)
  obtain ⟨b0, hb0mem, _⟩ := tail_byte_some p len j 0 cs m0 hcstr hlen (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xff8#12)).toNat
      = p.toNat + 8*j + 0 := by
    rw [lbu_addr p j 0 (by omega) (0xff8#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    rw [show (8*j + 0 : Nat) = 8*j from by omega]
    exact ptrN p (8*j) (by have := hreg.nowrap; omega)
  -- d2c: lbu a5,-8(a4)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d2c c.σ c.tick c.steps (0x80006d2c#64) vmi (p + BitVec.ofNat 64 (8*(j+1))) b0
      hgood hpc hmi ha4 hloaded rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr]; rw [hmem]; exact hb0mem) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d30#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006d2c#64) 4 = (0x80006d30#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha4_1 := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- d30: sub a3,a4,a0  → a3 = (p+8(j+1)) - p = ofNat(8(j+1))
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d30 σ1 i1 (c.steps + 1) (0x80006d30#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) p
      hG1 hpc1 hmi1' ha4_1 ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d34#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d30#64) 4 = (0x80006d34#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
  have ha3_2 : σ2.regs.get? Register.x13 = some (BitVec.ofNat 64 (8*(j+1))) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sub_a4_a0_val] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  -- a5 = zext b0 where b0 = byte@(p+8j+0) = m0[p.toNat+8j+0]
  have ha5b : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + 0]?).getD 0)) := by
    rw [ha5_2, show b0 = (m0[p.toNat + 8*j + 0]?).getD 0 from by rw [hb0mem]; rfl]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5b,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, halign, hcstr, hlen, hjlo, hjhi, by omega⟩

/-! ### Generic tail decision transitions

For each offset `k ≤ 5` we have two one-step-family transitions from the `beqz`-PC:
* **exit** (byte `= 0`, i.e. `8j+k = len`): `beqz` taken to the exit-addi PC, then
  `addi a0,a3,-(8-k)` gives `a0 = ofNat len`, and `ret` returns.  We package this via
  a `tail_exit` helper parameterized by the beqz/addi/ret sites.
* **next** (byte `≠ 0`, i.e. `8j+k < len`): `beqz` not taken, then the next `lbu`
  reads byte `k+1` → `TDec (k+1)`.

We handle the six offsets by direct instantiation; offsets 6,7 use the `snez` path. -/

/-- The intermediate "post-addi" state at an exit ret-PC: `a0 = ofNat len`, `x1 = r`,
`mem = m0`, ready for `ret_to_done`. -/
def AtRet (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (retpc : BitVec 64) (c : Config) : Prop :=
  GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some retpc ∧
  c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 len) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2

/-- RAM/window/alignment side facts for an exit ret-PC (all six lie in `[0xd98, 0xdc1)`,
in RAM, below the HTIF window, 4-aligned). -/
theorem exit_ret_side (retpc : BitVec 64) (hpcval : 0x80006d98 ≤ retpc.toNat ∧ retpc.toNat ≤ 0x80006dc0
    ∧ retpc.toNat % 4 = 0) :
    0x80000000 ≤ retpc.toNat ∧ retpc.toNat + 4 ≤ tohostAddr ∧ retpc.toNat % 4 = 0 := by
  have htoh : tohostAddr = 0x8001ad00 := rfl
  obtain ⟨h1, h2, h3⟩ := hpcval
  exact ⟨by omega, by omega, h3⟩

/-- The `beqz a5` guard value from a `TDec j k` byte: `a5 = zext(byte)`, and
`(a5 == 0) = (8j+k = len)` (byte is NUL iff at length). -/
theorem tdec_guard (p : BitVec 64) (len j k : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 p.toNat cs) (hlen : cs.length = len)
    (hkle : 8*j + k ≤ len) :
    ((zero_extend (m := 64) ((m0[p.toNat + 8*j + k]?).getD 0)) == (0#64))
      = decide (8*j + k = len) := by
  obtain ⟨b, hbmem, hbz⟩ := tail_byte_some p len j k cs m0 hcstr hlen hkle
  rw [hbmem, Option.getD_some, zext_beqz]
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  exact hbz

/-- RetBytes for each exit ret-PC from `StrlenLoaded` (all six are `67 80 00 00`). -/
theorem retbytes_d98 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006d98#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006d98 h
  exact show mem[(0x80006d98#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006d98#64 : BitVec 64).toNat = 0x80006d98 from by decide]; exact this

theorem retbytes_da0 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006da0#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006da0 h
  exact show mem[(0x80006da0#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006da0#64 : BitVec 64).toNat = 0x80006da0 from by decide]; exact this

theorem retbytes_da8 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006da8#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006da8 h
  exact show mem[(0x80006da8#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006da8#64 : BitVec 64).toNat = 0x80006da8 from by decide]; exact this

theorem retbytes_db0 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006db0#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006db0 h
  exact show mem[(0x80006db0#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006db0#64 : BitVec 64).toNat = 0x80006db0 from by decide]; exact this

theorem retbytes_db8 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006db8#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006db8 h
  exact show mem[(0x80006db8#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006db8#64 : BitVec 64).toNat = 0x80006db8 from by decide]; exact this

theorem retbytes_dc0 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006dc0#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006dc0 h
  exact show mem[(0x80006dc0#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006dc0#64 : BitVec 64).toNat = 0x80006dc0 from by decide]; exact this

/-- State at an exit-addi PC: `a3 = ofNat(8(j+1))`, `x1 = r`, mem = m0, byte fact
`8j+k = len`. -/
def AtAddi (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (j : Nat) (addipc : BitVec 64) (c : Config) : Prop :=
  GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some addipc ∧
  c.σ.regs.get? Register.x13 = some (BitVec.ofNat 64 (8*(j+1))) ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2

/-- Offset-0 exit-addi `addi a0,a3,-8` (`0xd9c → 0xda0`): `a0 := a3 - 8 = ofNat len`. -/
theorem addi_d9c (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat)
    (hlen : 8*j + 0 = len) :
    Triple (AtAddi r len m0 j (0x80006d9c#64)) (AtRet r len m0 (0x80006da0#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d9c c.σ c.tick c.steps (0x80006d9c#64) vmi (BitVec.ofNat 64 (8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006da0#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006d9c#64) 4 = (0x80006da0#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_val j len 0 (0xff8#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Offset-1 exit-addi `addi a0,a3,-7` (`0xd94 → 0xd98`). -/
theorem addi_d94 (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat)
    (hlen : 8*j + 1 = len) :
    Triple (AtAddi r len m0 j (0x80006d94#64)) (AtRet r len m0 (0x80006d98#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006d94 c.σ c.tick c.steps (0x80006d94#64) vmi (BitVec.ofNat 64 (8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006d98#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006d94#64) 4 = (0x80006d98#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_val j len 1 (0xff9#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Offset-2 exit-addi `addi a0,a3,-6` (`0xdac → 0xdb0`). -/
theorem addi_dac (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat)
    (hlen : 8*j + 2 = len) :
    Triple (AtAddi r len m0 j (0x80006dac#64)) (AtRet r len m0 (0x80006db0#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006dac c.σ c.tick c.steps (0x80006dac#64) vmi (BitVec.ofNat 64 (8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006db0#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006dac#64) 4 = (0x80006db0#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_val j len 2 (0xffa#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Offset-3 exit-addi `addi a0,a3,-5` (`0xda4 → 0xda8`). -/
theorem addi_da4 (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat)
    (hlen : 8*j + 3 = len) :
    Triple (AtAddi r len m0 j (0x80006da4#64)) (AtRet r len m0 (0x80006da8#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006da4 c.σ c.tick c.steps (0x80006da4#64) vmi (BitVec.ofNat 64 (8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006da8#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006da4#64) 4 = (0x80006da8#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_val j len 3 (0xffb#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Offset-4 exit-addi `addi a0,a3,-4` (`0xdb4 → 0xdb8`). -/
theorem addi_db4 (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat)
    (hlen : 8*j + 4 = len) :
    Triple (AtAddi r len m0 j (0x80006db4#64)) (AtRet r len m0 (0x80006db8#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006db4 c.σ c.tick c.steps (0x80006db4#64) vmi (BitVec.ofNat 64 (8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006db8#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006db4#64) 4 = (0x80006db8#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_val j len 4 (0xffc#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-- Offset-5 exit-addi `addi a0,a3,-3` (`0xdbc → 0xdc0`). -/
theorem addi_dbc (r : BitVec 64) (len : Nat) (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat)
    (hlen : 8*j + 5 = len) :
    Triple (AtAddi r len m0 j (0x80006dbc#64)) (AtRet r len m0 (0x80006dc0#64)) := by
  apply Triple.of_step
  intro c ⟨hgood, hloaded, hmem, hpc, ha3, hra, ⟨vmi, hmi⟩, htick⟩
  obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
    site_80006dbc c.σ c.tick c.steps (0x80006dbc#64) vmi (BitVec.ofNat 64 (8*(j+1)))
      hgood hpc hmi ha3 hloaded rfl htick
  have hpc' : σ'.regs.get? Register.PC = some (0x80006dc0#64 : BitVec 64) := by
    have := obs_alu_pc hobs; rwa [show BitVec.addInt (0x80006dbc#64) 4 = (0x80006dc0#64 : BitVec 64) from by decide] at this
  have ha0' : σ'.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [exit_addi_val j len 5 (0xffd#12) (by omega) hlen (by apply BitVec.eq_of_toNat_eq; decide)] at this
  have hra' := obs_alu_other' hobs Register.x1 (by decide) hra
  refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep,
    hG', by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, hpc', ha0', hra',
    obs_alu_minstret hobs, hi'⟩

/-! ### Byte-tail `beqz` decisions → `Done`

At `TDec j k` (`k ≤ 5`) with `8j+k = len` (the NUL byte), `beqz a5` is taken to the
exit-addi block, which computes `a0 = ofNat len`, then `ret`.  We chain the beqz-taken
transition (→ `AtAddi`) with the addi (→ `AtRet`) and `ret_to_done` (→ `Done`). -/

/-- Offset-0 tail exit (`0xd34` beqz taken, `8j = len`) → `Done`. -/
theorem tdec_exit_0 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlen : 8*j + 0 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 0 (0x80006d34#64)) (Done p r len m0) := by
  have hto_addi : Triple (TDec p r len cs m0 j 0 (0x80006d34#64)) (AtAddi r len m0 j (0x80006d9c#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 0]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guard p len j 0 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d34_taken c.σ c.tick c.steps (0x80006d34#64) vmi
        (zero_extend (m := 64) ((m0[p.toNat + 8*j + 0]?).getD 0))
        hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d34#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13) = (0x80006d9c#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other' hobs Register.x13 (by decide) ha3,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_d9c r len m0 j hlen)).seq (ret_to_done p r len m0 (0x80006da0#64) retbytes_da0 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006da0#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006da0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006da0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-! ### Byte-tail `beqz` not-taken → next offset

At `TDec j k` with `8j+k < len` (byte nonzero), `beqz` falls through and the next
`lbu` reads byte `k+1`, reaching `TDec j (k+1)`.  We prove each `k → k+1` step.  These
share a helper `tdec_next` parameterized by the beqz-PC, next-lbu-PC, next-beqz-PC,
the beqz imm (for the fall-through), and the next `lbu` site (via a callback). -/

/-- Generic tail `beqz`-not-taken + next-`lbu` step (`k → k+1`, `k ≤ 5`).
`hlbu` runs the `lbu` at `lbupc` (offset `k+1`, imm sext `-(8-(k+1))`) reading byte
`k+1`; the resulting `TDec (k+1)` sits at `nextbeqzpc`. -/
theorem tdec_next_0 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlt : 8*j + 0 < len) :
    Triple (TDec p r len cs m0 j 0 (0x80006d34#64)) (TDec p r len cs m0 j 1 (0x80006d3c#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 0]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guard p len j 0 cs m0 hcstr hlen' hkle]; simp; omega
  -- d34: beqz a5 not taken → d38
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d34_nottaken c.σ c.tick c.steps (0x80006d34#64) vmi
      (zero_extend (m := 64) ((m0[p.toNat + 8*j + 0]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d38#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d34#64) 4 = (0x80006d38#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- d38: lbu a5,-7(a4) → byte offset 1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 1 hreg hjlo (by omega)
  obtain ⟨b1, hb1mem, _⟩ := tail_byte_some p len j 1 cs m0 hcstr hlen' (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xff9#12)).toNat
      = p.toNat + 8*j + 1 := by
    rw [lbu_addr p j 1 (by omega) (0xff9#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN p (8*j + 1) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d38 σ1 i1 (c.steps + 1) (0x80006d38#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) b1
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb1mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d3c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d38#64) 4 = (0x80006d3c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + 1]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b1 = (m0[p.toNat + 8*j + 1]?).getD 0 from by rw [hb1mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, halgn, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Offset-1 tail exit (`0xd3c` beqz taken, `8j+1 = len`) → `Done`. -/
theorem tdec_exit_1 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlen : 8*j + 1 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 1 (0x80006d3c#64)) (Done p r len m0) := by
  have hto_addi : Triple (TDec p r len cs m0 j 1 (0x80006d3c#64)) (AtAddi r len m0 j (0x80006d94#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 1]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guard p len j 1 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d3c_taken c.σ c.tick c.steps (0x80006d3c#64) vmi
        (zero_extend (m := 64) ((m0[p.toNat + 8*j + 1]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d3c#64 : BitVec 64) + sign_extend (m := 64) (0x0058#13) = (0x80006d94#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other' hobs Register.x13 (by decide) ha3,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_d94 r len m0 j hlen)).seq (ret_to_done p r len m0 (0x80006d98#64) retbytes_d98 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006d98#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006d98#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006d98#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Offset-2 tail exit (`0xd44` beqz taken, `8j+2 = len`) → `Done`. -/
theorem tdec_exit_2 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlen : 8*j + 2 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 2 (0x80006d44#64)) (Done p r len m0) := by
  have hto_addi : Triple (TDec p r len cs m0 j 2 (0x80006d44#64)) (AtAddi r len m0 j (0x80006dac#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 2]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guard p len j 2 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d44_taken c.σ c.tick c.steps (0x80006d44#64) vmi
        (zero_extend (m := 64) ((m0[p.toNat + 8*j + 2]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d44#64 : BitVec 64) + sign_extend (m := 64) (0x0068#13) = (0x80006dac#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other' hobs Register.x13 (by decide) ha3,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_dac r len m0 j hlen)).seq (ret_to_done p r len m0 (0x80006db0#64) retbytes_db0 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006db0#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006db0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006db0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Offset-3 tail exit (`0xd4c` beqz taken, `8j+3 = len`) → `Done`. -/
theorem tdec_exit_3 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlen : 8*j + 3 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 3 (0x80006d4c#64)) (Done p r len m0) := by
  have hto_addi : Triple (TDec p r len cs m0 j 3 (0x80006d4c#64)) (AtAddi r len m0 j (0x80006da4#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 3]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guard p len j 3 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d4c_taken c.σ c.tick c.steps (0x80006d4c#64) vmi
        (zero_extend (m := 64) ((m0[p.toNat + 8*j + 3]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d4c#64 : BitVec 64) + sign_extend (m := 64) (0x0058#13) = (0x80006da4#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other' hobs Register.x13 (by decide) ha3,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_da4 r len m0 j hlen)).seq (ret_to_done p r len m0 (0x80006da8#64) retbytes_da8 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006da8#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006da8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006da8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Offset-4 tail exit (`0xd54` beqz taken, `8j+4 = len`) → `Done`. -/
theorem tdec_exit_4 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlen : 8*j + 4 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 4 (0x80006d54#64)) (Done p r len m0) := by
  have hto_addi : Triple (TDec p r len cs m0 j 4 (0x80006d54#64)) (AtAddi r len m0 j (0x80006db4#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 4]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guard p len j 4 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d54_taken c.σ c.tick c.steps (0x80006d54#64) vmi
        (zero_extend (m := 64) ((m0[p.toNat + 8*j + 4]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d54#64 : BitVec 64) + sign_extend (m := 64) (0x0060#13) = (0x80006db4#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other' hobs Register.x13 (by decide) ha3,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_db4 r len m0 j hlen)).seq (ret_to_done p r len m0 (0x80006db8#64) retbytes_db8 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006db8#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006db8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006db8#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Offset-5 tail exit (`0xd5c` beqz taken, `8j+5 = len`) → `Done`. -/
theorem tdec_exit_5 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlen : 8*j + 5 = len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 5 (0x80006d5c#64)) (Done p r len m0) := by
  have hto_addi : Triple (TDec p r len cs m0 j 5 (0x80006d5c#64)) (AtAddi r len m0 j (0x80006dbc#64)) := by
    apply Triple.of_step
    intro c hSt
    obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
      hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
    have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 5]?).getD 0)) == (0#64)) = true := by
      rw [tdec_guard p len j 5 cs m0 hcstr hlen' hkle]; simp [hlen]
    obtain ⟨σ', i', hstep, hi', hG', hmem', hobs⟩ :=
      site_80006d5c_taken c.σ c.tick c.steps (0x80006d5c#64) vmi
        (zero_extend (m := 64) ((m0[p.toNat + 8*j + 5]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
    have hpceq : (0x80006d5c#64 : BitVec 64) + sign_extend (m := 64) (0x0060#13) = (0x80006dbc#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    refine ⟨⟨σ', i', c.steps + 1⟩, by cases c; exact hstep, hG',
      by rw [hmem']; exact hloaded, by rw [hmem']; exact hmem, ?_,
      obs_btaken_other' hobs Register.x13 (by decide) ha3,
      obs_btaken_other' hobs Register.x1 (by decide) hra,
      obs_btaken_minstret hobs, hi'⟩
    rw [obs_btaken_pc hobs, hpceq]
  refine (hto_addi.seq (addi_dbc r len m0 j hlen)).seq (ret_to_done p r len m0 (0x80006dc0#64) retbytes_dc0 ?_ ?_ ?_ halign)
  all_goals first
    | exact (exit_ret_side (0x80006dc0#64) (by refine ⟨by decide, by decide, by decide⟩)).1
    | exact (exit_ret_side (0x80006dc0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.1
    | exact (exit_ret_side (0x80006dc0#64) (by refine ⟨by decide, by decide, by decide⟩)).2.2

/-- Offset-1 → offset-2 tail advance (`0xd3c` beqz not-taken, `8j+1 < len`). -/
theorem tdec_next_1 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlt : 8*j + 1 < len) :
    Triple (TDec p r len cs m0 j 1 (0x80006d3c#64)) (TDec p r len cs m0 j 2 (0x80006d44#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 1]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guard p len j 1 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d3c_nottaken c.σ c.tick c.steps (0x80006d3c#64) vmi
      (zero_extend (m := 64) ((m0[p.toNat + 8*j + 1]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d40#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d3c#64) 4 = (0x80006d40#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 2 hreg hjlo (by omega)
  obtain ⟨b2, hb2mem, _⟩ := tail_byte_some p len j 2 cs m0 hcstr hlen' (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xffa#12)).toNat
      = p.toNat + 8*j + 2 := by
    rw [lbu_addr p j 2 (by omega) (0xffa#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN p (8*j + 2) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d40 σ1 i1 (c.steps + 1) (0x80006d40#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) b2
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb2mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d44#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d40#64) 4 = (0x80006d44#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + 2]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b2 = (m0[p.toNat + 8*j + 2]?).getD 0 from by rw [hb2mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, halgn, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Offset-2 → offset-3 tail advance (`0xd44` beqz not-taken, `8j+2 < len`). -/
theorem tdec_next_2 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlt : 8*j + 2 < len) :
    Triple (TDec p r len cs m0 j 2 (0x80006d44#64)) (TDec p r len cs m0 j 3 (0x80006d4c#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 2]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guard p len j 2 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d44_nottaken c.σ c.tick c.steps (0x80006d44#64) vmi
      (zero_extend (m := 64) ((m0[p.toNat + 8*j + 2]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d48#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d44#64) 4 = (0x80006d48#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 3 hreg hjlo (by omega)
  obtain ⟨b3, hb3mem, _⟩ := tail_byte_some p len j 3 cs m0 hcstr hlen' (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xffb#12)).toNat
      = p.toNat + 8*j + 3 := by
    rw [lbu_addr p j 3 (by omega) (0xffb#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN p (8*j + 3) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d48 σ1 i1 (c.steps + 1) (0x80006d48#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) b3
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb3mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d4c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d48#64) 4 = (0x80006d4c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + 3]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b3 = (m0[p.toNat + 8*j + 3]?).getD 0 from by rw [hb3mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, halgn, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Offset-3 → offset-4 tail advance (`0xd4c` beqz not-taken, `8j+3 < len`). -/
theorem tdec_next_3 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlt : 8*j + 3 < len) :
    Triple (TDec p r len cs m0 j 3 (0x80006d4c#64)) (TDec p r len cs m0 j 4 (0x80006d54#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 3]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guard p len j 3 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d4c_nottaken c.σ c.tick c.steps (0x80006d4c#64) vmi
      (zero_extend (m := 64) ((m0[p.toNat + 8*j + 3]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d50#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d4c#64) 4 = (0x80006d50#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 4 hreg hjlo (by omega)
  obtain ⟨b4, hb4mem, _⟩ := tail_byte_some p len j 4 cs m0 hcstr hlen' (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xffc#12)).toNat
      = p.toNat + 8*j + 4 := by
    rw [lbu_addr p j 4 (by omega) (0xffc#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN p (8*j + 4) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d50 σ1 i1 (c.steps + 1) (0x80006d50#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) b4
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb4mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d54#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d50#64) 4 = (0x80006d54#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + 4]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b4 = (m0[p.toNat + 8*j + 4]?).getD 0 from by rw [hb4mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, halgn, hcstr, hlen', hjlo, hjhi, by omega⟩

/-- Offset-4 → offset-5 tail advance (`0xd54` beqz not-taken, `8j+4 < len`). -/
theorem tdec_next_4 (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlt : 8*j + 4 < len) :
    Triple (TDec p r len cs m0 j 4 (0x80006d54#64)) (TDec p r len cs m0 j 5 (0x80006d5c#64)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 4]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guard p len j 4 cs m0 hcstr hlen' hkle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d54_nottaken c.σ c.tick c.steps (0x80006d54#64) vmi
      (zero_extend (m := 64) ((m0[p.toNat + 8*j + 4]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d58#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d54#64) 4 = (0x80006d58#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 5 hreg hjlo (by omega)
  obtain ⟨b5, hb5mem, _⟩ := tail_byte_some p len j 5 cs m0 hcstr hlen' (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xffd#12)).toNat
      = p.toNat + 8*j + 5 := by
    rw [lbu_addr p j 5 (by omega) (0xffd#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN p (8*j + 5) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d58 σ1 i1 (c.steps + 1) (0x80006d58#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) b5
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb5mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d5c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d58#64) 4 = (0x80006d5c#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have ha4_2 := obs_alu_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 : σ2.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[p.toNat + 8*j + 5]?).getD 0)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show b5 = (m0[p.toNat + 8*j + 5]?).getD 0 from by rw [hb5mem]; rfl] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha3_2, ha5_2,
    ha4_2, hra_2, ⟨vmi2, hmi2'⟩, hi2, hreg, halgn, hcstr, hlen', hjlo, hjhi, by omega⟩

/-! ### The `snez` tail path (offsets 6, 7)

If bytes `0..5` are all nonzero (`8j+5 < len`, so `len ∈ {8j+6, 8j+7}`), the tail
skips the `beqz` ladder: `0xd60` loads byte 6, `0xd64 snez a0,a5` (`a0 = byte6 ≠ 0 ? 1
: 0`), `0xd68 add a0,a0,a3` (`+ 8(j+1)`), `0xd6c addi a0,a0,-2`, `0xd70 ret`.  The
result is `a0 = snez(byte6) + 8(j+1) - 2 = len`: for `len = 8j+6`, byte 6 is the NUL so
`snez = 0` giving `8j+6`; for `len = 8j+7`, byte 6 is a char so `snez = 1` giving
`8j+7`. -/

/-- The `snez` value as a `Nat`: `1` iff byte `≠ 0`, else `0`. -/
theorem snez_toNat (b : BitVec 8) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b)))).toNat
      = (if b = 0 then 0 else 1) := by
  rcases (Decidable.em (b = 0)) with h | h
  · subst h; decide
  · simp only [if_neg h]
    have hpos : 0 < (zero_extend (m := 64) b).toNat := by
      rcases Nat.eq_zero_or_pos (zero_extend (m := 64) b).toNat with hz | hp
      · exfalso; apply h; apply BitVec.eq_of_toNat_eq
        simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
          Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using hz
      · exact hp
    have : zopz0zI_u (0#64) (zero_extend (m := 64) b) = true := by
      unfold zopz0zI_u Sail.BitVec.toNatInt
      simp only [decide_eq_true_eq, Int.ofNat_eq_natCast]
      rw [show (0#64 : BitVec 64).toNat = 0 from rfl]; exact_mod_cast hpos
    rw [this]; rfl

/-- Final `snez`-path arithmetic: `snez_val + ofNat(8(j+1)) + sext(-2) = ofNat len`,
where `snez_val = (byte6 = 0 ? 0 : 1)` and `byte6 = 0 ↔ 8j+6 = len` (as `8j+5 < len <
8(j+1)`, so `len ∈ {8j+6, 8j+7}`). -/
theorem snez_final (p : BitVec 64) (len j : Nat) (b6 : BitVec 8)
    (hlo : 8*j + 5 < len) (hhi : len < 8*(j+1)) (hnw : 8*(j+1) < 2^64)
    (hb6 : b6 = 0 ↔ 8*j + 6 = len) :
    (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))
      + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xffe#12) = BitVec.ofNat 64 len := by
  have hsext : (sign_extend (m := 64) (0xffe#12) : BitVec 64) = -(BitVec.ofNat 64 2) := by
    apply BitVec.eq_of_toNat_eq; decide
  -- snez_val as ofNat
  have hsnez : (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))).toNat
      = (if b6 = 0 then 0 else 1) := snez_toNat b6
  -- resolve which case
  have hval : (if b6 = 0 then (0:Nat) else 1) + 8*(j+1) - 2 = len := by
    by_cases h : b6 = 0
    · have := hb6.mp h; rw [if_pos h]; omega
    · have hne : ¬ (8*j + 6 = len) := fun hc => h (hb6.mpr hc); rw [if_neg h]; omega
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_add, BitVec.toNat_add, hsnez, hsext, BitVec.toNat_neg]
  have h2 : (2#64 : BitVec 64).toNat = 2 := rfl
  rw [h2, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (show len < 2^64 from by omega),
    Nat.mod_eq_of_lt (show 8*(j+1) < 2^64 from hnw)]
  have hm2 : (2^64 - 2) % 2^64 = 2^64 - 2 := Nat.mod_eq_of_lt (by omega)
  rw [hm2]
  by_cases h : b6 = 0
  · rw [if_pos h] at hval ⊢
    rw [Nat.mod_eq_of_lt (show 0 + 8*(j+1) < 2^64 from by omega)]
    omega
  · rw [if_neg h] at hval ⊢
    rw [Nat.mod_eq_of_lt (show 1 + 8*(j+1) < 2^64 from by omega)]
    omega

/-- RetBytes for `0x80006d70` (the `snez`-path ret). -/
theorem retbytes_d70 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006d70#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006d70 h
  exact show mem[(0x80006d70#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006d70#64 : BitVec 64).toNat = 0x80006d70 from by decide]
       exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩

/-- The `snez` tail path (`0xd5c` beqz not-taken → `0xd60`/`d64`/`d68`/`d6c`/`d70`):
from `TDec j 5 d5c` with `8j+5 < len` reaches `Done` with `a0 = ofNat len`. -/
theorem tdec_snez (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (hlt : 8*j + 5 < len) (halign : r.toNat % 4 = 0) :
    Triple (TDec p r len cs m0 j 5 (0x80006d5c#64)) (Done p r len m0) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, halgn, hcstr, hlen', hjlo, hjhi, hkle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[p.toNat + 8*j + 5]?).getD 0)) == (0#64)) = false := by
    rw [tdec_guard p len j 5 cs m0 hcstr hlen' hkle]; simp; omega
  -- d5c: beqz not taken → d60
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d5c_nottaken c.σ c.tick c.steps (0x80006d5c#64) vmi
      (zero_extend (m := 64) ((m0[p.toNat + 8*j + 5]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d60#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d5c#64) 4 = (0x80006d60#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_bnottaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- d60: lbu a5,-2(a4) → byte offset 6
  obtain ⟨htlo, hthi, hthtif⟩ := tail_lbu_bounds p len j 6 hreg hjlo (by omega)
  obtain ⟨b6, hb6mem, hb6z⟩ := tail_byte_some p len j 6 cs m0 hcstr hlen' (by omega)
  have haddr : ((p + BitVec.ofNat 64 (8*(j+1))) + sign_extend (m := 64) (0xffe#12)).toNat
      = p.toNat + 8*j + 6 := by
    rw [lbu_addr p j 6 (by omega) (0xffe#12) (by apply BitVec.eq_of_toNat_eq; decide)]
    exact ptrN p (8*j + 6) (by have := hreg.nowrap; omega)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d60 σ1 i1 (c.steps + 1) (0x80006d60#64) vmi1 (p + BitVec.ofNat 64 (8*(j+1))) b6
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl
      (by rw [haddr]; exact htlo) (by rw [haddr]; exact hthi) (by rw [haddr]; exact hthtif)
      (by rw [haddr, hmem1, hmem]; exact hb6mem) hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d64#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d60#64) 4 = (0x80006d64#64 : BitVec 64) from by decide] at this
  have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- d64: snez a0,a5 → a0 = (a5 ≠ 0 ? 1 : 0)
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d64 σ2 i2 (c.steps + 1 + 1) (0x80006d64#64) vmi2 (zero_extend (m := 64) b6)
      hG2 hpc2 hmi2' ha5_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d68#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d64#64) 4 = (0x80006d68#64 : BitVec 64) from by decide] at this
  have ha3_3 := obs_alu_other' hobs3 Register.x13 (by decide) ha3_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha0_3 := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  -- d68: add a0,a0,a3 → a0 = snez_val + ofNat(8(j+1))
  obtain ⟨σ4, i4, hs4, hi4, hG4, hmem4, hobs4⟩ :=
    site_80006d68 σ3 i3 (c.steps + 1 + 1 + 1) (0x80006d68#64) vmi3
      (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6))))
      (BitVec.ofNat 64 (8*(j+1)))
      hG3 hpc3 hmi3' ha0_3 ha3_3 (by rw [hmem3, hmem2, hmem1]; exact hloaded) rfl hi3
  have hpc4 : σ4.regs.get? Register.PC = some (0x80006d6c#64 : BitVec 64) := by
    have := obs_alu_pc hobs4; rwa [show BitVec.addInt (0x80006d68#64) 4 = (0x80006d6c#64 : BitVec 64) from by decide] at this
  have hra_4 := obs_alu_other' hobs4 Register.x1 (by decide) hra_3
  have ha0_4 := obs_alu_rd hobs4 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi4, hmi4'⟩ := obs_alu_minstret hobs4
  -- d6c: addi a0,a0,-2 → a0 = snez_val + ofNat(8(j+1)) - 2 = ofNat len
  obtain ⟨σ5, i5, hs5, hi5, hG5, hmem5, hobs5⟩ :=
    site_80006d6c σ4 i4 (c.steps + 1 + 1 + 1 + 1) (0x80006d6c#64) vmi4
      ((zero_extend (m := 64) (bool_to_bit (zopz0zI_u (0#64) (zero_extend (m := 64) b6)))) + BitVec.ofNat 64 (8*(j+1)))
      hG4 hpc4 hmi4' ha0_4 (by rw [hmem4, hmem3, hmem2, hmem1]; exact hloaded) rfl hi4
  have hpc5 : σ5.regs.get? Register.PC = some (0x80006d70#64 : BitVec 64) := by
    have := obs_alu_pc hobs5; rwa [show BitVec.addInt (0x80006d6c#64) 4 = (0x80006d70#64 : BitVec 64) from by decide] at this
  have hra_5 := obs_alu_other' hobs5 Register.x1 (by decide) hra_4
  have ha0_5 : σ5.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs5 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [snez_final p len j b6 hlt hjhi (by have := hreg.nowrap; omega)
      (by rw [hb6z])] at this
  obtain ⟨vmi5, hmi5'⟩ := obs_alu_minstret hobs5
  have hmem5eq : σ5.mem = c.σ.mem := by rw [hmem5, hmem4, hmem3, hmem2, hmem1]
  -- d70: ret → Done
  have hAtRet : AtRet r len m0 (0x80006d70#64) ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ := by
    refine ⟨hG5, by rw [hmem5eq]; exact hloaded, by rw [hmem5eq]; exact hmem, hpc5, ha0_5, hra_5,
      ⟨vmi5, hmi5'⟩, hi5⟩
  obtain ⟨cf, hsf, hDone⟩ := ret_to_done p r len m0 (0x80006d70#64) retbytes_d70
    (by decide) (by decide) (by decide)
    halign ⟨σ5, i5, c.steps + 1 + 1 + 1 + 1 + 1⟩ hAtRet
  refine ⟨cf, ?_, hDone⟩
  exact (((((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans
    (Steps.single hs4)).trans (Steps.single hs5)).trans hsf

/-! ### Byte-tail assembly (`WTail → Done`)

Dispatch on `i₀ = len - 8j ∈ {0,…,7}`.  For `i₀ ≤ 5` the tail scans offsets `0..i₀-1`
(each nonzero, via `tdec_next`) then exits at offset `i₀` (`tdec_exit`).  For `i₀ ∈
{6,7}` it scans through offset 5 then takes the `snez` path (`tdec_snez`). -/
theorem tail_to_done (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (j : Nat) (halign : r.toNat % 4 = 0) :
    Triple (WTail p r len cs m0 j) (Done p r len m0) := by
  -- We case on i₀ = len - 8j. WTail gives 8j ≤ len < 8(j+1), so i₀ ∈ {0,…,7}.
  refine (tail_entry p r len cs m0 j).seq ?_
  -- from TDec j 0 d34 to Done, by cases on len - 8j
  intro c hSt
  have hjlo := hSt.jlo; have hjhi := hSt.jhi
  have hi0 : len - 8*j < 8 := by omega
  -- dispatch
  rcases (show len = 8*j + 0 ∨ len = 8*j + 1 ∨ len = 8*j + 2 ∨ len = 8*j + 3 ∨
      len = 8*j + 4 ∨ len = 8*j + 5 ∨ len = 8*j + 6 ∨ len = 8*j + 7 from by omega)
    with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · exact tdec_exit_0 p r len cs m0 j (by omega) halign c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      (tdec_exit_1 p r len cs m0 j (by omega) halign)) c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      ((tdec_next_1 p r len cs m0 j (by omega)).seq
      (tdec_exit_2 p r len cs m0 j (by omega) halign))) c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      ((tdec_next_1 p r len cs m0 j (by omega)).seq
      ((tdec_next_2 p r len cs m0 j (by omega)).seq
      (tdec_exit_3 p r len cs m0 j (by omega) halign)))) c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      ((tdec_next_1 p r len cs m0 j (by omega)).seq
      ((tdec_next_2 p r len cs m0 j (by omega)).seq
      ((tdec_next_3 p r len cs m0 j (by omega)).seq
      (tdec_exit_4 p r len cs m0 j (by omega) halign))))) c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      ((tdec_next_1 p r len cs m0 j (by omega)).seq
      ((tdec_next_2 p r len cs m0 j (by omega)).seq
      ((tdec_next_3 p r len cs m0 j (by omega)).seq
      ((tdec_next_4 p r len cs m0 j (by omega)).seq
      (tdec_exit_5 p r len cs m0 j (by omega) halign)))))) c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      ((tdec_next_1 p r len cs m0 j (by omega)).seq
      ((tdec_next_2 p r len cs m0 j (by omega)).seq
      ((tdec_next_3 p r len cs m0 j (by omega)).seq
      ((tdec_next_4 p r len cs m0 j (by omega)).seq
      (tdec_snez p r len cs m0 j (by omega) halign)))))) c hSt
  · exact ((tdec_next_0 p r len cs m0 j (by omega)).seq
      ((tdec_next_1 p r len cs m0 j (by omega)).seq
      ((tdec_next_2 p r len cs m0 j (by omega)).seq
      ((tdec_next_3 p r len cs m0 j (by omega)).seq
      ((tdec_next_4 p r len cs m0 j (by omega)).seq
      (tdec_snez p r len cs m0 j (by omega) halign)))))) c hSt

/-- `WAtTail → Done`: run the byte tail from whichever iteration `j` reached it. -/
theorem wattail_to_done (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (WAtTail p r len cs m0) (Done p r len m0) :=
  Triple.exists_pre (fun j => tail_to_done p r len cs m0 j halign)

/-! ### Byte-at-a-time alignment head (`0xd74 … 0xd90`), NUL-in-head exit

For the unaligned entry path (`bnez a5` taken at `0xcf8` → `0xd78`), the code peels
bytes one at a time until either it finds the NUL (this section) or reaches an
8-aligned pointer (then the word loop scans the rest — that exit requires the
offset-generalized word loop, noted at the end of file).

Head-loop head `0xd78`, having peeled `m` bytes (`a4 = base + m`, `m ≤ len`, no NUL in
`[base, base+m)`, `(base+m) % 8 ≠ 0` — else we would have exited to the word loop):
`0xd78 lbu a5,0(a4)` loads byte `base+m`, `0xd7c addi a4,a4,1`, `0xd80 andi a3,a4,7`,
`0xd84 bnez a5,d74`.  If the byte is `0` (`m = len`), `bnez` falls through to `0xd88`
`sub a4,a4,a0`; `0xd8c addi a0,a4,-1`; `0xd90 ret`, returning `a0 = (m+1) - 1 = m = len`.

`HSt base r len cs m0 m`: the head-loop head observation at `0xd78`.  We prove the
NUL-exit (`byte = 0` ⇒ `Done`) here; the alignment-exit is the remaining item. -/

/-- Head-loop head `0xd78`, having peeled `m` bytes without a NUL (`m ≤ len`). -/
structure HSt (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d78#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some base
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 m)
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  mle : m ≤ len

/-- RAM/window/byte facts for the head `lbu a5,0(a4)` at `a4 = base+m` (`m ≤ len`). -/
theorem head_lbu_bounds (base : BitVec 64) (len m : Nat) (hreg : StrRegions base len)
    (hm : m ≤ len) :
    (base + BitVec.ofNat 64 m).toNat = base.toNat + m ∧
    0x80000000 ≤ ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat ∧
    ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ 0x100000000 ∧
    (((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat + 1 ≤ tohostAddr
      ∨ tohostAddr + 8 ≤ ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat) := by
  have htn : (base + BitVec.ofNat 64 m).toNat = base.toNat + m :=
    ptrN base m (by have := hreg.nowrap; omega)
  have hlo := hreg.lo; have hhi := hreg.hi; have hh := hreg.htif
  have htoh : tohostAddr = 0x8001ad00 := rfl
  have hs0 : ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat = base.toNat + m := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero, htn]
  refine ⟨htn, ?_, ?_, ?_⟩ <;> rw [hs0]
  · omega
  · omega
  · rcases hh with h | h
    · left; omega
    · right; omega

/-- The head byte at `base+m` (`m ≤ len`) is mapped, and is the NUL iff `m = len`. -/
theorem head_byte_some (base : BitVec 64) (len m : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 base.toNat cs) (hlen : cs.length = len)
    (hm : m ≤ len) :
    ∃ b : BitVec 8, m0[base.toNat + m]? = some b ∧ (b = 0 ↔ m = len) := by
  by_cases heq : m = len
  · refine ⟨0, ?_, by simp [heq]⟩
    have hnul := cstr_byte_nul m0 hcstr; rw [hlen] at hnul
    rw [heq]; exact hnul
  · obtain ⟨b, hb, hbne⟩ := cstr_byte_ne m0 hcstr m (by omega)
    refine ⟨b, hb, ?_⟩
    constructor
    · intro h; exact absurd h hbne
    · intro h; omega

/-- State at `0xd84` (`bnez a5`) after the head body of peel-step `m`: `a5 =
byte@(base+m)`, `a4 = base+(m+1)`, `a3 = (base+(m+1)) & 7`, `a0 = base`. -/
structure HDec (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (c : Config) : Prop where
  good : GoodState c.σ
  loaded : StrlenLoaded c.σ.mem
  mem : c.σ.mem = m0
  pc : c.σ.regs.get? Register.PC = some (0x80006d84#64 : BitVec 64)
  a0 : c.σ.regs.get? Register.x10 = some base
  a3 : c.σ.regs.get? Register.x13 = some ((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12))
  a5 : c.σ.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0))
  a4 : c.σ.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (m+1))
  ra : c.σ.regs.get? Register.x1 = some r
  minstret : ∃ v, c.σ.regs.get? Register.minstret = some v
  tick : c.tick < 2
  regions : StrRegions base len
  cstr : CStr m0 base.toNat cs
  hlen : cs.length = len
  mle : m ≤ len

/-- `(base + ofNat m) + sext 1 = base + ofNat (m+1)` (the `addi a4,a4,1` increment). -/
theorem a4_incr1 (base : BitVec 64) (m : Nat) :
    (base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x001#12) = base + BitVec.ofNat 64 (m+1) := by
  rw [show (sign_extend (m := 64) (0x001#12) : BitVec 64) = BitVec.ofNat 64 1 from by
        apply BitVec.eq_of_toNat_eq; decide, BitVec.add_assoc, ← BitVec.ofNat_add]

/-- Head body (`0xd78 → 0xd84`): `lbu a5,0(a4); addi a4,a4,1; andi a3,a4,7`. -/
theorem head_body (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) :
    Triple (HSt base r len cs m0 m) (HDec base r len cs m0 m) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hcstr, hlen, hmle⟩ := hSt
  obtain ⟨htn, hlo, hhi, hhtif⟩ := head_lbu_bounds base len m hreg hmle
  obtain ⟨b, hbmem, _⟩ := head_byte_some base len m cs m0 hcstr hlen hmle
  have haddr : ((base + BitVec.ofNat 64 m) + sign_extend (m := 64) (0x000#12)).toNat = base.toNat + m := by
    rw [show (sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by apply BitVec.eq_of_toNat_eq; decide,
      BitVec.add_zero, htn]
  -- d78: lbu a5,0(a4)
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d78 c.σ c.tick c.steps (0x80006d78#64) vmi (base + BitVec.ofNat 64 m) b
      hgood hpc hmi ha4 hloaded rfl hlo hhi hhtif
      (by rw [haddr, hmem]; exact hbmem) htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d7c#64 : BitVec 64) := by
    have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006d78#64) 4 = (0x80006d7c#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_alu_other' hobs1 Register.x10 (by decide) ha0
  have ha4_1 := obs_alu_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
  have ha5_1 := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
  -- d7c: addi a4,a4,1  → a4 = base+(m+1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d7c σ1 i1 (c.steps + 1) (0x80006d7c#64) vmi1 (base + BitVec.ofNat 64 m)
      hG1 hpc1 hmi1' ha4_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d80#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d7c#64) 4 = (0x80006d80#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha5_2 := obs_alu_other' hobs2 Register.x15 (by decide) ha5_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (base + BitVec.ofNat 64 (m+1)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [a4_incr1 base m] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- d80: andi a3,a4,7  → a3 = a4 & 7
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d80 σ2 i2 (c.steps + 1 + 1) (0x80006d80#64) vmi2 (base + BitVec.ofNat 64 (m+1))
      hG2 hpc2 hmi2' ha4_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d84#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d80#64) 4 = (0x80006d84#64 : BitVec 64) from by decide] at this
  have ha0_3 := obs_alu_other' hobs3 Register.x10 (by decide) ha0_2
  have ha4_3 := obs_alu_other' hobs3 Register.x14 (by decide) ha4_2
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha5_3 := obs_alu_other' hobs3 Register.x15 (by decide) ha5_2
  have ha3_3 := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  have ha5b : σ3.regs.get? Register.x15 = some (zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) := by
    rw [ha5_3, show b = (m0[base.toNat + m]?).getD 0 from by rw [hbmem]; rfl]
  refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
    ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3),
    hG3, by rw [hmem3eq]; exact hloaded, by rw [hmem3eq]; exact hmem, hpc3, ha0_3, ha3_3, ha5b,
    ha4_3, hra_3, ⟨vmi3, hmi3'⟩, hi3, hreg, hcstr, hlen, hmle⟩

/-- The head `bnez a5` guard: `a5 = zext(byte@(base+m))`, so `(a5 != 0) = (m ≠ len)`
(byte is nonzero iff before the NUL). -/
theorem hdec_guard (base : BitVec 64) (len m : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (hcstr : CStr m0 base.toNat cs) (hlen : cs.length = len)
    (hmle : m ≤ len) :
    ((zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) != (0#64)) = decide (m ≠ len) := by
  obtain ⟨b, hbmem, hbz⟩ := head_byte_some base len m cs m0 hcstr hlen hmle
  rw [hbmem, Option.getD_some]
  rw [Bool.eq_iff_iff, bne_iff_ne, ne_eq, decide_eq_true_eq]
  constructor
  · intro h hc; apply h; rw [hbz.mpr hc]; rfl
  · intro h hc
    have : (zero_extend (m := 64) b).toNat = 0 := by rw [hc]; rfl
    apply h; apply hbz.mp; apply BitVec.eq_of_toNat_eq
    simpa [zero_extend, Sail.BitVec.zeroExtend, BitVec.toNat_setWidth,
      Nat.mod_eq_of_lt (show b.toNat < 2^64 from by have := b.isLt; omega)] using this

/-- RetBytes for `0x80006d90` (the head NUL-exit ret). -/
theorem retbytes_d90 (mem : Std.ExtHashMap Nat (BitVec 8)) (h : StrlenLoaded mem) :
    RetBytes mem (0x80006d90#64).toNat := by
  have := Vsa.Sim.Code.strlen_at_80006d90 h
  exact show mem[(0x80006d90#64 : BitVec 64).toNat]? = _ ∧ _ from
    by rw [show (0x80006d90#64 : BitVec 64).toNat = 0x80006d90 from by decide]
       exact ⟨this.1, this.2.1, this.2.2.1, this.2.2.2⟩

/-- Head NUL-exit (`0xd84` bnez not-taken, `m = len`): `0xd88 sub a4,a4,a0`
(`a4 = m+1`), `0xd8c addi a0,a4,-1` (`a0 = m = len`), `0xd90 ret` → `Done`. -/
theorem head_nul_exit (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (hm : m = len) (halign : r.toNat % 4 = 0) :
    Triple (HDec base r len cs m0 m) (Done base r len m0) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hcstr, hlen, hmle⟩ := hSt
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) != (0#64)) = false := by
    rw [hdec_guard base len m cs m0 hcstr hlen hmle]; simp [hm]
  -- d84: bnez a5 not taken → d88
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d84_nottaken c.σ c.tick c.steps (0x80006d84#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d88#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006d84#64) 4 = (0x80006d88#64 : BitVec 64) from by decide] at this
  have ha0_1 := obs_bnottaken_other' hobs1 Register.x10 (by decide) ha0
  have ha4_1 := obs_bnottaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
  -- d88: sub a4,a4,a0  → a4 = (base+(m+1)) - base = ofNat(m+1)
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d88 σ1 i1 (c.steps + 1) (0x80006d88#64) vmi1 (base + BitVec.ofNat 64 (m+1)) base
      hG1 hpc1 hmi1' ha4_1 ha0_1 (by rw [hmem1]; exact hloaded) rfl hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d8c#64 : BitVec 64) := by
    have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006d88#64) 4 = (0x80006d8c#64 : BitVec 64) from by decide] at this
  have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
  have ha4_2 : σ2.regs.get? Register.x14 = some (BitVec.ofNat 64 (m+1)) := by
    have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [sub_a4_a0_val] at this
  obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
  -- d8c: addi a0,a4,-1  → a0 = ofNat(m+1) - 1 = ofNat m = ofNat len
  obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
    site_80006d8c σ2 i2 (c.steps + 1 + 1) (0x80006d8c#64) vmi2 (BitVec.ofNat 64 (m+1))
      hG2 hpc2 hmi2' ha4_2 (by rw [hmem2, hmem1]; exact hloaded) rfl hi2
  have hpc3 : σ3.regs.get? Register.PC = some (0x80006d90#64 : BitVec 64) := by
    have := obs_alu_pc hobs3; rwa [show BitVec.addInt (0x80006d8c#64) 4 = (0x80006d90#64 : BitVec 64) from by decide] at this
  have hra_3 := obs_alu_other' hobs3 Register.x1 (by decide) hra_2
  have ha0_3 : σ3.regs.get? Register.x10 = some (BitVec.ofNat 64 len) := by
    have := obs_alu_rd hobs3 (by decide) (by decide) (by decide) (by decide) (by decide)
    rwa [show (BitVec.ofNat 64 (m+1)) + sign_extend (m := 64) (0xfff#12) = BitVec.ofNat 64 len from by
      rw [show (sign_extend (m := 64) (0xfff#12) : BitVec 64) = -(BitVec.ofNat 64 1) from by
            apply BitVec.eq_of_toNat_eq; decide, BitVec.add_neg_eq_sub, ofNat_sub (m+1) 1 (by omega),
          show (m+1) - 1 = len from by omega]] at this
  obtain ⟨vmi3, hmi3'⟩ := obs_alu_minstret hobs3
  have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
  have hAtRet : AtRet r len m0 (0x80006d90#64) ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ :=
    ⟨hG3, by rw [hmem3eq]; exact hloaded, by rw [hmem3eq]; exact hmem, hpc3, ha0_3, hra_3,
      ⟨vmi3, hmi3'⟩, hi3⟩
  obtain ⟨cf, hsf, hDone⟩ := ret_to_done base r len m0 (0x80006d90#64) retbytes_d90
    (by decide) (by decide) (by decide) halign ⟨σ3, i3, c.steps + 1 + 1 + 1⟩ hAtRet
  exact ⟨cf, (((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3)).trans hsf, hDone⟩


/-- The `beqz a3` alignment guard: `a3 = (base+(m+1)) & 7`, so `(a3 == 0) = decide(
(base.toNat + (m+1)) % 8 = 0)` — true iff the advanced pointer is 8-aligned. -/
theorem head_align_guard (base : BitVec 64) (m : Nat) (hnw : base.toNat + (m+1) < 2^64) :
    (((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12)) == (0#64))
      = decide ((base.toNat + (m+1)) % 8 = 0) := by
  rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
  have hb : ((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12)).toNat
      = (base.toNat + (m+1)) % 8 := by
    rw [BitVec.toNat_and, show (sign_extend (m := 64) (0x007#12) : BitVec 64).toNat = 7 from by decide,
      show (7:Nat)=2^3-1 from rfl, Nat.and_two_pow_sub_one_eq_mod, show (2:Nat)^3=8 from rfl,
      ptrN base (m+1) hnw]
  constructor
  · intro h
    have hz : ((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12)).toNat = 0 := by
      rw [h]; rfl
    rw [hb] at hz; exact hz
  · intro h; apply BitVec.eq_of_toNat_eq; rw [hb, h]; rfl

/-- Head "continue peeling" back-edge (`0xd84` bnez taken, `m < len`, then `0xd74`
beqz not-taken, pointer `base+(m+1)` not yet aligned): loops back to `0xd78` with
`HSt (m+1)`. -/
theorem head_continue (base r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (m : Nat) (hlt : m < len)
    (hnal : (base.toNat + (m+1)) % 8 ≠ 0) :
    Triple (HDec base r len cs m0 m) (HSt base r len cs m0 (m+1)) := by
  intro c hSt
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, ha3, ha5, ha4, hra, ⟨vmi, hmi⟩, htick,
    hreg, hcstr, hlen, hmle⟩ := hSt
  have hnw : base.toNat + (m+1) < 2^64 := by have := hreg.nowrap; omega
  -- d84: bnez a5 taken → d74
  have hv : ((zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) != (0#64)) = true := by
    rw [hdec_guard base len m cs m0 hcstr hlen hmle]; simp; omega
  obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
    site_80006d84_taken c.σ c.tick c.steps (0x80006d84#64) vmi
      (zero_extend (m := 64) ((m0[base.toNat + m]?).getD 0)) hgood hpc hmi ha5 hloaded rfl hv htick
  have hpceq1 : (0x80006d84#64 : BitVec 64) + sign_extend (m := 64) (0x1ff0#13) = (0x80006d74#64 : BitVec 64) := by
    apply BitVec.eq_of_toNat_eq; decide
  have hpc1 : σ1.regs.get? Register.PC = some (0x80006d74#64 : BitVec 64) := by
    rw [obs_btaken_pc hobs1, hpceq1]
  have ha0_1 := obs_btaken_other' hobs1 Register.x10 (by decide) ha0
  have ha3_1 := obs_btaken_other' hobs1 Register.x13 (by decide) ha3
  have ha4_1 := obs_btaken_other' hobs1 Register.x14 (by decide) ha4
  have hra_1 := obs_btaken_other' hobs1 Register.x1 (by decide) hra
  obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
  -- d74: beqz a3 not taken (not aligned) → d78
  have hv2 : (((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12)) == (0#64)) = false := by
    rw [head_align_guard base m hnw]; simp [hnal]
  obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
    site_80006d74_nottaken σ1 i1 (c.steps + 1) (0x80006d74#64) vmi1
      ((base + BitVec.ofNat 64 (m+1)) &&& sign_extend (m := 64) (0x007#12))
      hG1 hpc1 hmi1' ha3_1 (by rw [hmem1]; exact hloaded) rfl hv2 hi1
  have hpc2 : σ2.regs.get? Register.PC = some (0x80006d78#64 : BitVec 64) := by
    have := obs_bnottaken_pc hobs2; rwa [show BitVec.addInt (0x80006d74#64) 4 = (0x80006d78#64 : BitVec 64) from by decide] at this
  have ha0_2 := obs_bnottaken_other' hobs2 Register.x10 (by decide) ha0_1
  have ha4_2 := obs_bnottaken_other' hobs2 Register.x14 (by decide) ha4_1
  have hra_2 := obs_bnottaken_other' hobs2 Register.x1 (by decide) hra_1
  obtain ⟨vmi2, hmi2'⟩ := obs_bnottaken_minstret hobs2
  have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
  refine ⟨⟨σ2, i2, c.steps + 1 + 1⟩, (Steps.single hs1).trans (Steps.single hs2),
    hG2, by rw [hmem2eq]; exact hloaded, by rw [hmem2eq]; exact hmem, hpc2, ha0_2, ha4_2, hra_2,
    ⟨vmi2, hmi2'⟩, hi2, hreg, hcstr, hlen, by omega⟩

/-! ## The aligned-path `strlen` spec (`Pre → Done`)

For the 8-aligned fast path: entry + magic setup → word loop → byte tail → return.
`r` must be 4-aligned (so `ret`'s bit-0 clear is a no-op). -/
theorem strlen_aligned_spec (p r : BitVec 64) (len : Nat) (cs : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (halign : r.toNat % 4 = 0) :
    Triple (Pre p r len cs m0) (Done p r len m0) :=
  ((entry_aligned p r len cs m0).seq
    ((fun c hc => wloop_to_tail p r len cs m0 c (Or.inl hc)) :
      Triple (WAtHead p r len cs m0) (WAtTail p r len cs m0))).seq
    (wattail_to_done p r len cs m0 halign)

/-! ## Top-level `strlen` specification

`strlen_pre`/`strlen_post` package the prompt's P/Q.  The precondition pins the
entry configuration (`PC = 0x80006cf0`, `x10 = p`, `x1 = r` 4-aligned, `mem = m0`), a
`CString m0 p s` string of length `s.length`, and the `StrRegions` disjointness /
no-wrap side conditions.  The postcondition returns to `r` with `x10 = ofNat
s.length`, `x1 = r`, `mem = m0` (strlen never stores).

`strlen_spec` is proved here for the **8-aligned fast path** (`p.toNat % 8 = 0`), the
common case the caller controls; it composes the fully verified entry, magic setup,
word loop, byte tail, and exit blocks.  The unaligned head-peel path is discussed in
the closing note. -/

/-- Top-level precondition (8-aligned fast path). -/
def strlen_pre (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧ StrlenLoaded c.σ.mem ∧ c.σ.mem = m0 ∧
  c.σ.regs.get? Register.PC = some (0x80006cf0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some p ∧ c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  StrRegions p s.length ∧ p.toNat % 8 = 0 ∧ CString m0 p.toNat s ∧ r.toNat % 4 = 0

/-- Top-level postcondition: returned to `r` with `x10 = ofNat s.length`. -/
def strlen_post (r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (c : Config) : Prop :=
  GoodState c.σ ∧ c.σ.regs.get? Register.PC = some r ∧
  c.σ.regs.get? Register.x10 = some (BitVec.ofNat 64 s.length) ∧
  c.σ.regs.get? Register.x1 = some r ∧ c.σ.mem = m0

/-- **`strlen` total-correctness spec (8-aligned fast path).**  From `strlen_pre` the
machine runs to `strlen_post`: it returns to `r` with `x10 = s.length` and memory
unchanged.  Composes `strlen_aligned_spec` after bridging `CString`'s existential to
the concrete char-list ghost. -/
theorem strlen_spec (p r : BitVec 64) (s : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) :
    Triple (strlen_pre p r s m0) (strlen_post r s m0) := by
  intro c hpre
  obtain ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, halign, hcstring, halignr⟩ := hpre
  obtain ⟨cs, hcstr, hlens⟩ := cstring_length m0 p.toNat s hcstring
  -- Pre p r s.length cs m0 (with len = s.length = cs.length)
  have hPre : Pre p r s.length cs m0 c :=
    ⟨hgood, hloaded, hmem, hpc, ha0, hra, hmi, htick, hreg, halign, hcstr, hlens.symm⟩
  obtain ⟨c', hsteps, hdone⟩ := strlen_aligned_spec p r s.length cs m0 halignr c hPre
  obtain ⟨hG', hpc', ha0', hra', hmem'⟩ := hdone
  exact ⟨c', hsteps, hG', hpc', ha0', hra', hmem'⟩

/-! ## Unaligned head-peel path — status

The byte-at-a-time alignment head (`0xd74 … 0xd90`) is fully modelled: `head_body`
(`0xd78 → 0xd84`), `head_nul_exit` (`0xd84` bnez not-taken, `m = len` ⇒ `Done` with
`a0 = m = len`), and `head_continue` (`0xd84` taken + `0xd74` not-taken ⇒ `HSt (m+1)`).

Two items complete the unaligned path (`bnez a5` taken at `0xcf8`):

1. **Head loop assembly** (`Triple.loop` over `HSt m ∨ Done`, measure `len + 1 - m`,
   PC-guarded at `0xd78`): straightforward from `head_body`/`head_nul_exit`/
   `head_continue` in the pattern of `wloop_to_tail`, plus the unaligned entry
   `0xcf0 → 0xd78` (`andi`; `mv`; `bnez` taken).

2. **Alignment exit** (`0xd74` beqz taken ⇒ `0xcfc`, re-entering the magic setup then
   the word loop with `a4` 8-aligned but `a0 = base ≠ a4`).  This is the one piece
   that needs the word loop **offset-generalized**: the verified `WSt`/`W28`/`WTail`/
   `TDec` and their transitions carry a single scan base `p` used simultaneously for
   `a0`, the string origin, and the aligned addresses.  For the alignment exit these
   must be decoupled — `a0 = base` (length origin), scan base `q = base + off0`
   (aligned), length positions `off0 + 8j + k` — a mechanical parameterization (the
   aligned spec is the `off0 = 0` instance).  Every arithmetic lemma already generalizes
   (`detect_taken/nottaken`, `exit_addi_val`, `snez_final` are stated over the length
   index, not `p`); only the structure fields and the ~20 site-threading proofs need the
   extra `off0`/`base` parameters.  No new mathematical content is required.
-/

end Vsa.Sim
