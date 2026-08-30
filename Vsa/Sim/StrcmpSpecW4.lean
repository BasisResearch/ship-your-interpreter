import Vsa.Sim.StrcmpSpecW3
import Vsa.Sim.ObsAvoid

/-!
# Layer 3 — `strcmp` word-path spec, part 4 (NUL exits, `strcmp_word_spec`, `strcmp_full_spec`)

Finishes the aligned word path. `StrcmpSpecW2` widened `WordExit`'s NUL arm to the full
register state `WNulExit`; here we discharge the three NUL-word blocks
(`0xfac`/`0xfa4`/`0xfb8`) to `BDone`, assemble the word-path spec `strcmp_word_spec`, and
unify with the byte path in `strcmp_full_spec`.

**NUL-exit control flow** (from `StrcmpSpecW3`'s verified disasm notes). At a NUL exit for
offset `n = 24j + off(pc)`, A's word at `n` holds the NUL (`la < n+8`). The block advances
`a0/a1` to `pa+n`/`pb+n` (`fa4` by 8, `fb8` by 16, `fac` by 0) then `bne a2,a3` re-tests the
cached words:

* **equal** ⇒ both strings' NULs coincide (`la = lb`), so the strings are EQUAL and
  `li a0,0; ret` returns `0` = `strcmpSpecSign` (via `strcmpSpecSign_eq`);
* **differ** ⇒ jump to the byte loop `0xf84` at the advanced pointer `pa+n` over the
  suffixes `csa.drop n` / `csb.drop n`; `byte_loop_to_done` + `byte_f9c_ret` finds the
  tail difference, and `strcmpSpecSign_drop` lifts the suffix sign to the whole strings.
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
open Vsa.MemRepr
open Vsa.Sim.Code (StrcmpLoaded)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## Region-suffix bridge (word region → byte region at the advanced pointer)

The byte-loop re-entry runs `BSt` (a `StrcmpRegion`, byte width-1 reads up to `p+len`) at
base `pa+n` with the suffix string `csa.drop n` (length `la - n`). We derive a
`StrcmpRegion (pa + ofNat n) (la - n)` from the word `StrcmpWRegion pa la`, using `n ≤ la`
(so `pa.toNat + n + (la - n) + 1 = pa.toNat + la + 1 ≤ pa.toNat + la + 8`). -/

/-- A word region gives a byte region at the advanced pointer `p + n` for the suffix of
length `len - n` (`n ≤ len`). -/
theorem strcmpWRegion_drop (p : BitVec 64) (len n : Nat) (hreg : StrcmpWRegion p len)
    (hn : n ≤ len) :
    StrcmpRegion (p + BitVec.ofNat 64 n) (len - n) := by
  have hnowrap := hreg.nowrap
  have htn : (p + BitVec.ofNat 64 n).toNat = p.toNat + n := ptrN p n (by omega)
  have hlo := hreg.lo
  have hhi := hreg.hi
  have hcode := hreg.code
  have hh := hreg.htif
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rw [htn]
  · omega
  · omega
  · omega
  · rcases hcode with h | h
    · left; omega
    · right; omega
  · rcases hh with h | h
    · left; omega
    · right; omega

/-! ## NUL-exit equal case: `la = lb`, spec sign `0`

When the cached words are EQUAL at the NUL offset `n` and A's word holds the NUL
(`n ≤ la < n+8`), the two strings terminate at the same place. From `BytePrefix csa csb n`
plus byte-for-byte word agreement on `[n, n+8)`, we get `BytePrefix csa csb la` and
`byteVal csb la = 0`, hence `lb = la` and `strcmpSpecSign csa csb = 0`. -/

/-- Equal NUL words ⇒ the strings are equal (`strcmpSpecSign = 0`). -/
theorem nul_eq_spec_zero (m0 : Std.ExtHashMap Nat (BitVec 8)) (pa pb : BitVec 64)
    (csa csb : List Char) (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (n : Nat) (hpre : BytePrefix csa csb n) (hnle : n ≤ csa.length)
    (hnf : csa.length < n + 8)
    (heq : cwordAt m0 (pa.toNat + n) = cwordAt m0 (pb.toNat + n)) :
    strcmpSpecSign csa csb = 0 := by
  -- byte agreement on [n, n+8) from equal words
  have hbyteEq : ∀ i, n ≤ i → i < n + 8 → i ≤ csa.length → i ≤ csb.length →
      byteVal csa i = byteVal csb i := by
    intro i hi1 hi2 hia hib
    have hk : i - n < 8 := by omega
    have hA : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*(i-n)) 8).toNat = byteVal csa i := by
      rw [cword_byte_byteVal m0 pa csa hcstra n (i-n) hk (by omega),
        show n + (i - n) = i from by omega]
    have hB : ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*(i-n)) 8).toNat = byteVal csb i := by
      rw [cword_byte_byteVal m0 pb csb hcstrb n (i-n) hk (by omega),
        show n + (i - n) = i from by omega]
    have : ((cwordAt m0 (pa.toNat + n)).extractLsb' (8*(i-n)) 8).toNat
         = ((cwordAt m0 (pb.toNat + n)).extractLsb' (8*(i-n)) 8).toNat := by rw [heq]
    rw [hA, hB] at this; exact this
  -- B's length is ≥ n (from prefix), and ≥ la is what we prove; first n ≤ lb
  have hnlb : n ≤ csb.length := prefix_le_lenb hpre
  -- BytePrefix csa csb la (agree + A-nonzero on [0, la))
  have hprela : BytePrefix csa csb csa.length := by
    intro i hi
    rcases Nat.lt_or_ge i n with hin | hin
    · exact hpre i hin
    · -- i ∈ [n, la): byte i is an A-char (nonzero), agrees with B
      have hilb : i ≤ csb.length := by
        -- byteVal csa i ≠ 0 (i < la), and it agrees with byteVal csb i, so i < lb ⇒ i ≤ lb
        by_cases hib : i ≤ csb.length
        · exact hib
        · exfalso
          -- lb < i ≤ la and lb ∈ [n, n+8): B's NUL byte at lb is 0, A's char there nonzero,
          -- but the equal words force agreement at lb.
          have hlbn : n ≤ csb.length := hnlb
          have hlblt : csb.length < i := by omega
          have hlbla : csb.length < csa.length := by omega
          have hbz : byteVal csb csb.length = 0 := by
            unfold byteVal; rw [show csb[csb.length]? = none from by simp]
          have hane : byteVal csa csb.length ≠ 0 := by
            obtain ⟨ba, hba, hbane⟩ := cstr_byte_ne m0 hcstra csb.length hlbla
            rw [← cstr_byteVal m0 pa.toNat csa hcstra csb.length hlbla ba hba hbane]
            exact fun h => hbane (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
          rw [hbyteEq csb.length hlbn (by omega) (by omega) (Nat.le_refl _), hbz] at hane
          exact hane rfl
      refine ⟨hbyteEq i hin (by omega) (by omega) hilb, ?_⟩
      obtain ⟨ba, hba, hbane⟩ := cstr_byte_ne m0 hcstra i hi
      rw [← cstr_byteVal m0 pa.toNat csa hcstra i hi ba hba hbane]
      exact fun h => hbane (BitVec.eq_of_toNat_eq (by rw [h]; rfl))
  -- byteVal csa la = 0 (past A's end); it agrees with byteVal csb la ⇒ byteVal csb la = 0
  have hAnul : byteVal csa csa.length = 0 := by
    unfold byteVal; rw [show csa[csa.length]? = none from by simp]
  have hlalb : csa.length ≤ csb.length := prefix_le_lenb hprela
  have hBnul : byteVal csb csa.length = 0 := by
    rw [← hbyteEq csa.length hnle (by omega) (Nat.le_refl _) hlalb, hAnul]
  -- lb = la
  have hlb : csb.length = csa.length :=
    (cstr_byteVal_zero m0 pb.toNat csb hcstrb csa.length hlalb hBnul).symm
  exact strcmpSpecSign_eq csa csb csa.length hprela rfl hlb

/-! ## Byte-loop suffix run: `BSt (drop n) 0` → `BDone` for the WHOLE strings

From the byte-loop head at `0xf84`, base `pa+n`/`pb+n`, suffix strings `csa.drop n` /
`csb.drop n`, the byte loop finds the tail difference and returns to `r` with the SUFFIX
spec sign; `strcmpSpecSign_drop` (under `[0,n)` agreement) rewrites it to the whole-string
sign. -/

/-- The byte loop from `BSt g pa' pb' r (csa.drop n) (csb.drop n) 0` reaches `BDone r
csa csb m0` (the WHOLE-string `BDone`), given `[0,n)` agreement. -/
theorem bst_suffix_to_done (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) (halignr : r.toNat % 4 = 0)
    (hagree : ∀ i, i < n → byteVal csa i = byteVal csb i) :
    Triple (BSt g (pa + BitVec.ofNat 64 n) (pb + BitVec.ofNat 64 n) r
              (csa.drop n) (csb.drop n) m0 o 0)
           (BDone g r csa csb m0 o) := by
  intro c hBSt
  -- run the byte loop to BF9c, then the ret
  obtain ⟨c1, hs1, hDone⟩ :=
    ((byte_loop_to_done g (pa + BitVec.ofNat 64 n) (pb + BitVec.ofNat 64 n) r
        (csa.drop n) (csb.drop n) m0 o).seq
      (fun c hc => by
        obtain ⟨ba, bb, hF9c⟩ := hc
        exact byte_f9c_ret g r (csa.drop n) (csb.drop n) ba bb m0 o halignr c hF9c))
      c (Or.inl ⟨0, hBSt⟩)
  -- weaken suffix BDone to whole-string BDone via strcmpSpecSign_drop; the ghost frame is
  -- the SAME g (the byte loop preserves NotWrittenStrcmp, so the suffix run's frame is the
  -- outer pre-call frame — no re-instantiation needed).
  obtain ⟨hG, hpc, hra, hmem, hout, htick, ⟨x, hx, hsign⟩, hframe⟩ := hDone
  refine ⟨c1, hs1, hG, hpc, hra, hmem, hout, htick, ⟨x, hx, ?_⟩, hframe⟩
  rw [hsign, strcmpSpecSign_drop csa csb n hagree]

/-! ## Shared byte-loop head builder at a NUL `bne`-taken target (`0xf84`)

Both NUL `bne a2,a3` sites (`0xfac`, `0xfc0`) branch to `0xf84` with `a0 = pa+n`,
`a1 = pb+n`, the words differing. This produces the byte-loop head `BSt` over the suffix
strings so `bst_suffix_to_done` closes it. -/

/-- Build a suffix `BSt` at `0xf84` from the advanced-pointer state. `pa'` is `pa+n`,
`csa' = csa.drop n`, with the byte region and CStr derived from the word witnesses. -/
theorem mk_suffix_bst (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat)
    (hrega : StrcmpWRegion pa csa.length) (hregb : StrcmpWRegion pb csb.length)
    (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (hnle : n ≤ csa.length) (hnleb : n ≤ csb.length) (c : Config)
    (hgood : GoodState c.σ) (hloaded : StrcmpLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x80006f84#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 n))
    (ha1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 n))
    (hra : c.σ.regs.get? Register.x1 = some r)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (htick : c.tick < 2)
    (hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) :
    BSt g (pa + BitVec.ofNat 64 n) (pb + BitVec.ofNat 64 n) r (csa.drop n) (csb.drop n) m0 o 0 c := by
  have hptra : (pa + BitVec.ofNat 64 n).toNat = pa.toNat + n :=
    ptrN pa n (by have := hrega.nowrap; omega)
  have hptrb : (pb + BitVec.ofNat 64 n).toNat = pb.toNat + n :=
    ptrN pb n (by have := hregb.nowrap; omega)
  refine ⟨hgood, hloaded, hmem, hout, hpc, ?_, ?_, hra, hmi, htick, ?_, ?_, ?_, ?_,
    (fun i hi => absurd hi (by omega)), hframe⟩
  · rw [show pa + BitVec.ofNat 64 n + BitVec.ofNat 64 0 = pa + BitVec.ofNat 64 n from by simp]
    exact ha0
  · rw [show pb + BitVec.ofNat 64 n + BitVec.ofNat 64 0 = pb + BitVec.ofNat 64 n from by simp]
    exact ha1
  · have := strcmpWRegion_drop pa csa.length n hrega hnle
    rwa [List.length_drop]
  · have := strcmpWRegion_drop pb csb.length n hregb hnleb
    rwa [List.length_drop]
  · rw [hptra]; exact cstr_drop m0 hcstra n hnle
  · rw [hptrb]; exact cstr_drop m0 hcstrb n hnleb

/-! ## The NUL `bne a2,a3` sites (`0xfac`, `0xfc0`)

At the bne site the pointers are already advanced to `pa+n`/`pb+n`, `a2/a3` hold the cached
words. Equal ⇒ `li a0,0; ret` (result 0, via `nul_eq_spec_zero`); differ ⇒ byte loop at
`pa+n` (via `mk_suffix_bst` + `bst_suffix_to_done`). Two near-identical instances differing
only in the ret-path site names (`fb0/fb4` vs `fc4/fc8`). -/

/-- The `0xfac` `bne a2,a3` site. -/
theorem nul_bne_fac (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) (halignr : r.toNat % 4 = 0)
    (hrega : StrcmpWRegion pa csa.length) (hregb : StrcmpWRegion pb csb.length)
    (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (hpre : BytePrefix csa csb n) (hnle : n ≤ csa.length) (hnf : csa.length < n + 8)
    (c : Config)
    (hgood : GoodState c.σ) (hloaded : StrcmpLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x80006fac#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 n))
    (ha1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 n))
    (ha2 : c.σ.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + n)))
    (ha3 : c.σ.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + n)))
    (hra : c.σ.regs.get? Register.x1 = some r)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (htick : c.tick < 2)
    (hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) :
    ∃ c', Steps c c' ∧ BDone g r csa csb m0 o c' := by
  obtain ⟨vmi, hmi⟩ := hmi
  have hnleb : n ≤ csb.length := prefix_le_lenb hpre
  by_cases hwe : cwordAt m0 (pa.toNat + n) = cwordAt m0 (pb.toNat + n)
  · -- equal: bne not taken → fb0 (li a0,0) → fb4 (ret) → BDone sign 0
    have hguard : ((cwordAt m0 (pa.toNat + n)) != (cwordAt m0 (pb.toNat + n))) = false := by rw [hwe]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006fac_nottaken c.σ c.tick c.steps (0x80006fac#64) vmi
        (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n))
        hgood hpc hmi ha2 ha3 hloaded rfl hguard htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fb0#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006fac#64) 4 = (0x80006fb0#64 : BitVec 64) from by decide] at this
    have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    -- fb0: li a0,0
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_80006fb0 σ1 i1 (c.steps + 1) (0x80006fb0#64) vmi1 hG1 hpc1 hmi1' (by rw [hmem1]; exact hloaded) rfl hi1
    have hpc2 : σ2.regs.get? Register.PC = some (0x80006fb4#64 : BitVec 64) := by
      have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006fb0#64) 4 = (0x80006fb4#64 : BitVec 64) from by decide] at this
    have ha0_2 : σ2.regs.get? Register.x10 = some ((0#64) + sign_extend (m := 64) (0x000#12)) :=
      obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
    have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs2 R hR.2.2.2.1 hR).trans (hframe_1 R hR)
    obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
    -- fb4: ret
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halignr]; exact halignr
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80006fb4 σ2 i2 (c.steps + 1 + 1) (0x80006fb4#64) vmi2 r
        hG2 hpc2 hmi2' hra_2 (by rw [hmem2, hmem1]; exact hloaded) rfl htgt hi2
    have hpc3 : σ3.regs.get? Register.PC = some r := by rw [obs_jr_pc hobs3, ret_tgt r halignr]
    have ha0_3 := obs_jr_other' hobs3 Register.x10 (by decide) ha0_2
    have hra_3 := obs_jr_other' hobs3 Register.x1 (by decide) hra_2
    have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
      fun R hR => (sframe_jr hobs3 R hR).trans (hframe_2 R hR)
    have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
    have hout3 : σ3.sailOutput = o :=
      (by chain_out [hobs1, hobs2, hobs3] : σ3.sailOutput = c.σ.sailOutput).trans hout
    have hsign0 : strcmpSpecSign csa csb = 0 :=
      nul_eq_spec_zero m0 pa pb csa csb hcstra hcstrb n hpre hnle hnf hwe
    refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
      ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3), ?_⟩
    refine ⟨hG3, hpc3, hra_3, by rw [hmem3eq]; exact hmem, hout3, hi3, ?_, hframe_3⟩
    refine ⟨(0#64) + sign_extend (m := 64) (0x000#12), ha0_3, ?_⟩
    rw [hsign0, show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide]
    simp [strcmpSign]
  · -- differ: bne taken → f84 (byte loop over suffixes)
    have hguard : ((cwordAt m0 (pa.toNat + n)) != (cwordAt m0 (pb.toNat + n))) = true := by rw [bne_iff_ne]; exact hwe
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006fac_taken c.σ c.tick c.steps (0x80006fac#64) vmi
        (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n))
        hgood hpc hmi ha2 ha3 hloaded rfl hguard htick
    have hpceq : (0x80006fac#64 : BitVec 64) + sign_extend (m := 64) (0x1fd8#13) = (0x80006f84#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006f84#64 : BitVec 64) := by rw [obs_btaken_pc hobs1, hpceq]
    have ha0_1 := obs_btaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_btaken_other' hobs1 Register.x11 (by decide) ha1
    have hra_1 := obs_btaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    have hout1 : σ1.sailOutput = o :=
      (by chain_out [hobs1] : σ1.sailOutput = c.σ.sailOutput).trans hout
    have hBSt := mk_suffix_bst g pa pb r csa csb m0 o n hrega hregb hcstra hcstrb hnle hnleb
      ⟨σ1, i1, c.steps + 1⟩ hG1 (by rw [hmem1eq]; exact hloaded) (by rw [hmem1eq]; exact hmem)
      hout1
      hpc1 ha0_1 ha1_1 hra_1 ⟨vmi1, hmi1'⟩ hi1 hframe_1
    obtain ⟨c', hsteps', hDone'⟩ := bst_suffix_to_done g pa pb r csa csb m0 o n halignr
      (fun i hi => (hpre i hi).1) ⟨σ1, i1, c.steps + 1⟩ hBSt
    exact ⟨c', (Steps.single hs1).trans hsteps', hDone'⟩

/-- The `0xfc0` `bne a2,a3` site (group-2 path). Identical to `nul_bne_fac` modulo the
ret-path site names (`fc4`/`fc8`) and branch offset (`0x1fc4`). -/
theorem nul_bne_fc0 (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (n : Nat) (halignr : r.toNat % 4 = 0)
    (hrega : StrcmpWRegion pa csa.length) (hregb : StrcmpWRegion pb csb.length)
    (hcstra : CStr m0 pa.toNat csa) (hcstrb : CStr m0 pb.toNat csb)
    (hpre : BytePrefix csa csb n) (hnle : n ≤ csa.length) (hnf : csa.length < n + 8)
    (c : Config)
    (hgood : GoodState c.σ) (hloaded : StrcmpLoaded c.σ.mem) (hmem : c.σ.mem = m0)
    (hout : c.σ.sailOutput = o)
    (hpc : c.σ.regs.get? Register.PC = some (0x80006fc0#64 : BitVec 64))
    (ha0 : c.σ.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 n))
    (ha1 : c.σ.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 n))
    (ha2 : c.σ.regs.get? Register.x12 = some (cwordAt m0 (pa.toNat + n)))
    (ha3 : c.σ.regs.get? Register.x13 = some (cwordAt m0 (pb.toNat + n)))
    (hra : c.σ.regs.get? Register.x1 = some r)
    (hmi : ∃ v, c.σ.regs.get? Register.minstret = some v) (htick : c.tick < 2)
    (hframe : ∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R) :
    ∃ c', Steps c c' ∧ BDone g r csa csb m0 o c' := by
  obtain ⟨vmi, hmi⟩ := hmi
  have hnleb : n ≤ csb.length := prefix_le_lenb hpre
  by_cases hwe : cwordAt m0 (pa.toNat + n) = cwordAt m0 (pb.toNat + n)
  · have hguard : ((cwordAt m0 (pa.toNat + n)) != (cwordAt m0 (pb.toNat + n))) = false := by rw [hwe]; simp
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006fc0_nottaken c.σ c.tick c.steps (0x80006fc0#64) vmi
        (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n))
        hgood hpc hmi ha2 ha3 hloaded rfl hguard htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fc4#64 : BitVec 64) := by
      have := obs_bnottaken_pc hobs1; rwa [show BitVec.addInt (0x80006fc0#64) 4 = (0x80006fc4#64 : BitVec 64) from by decide] at this
    have hra_1 := obs_bnottaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_bnottaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_bnottaken_minstret hobs1
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_80006fc4 σ1 i1 (c.steps + 1) (0x80006fc4#64) vmi1 hG1 hpc1 hmi1' (by rw [hmem1]; exact hloaded) rfl hi1
    have hpc2 : σ2.regs.get? Register.PC = some (0x80006fc8#64 : BitVec 64) := by
      have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006fc4#64) 4 = (0x80006fc8#64 : BitVec 64) from by decide] at this
    have ha0_2 : σ2.regs.get? Register.x10 = some ((0#64) + sign_extend (m := 64) (0x000#12)) :=
      obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
    have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs2 R hR.2.2.2.1 hR).trans (hframe_1 R hR)
    obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
    have htgt : (BitVec.update (r + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0 := by
      rw [ret_tgt r halignr]; exact halignr
    obtain ⟨σ3, i3, hs3, hi3, hG3, hmem3, hobs3⟩ :=
      site_80006fc8 σ2 i2 (c.steps + 1 + 1) (0x80006fc8#64) vmi2 r
        hG2 hpc2 hmi2' hra_2 (by rw [hmem2, hmem1]; exact hloaded) rfl htgt hi2
    have hpc3 : σ3.regs.get? Register.PC = some r := by rw [obs_jr_pc hobs3, ret_tgt r halignr]
    have ha0_3 := obs_jr_other' hobs3 Register.x10 (by decide) ha0_2
    have hra_3 := obs_jr_other' hobs3 Register.x1 (by decide) hra_2
    have hframe_3 : ∀ R, NotWrittenStrcmp R → σ3.regs.get? R = g R :=
      fun R hR => (sframe_jr hobs3 R hR).trans (hframe_2 R hR)
    have hmem3eq : σ3.mem = c.σ.mem := by rw [hmem3, hmem2, hmem1]
    have hout3 : σ3.sailOutput = o :=
      (by chain_out [hobs1, hobs2, hobs3] : σ3.sailOutput = c.σ.sailOutput).trans hout
    have hsign0 : strcmpSpecSign csa csb = 0 :=
      nul_eq_spec_zero m0 pa pb csa csb hcstra hcstrb n hpre hnle hnf hwe
    refine ⟨⟨σ3, i3, c.steps + 1 + 1 + 1⟩,
      ((Steps.single hs1).trans (Steps.single hs2)).trans (Steps.single hs3), ?_⟩
    refine ⟨hG3, hpc3, hra_3, by rw [hmem3eq]; exact hmem, hout3, hi3, ?_, hframe_3⟩
    refine ⟨(0#64) + sign_extend (m := 64) (0x000#12), ha0_3, ?_⟩
    rw [hsign0, show ((0#64) + sign_extend (m := 64) (0x000#12) : BitVec 64) = 0#64 from by
      apply BitVec.eq_of_toNat_eq; decide]
    simp [strcmpSign]
  · have hguard : ((cwordAt m0 (pa.toNat + n)) != (cwordAt m0 (pb.toNat + n))) = true := by rw [bne_iff_ne]; exact hwe
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006fc0_taken c.σ c.tick c.steps (0x80006fc0#64) vmi
        (cwordAt m0 (pa.toNat + n)) (cwordAt m0 (pb.toNat + n))
        hgood hpc hmi ha2 ha3 hloaded rfl hguard htick
    have hpceq : (0x80006fc0#64 : BitVec 64) + sign_extend (m := 64) (0x1fc4#13) = (0x80006f84#64 : BitVec 64) := by
      apply BitVec.eq_of_toNat_eq; decide
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006f84#64 : BitVec 64) := by rw [obs_btaken_pc hobs1, hpceq]
    have ha0_1 := obs_btaken_other' hobs1 Register.x10 (by decide) ha0
    have ha1_1 := obs_btaken_other' hobs1 Register.x11 (by decide) ha1
    have hra_1 := obs_btaken_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_btaken hobs1 R hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_btaken_minstret hobs1
    have hmem1eq : σ1.mem = c.σ.mem := hmem1
    have hout1 : σ1.sailOutput = o :=
      (by chain_out [hobs1] : σ1.sailOutput = c.σ.sailOutput).trans hout
    have hBSt := mk_suffix_bst g pa pb r csa csb m0 o n hrega hregb hcstra hcstrb hnle hnleb
      ⟨σ1, i1, c.steps + 1⟩ hG1 (by rw [hmem1eq]; exact hloaded) (by rw [hmem1eq]; exact hmem)
      hout1
      hpc1 ha0_1 ha1_1 hra_1 ⟨vmi1, hmi1'⟩ hi1 hframe_1
    obtain ⟨c', hsteps', hDone'⟩ := bst_suffix_to_done g pa pb r csa csb m0 o n halignr
      (fun i hi => (hpre i hi).1) ⟨σ1, i1, c.steps + 1⟩ hBSt
    exact ⟨c', (Steps.single hs1).trans hsteps', hDone'⟩

/-! ## The NUL-word exit `WNulExit → BDone`

Case on the three NUL-block PCs: `fac` reaches its `bne` directly (`nulOff 0`); `fa4`
does `addi a0,8; addi a1,8` (via `word_off8`) then falls into `fac`; `fb8` does
`addi a0,16; addi a1,16` (via `word_off16`) then `bne` at `fc0`. Each closes with
`nul_bne_fac`/`nul_bne_fc0`. -/

/-- **The NUL-word exit.** From `WNulExit` to `BDone`. -/
theorem wnul_to_done (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char)
    (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (j : Nat) (pc : BitVec 64) (halignr : r.toNat % 4 = 0) :
    Triple (WNulExit g pa pb r csa csb m0 o j pc) (BDone g r csa csb m0 o) := by
  intro c hSt
  obtain ⟨hpcv, hgood, hloaded, hmem, hout, hpcget, ha0, ha1, ha2, ha3, hra, ⟨vmi, hmi⟩, htick,
    hrega, hregb, hcstra, hcstrb, hmaskpin, hpre, hhasnul, hjle, hframe⟩ := hSt
  rcases hpcv with hpc | hpc | hpc
  · -- fac: nulOff = 0, n = 24j, pointers already at pa+n
    subst hpc
    have hoff : nulOff (0x80006fac#64 : BitVec 64) = 0 := by decide
    rw [hoff, Nat.add_zero] at ha2 ha3 hpre hhasnul hjle
    exact nul_bne_fac g pa pb r csa csb m0 o (24*j) halignr hrega hregb hcstra hcstrb hpre hjle hhasnul
      c hgood hloaded hmem hout hpcget ha0 ha1 ha2 ha3 hra ⟨vmi, hmi⟩ htick hframe
  · -- fa4: nulOff = 8, n = 24j+8. addi a0,8; addi a1,8 → fac
    subst hpc
    have hoff : nulOff (0x80006fa4#64 : BitVec 64) = 8 := by decide
    rw [hoff] at ha2 ha3 hpre hhasnul hjle
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006fa4 c.σ c.tick c.steps (0x80006fa4#64) vmi (pa + BitVec.ofNat 64 (24*j))
        hgood hpcget hmi ha0 hloaded rfl htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fa8#64 : BitVec 64) := by
      have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006fa4#64) 4 = (0x80006fa8#64 : BitVec 64) from by decide] at this
    have ha0_1 : σ1.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j + 8)) := by
      have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [word_off8] at this
    have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
    have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs1 R hR.2.2.2.1 hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_80006fa8 σ1 i1 (c.steps + 1) (0x80006fa8#64) vmi1 (pb + BitVec.ofNat 64 (24*j))
        hG1 hpc1 hmi1' ha1_1 (by rw [hmem1]; exact hloaded) rfl hi1
    have hpc2 : σ2.regs.get? Register.PC = some (0x80006fac#64 : BitVec 64) := by
      have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006fa8#64) 4 = (0x80006fac#64 : BitVec 64) from by decide] at this
    have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
    have ha1_2 : σ2.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j + 8)) := by
      have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [word_off8] at this
    have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
    have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
    have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
    have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.1 hR).trans (hframe_1 R hR)
    obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
    have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
    have hout2 : σ2.sailOutput = o :=
      (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
    obtain ⟨c', hsteps', hDone'⟩ := nul_bne_fac g pa pb r csa csb m0 o (24*j + 8) halignr
      hrega hregb hcstra hcstrb hpre hjle hhasnul
      ⟨σ2, i2, c.steps + 1 + 1⟩ hG2 (by rw [hmem2eq]; exact hloaded) (by rw [hmem2eq]; exact hmem)
      hout2
      hpc2 ha0_2 ha1_2 ha2_2 ha3_2 hra_2 ⟨vmi2, hmi2'⟩ hi2 hframe_2
    exact ⟨c', ((Steps.single hs1).trans (Steps.single hs2)).trans hsteps', hDone'⟩
  · -- fb8: nulOff = 16, n = 24j+16. addi a0,16; addi a1,16 → fc0
    subst hpc
    have hoff : nulOff (0x80006fb8#64 : BitVec 64) = 16 := by decide
    rw [hoff] at ha2 ha3 hpre hhasnul hjle
    obtain ⟨σ1, i1, hs1, hi1, hG1, hmem1, hobs1⟩ :=
      site_80006fb8 c.σ c.tick c.steps (0x80006fb8#64) vmi (pa + BitVec.ofNat 64 (24*j))
        hgood hpcget hmi ha0 hloaded rfl htick
    have hpc1 : σ1.regs.get? Register.PC = some (0x80006fbc#64 : BitVec 64) := by
      have := obs_alu_pc hobs1; rwa [show BitVec.addInt (0x80006fb8#64) 4 = (0x80006fbc#64 : BitVec 64) from by decide] at this
    have ha0_1 : σ1.regs.get? Register.x10 = some (pa + BitVec.ofNat 64 (24*j + 16)) := by
      have := obs_alu_rd hobs1 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [word_off16] at this
    have ha1_1 := obs_alu_other' hobs1 Register.x11 (by decide) ha1
    have ha2_1 := obs_alu_other' hobs1 Register.x12 (by decide) ha2
    have ha3_1 := obs_alu_other' hobs1 Register.x13 (by decide) ha3
    have hra_1 := obs_alu_other' hobs1 Register.x1 (by decide) hra
    have hframe_1 : ∀ R, NotWrittenStrcmp R → σ1.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs1 R hR.2.2.2.1 hR).trans (hframe R hR)
    obtain ⟨vmi1, hmi1'⟩ := obs_alu_minstret hobs1
    obtain ⟨σ2, i2, hs2, hi2, hG2, hmem2, hobs2⟩ :=
      site_80006fbc σ1 i1 (c.steps + 1) (0x80006fbc#64) vmi1 (pb + BitVec.ofNat 64 (24*j))
        hG1 hpc1 hmi1' ha1_1 (by rw [hmem1]; exact hloaded) rfl hi1
    have hpc2 : σ2.regs.get? Register.PC = some (0x80006fc0#64 : BitVec 64) := by
      have := obs_alu_pc hobs2; rwa [show BitVec.addInt (0x80006fbc#64) 4 = (0x80006fc0#64 : BitVec 64) from by decide] at this
    have ha0_2 := obs_alu_other' hobs2 Register.x10 (by decide) ha0_1
    have ha1_2 : σ2.regs.get? Register.x11 = some (pb + BitVec.ofNat 64 (24*j + 16)) := by
      have := obs_alu_rd hobs2 (by decide) (by decide) (by decide) (by decide) (by decide)
      rwa [word_off16] at this
    have ha2_2 := obs_alu_other' hobs2 Register.x12 (by decide) ha2_1
    have ha3_2 := obs_alu_other' hobs2 Register.x13 (by decide) ha3_1
    have hra_2 := obs_alu_other' hobs2 Register.x1 (by decide) hra_1
    have hframe_2 : ∀ R, NotWrittenStrcmp R → σ2.regs.get? R = g R :=
      fun R hR => (sframe_alu hobs2 R hR.2.2.2.2.1 hR).trans (hframe_1 R hR)
    obtain ⟨vmi2, hmi2'⟩ := obs_alu_minstret hobs2
    have hmem2eq : σ2.mem = c.σ.mem := by rw [hmem2, hmem1]
    have hout2 : σ2.sailOutput = o :=
      (by chain_out [hobs1, hobs2] : σ2.sailOutput = c.σ.sailOutput).trans hout
    obtain ⟨c', hsteps', hDone'⟩ := nul_bne_fc0 g pa pb r csa csb m0 o (24*j + 16) halignr
      hrega hregb hcstra hcstrb hpre hjle hhasnul
      ⟨σ2, i2, c.steps + 1 + 1⟩ hG2 (by rw [hmem2eq]; exact hloaded) (by rw [hmem2eq]; exact hmem)
      hout2
      hpc2 ha0_2 ha1_2 ha2_2 ha3_2 hra_2 ⟨vmi2, hmi2'⟩ hi2 hframe_2
    exact ⟨c', ((Steps.single hs1).trans (Steps.single hs2)).trans hsteps', hDone'⟩

/-! ## The aligned word-path `strcmp` spec (`PreWCmp → BDone`)

Composes `strcmp_word_reaches_exit` (entry `0xea0` → `WordExit`) with the exit dispatch:
the lane arm goes to `BDone` via `wlane_to_done`, the NUL arm via `wnul_to_done`. -/

/-- **Aligned word path, end to end.** From `PreWCmp` (`0xea0`, aligned) to `BDone`. -/
theorem strcmp_word_spec (g : (R : Register) → Option (RegisterType R))
    (pa pb r : BitVec 64) (csa csb : List Char) (m0 : Std.ExtHashMap Nat (BitVec 8))
    (o : Array String) (halignr : r.toNat % 4 = 0) :
    Triple (PreWCmp g pa pb r csa csb m0 o) (BDone g r csa csb m0 o) := by
  refine (strcmp_word_reaches_exit g pa pb r csa csb m0 o).seq ?_
  -- WordExit → BDone: lane arm | NUL arm
  intro c hEx
  rcases hEx with ⟨n, hlane⟩ | ⟨j, pc, hnul⟩
  · exact wlane_to_done g pa pb r csa csb m0 o n halignr c hlane
  · exact wnul_to_done g pa pb r csa csb m0 o j pc halignr c hnul

/-! ## Top-level `strcmp` full spec (byte path ∪ word path)

`strcmp_full_pre` widens `strcmp_pre`'s misalignment disjunct to `True` (either alignment
is admissible), keeping all shared side conditions and adding the word-path witnesses
(`StrcmpWRegion`, `MaskPinned`). `strcmp_full_post` is `strcmp_post` verbatim. The proof
`Triple.cases` on the entry alignment test `(pa|pb) & 7 = 0`: aligned → `strcmp_word_spec`,
misaligned → `strcmp_byte_path`. -/

/-- Top-level precondition (either path). Like `strcmp_pre` but WITHOUT the misalignment
guard, and carrying BOTH the byte-region and word-region/mask witnesses so either entry
path is discharged. -/
def strcmp_full_pre (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) (c : Config) : Prop :=
  GoodState c.σ ∧ StrcmpLoaded c.σ.mem ∧ c.σ.mem = m0 ∧ c.σ.sailOutput = o ∧
  c.σ.regs.get? Register.PC = some (0x80006ea0#64 : BitVec 64) ∧
  c.σ.regs.get? Register.x10 = some pa ∧ c.σ.regs.get? Register.x11 = some pb ∧
  c.σ.regs.get? Register.x1 = some r ∧
  (∃ v, c.σ.regs.get? Register.minstret = some v) ∧ c.tick < 2 ∧
  r.toNat % 4 = 0 ∧ CString m0 pa.toNat sa ∧ CString m0 pb.toNat sb ∧
  MaskPinned m0 ∧
  (∀ cs, CStr m0 pa.toNat cs → StrcmpRegion pa cs.length) ∧
  (∀ cs, CStr m0 pb.toNat cs → StrcmpRegion pb cs.length) ∧
  (∀ cs, CStr m0 pa.toNat cs → StrcmpWRegion pa cs.length) ∧
  (∀ cs, CStr m0 pb.toNat cs → StrcmpWRegion pb cs.length) ∧
  (∀ R : Register, NotWrittenStrcmp R → c.σ.regs.get? R = g R)

/-- **`strcmp` total-correctness spec (both paths).** From `strcmp_full_pre` (no
alignment guard) the machine runs to `strcmp_post`; the entry alignment test selects the
byte path or the word path, both landing the same result sign. -/
theorem strcmp_full_spec (g : (R : Register) → Option (RegisterType R)) (pa pb r : BitVec 64)
    (sa sb : String) (m0 : Std.ExtHashMap Nat (BitVec 8)) (o : Array String) :
    Triple (strcmp_full_pre g pa pb r sa sb m0 o) (strcmp_post g r pa pb sa sb m0 o) := by
  intro c hpre
  obtain ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, hmi, htick, halignr,
    ⟨csa, hcstra, hsa⟩, ⟨csb, hcstrb, hsb⟩, hmaskpin, hbrega, hbregb, hwrega, hwregb, hframe⟩ := hpre
  by_cases hal : ((pa ||| pb) &&& sign_extend (m := 64) (0x007#12)) = 0#64
  · -- aligned → word path
    have hPreW : PreWCmp g pa pb r csa csb m0 o c :=
      ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, hmi, htick,
        hwrega csa hcstra, hwregb csb hcstrb, hcstra, hcstrb, hmaskpin, hal, hframe⟩
    obtain ⟨c', hsteps, hDone⟩ := strcmp_word_spec g pa pb r csa csb m0 o halignr c hPreW
    obtain ⟨hG', hpc', hra', hmem', hout', htick', ⟨x, hx, hsign⟩, hframe'⟩ := hDone
    exact ⟨c', hsteps, hG', hpc', hra', hmem', hout', htick', hframe', csa, csb, x, hcstra, hcstrb, hsa, hsb, hx, hsign⟩
  · -- misaligned → byte path
    have hPreB : PreBCmp g pa pb r csa csb m0 o c :=
      ⟨hgood, hloaded, hmem, hout, hpc, ha0, ha1, hra, hmi, htick,
        hbrega csa hcstra, hbregb csb hcstrb, hcstra, hcstrb, hal, hframe⟩
    obtain ⟨c', hsteps, hDone⟩ := strcmp_byte_path g pa pb r csa csb m0 o halignr c hPreB
    obtain ⟨hG', hpc', hra', hmem', hout', htick', ⟨x, hx, hsign⟩, hframe'⟩ := hDone
    exact ⟨c', hsteps, hG', hpc', hra', hmem', hout', htick', hframe', csa, csb, x, hcstra, hcstrb, hsa, hsb, hx, hsign⟩

end Vsa.Sim
