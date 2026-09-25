import Vsa.Sim.Boot.Owned

/-!
# The physical boundary facts from a boot trace

The fields of `InterpRunPhysicalFacts` that are read facts or arithmetic,
over a byte view of the entry memory. The initial store is checked once over
the view with `interp_run`'s prologue footprint masked out
(`prologueMask`), which gives both `store` and `store_survives`.
-/

namespace Vsa.Sim.Boot

open Vsa.MemRepr Vsa.RuntimeRepr Vsa.While Vsa.Sim.LayoutInstance

/-- `interpRunWriteFootprint` for `inp = &Interp`, as a `Bool`. -/
def prologueMask (k : Nat) : Bool :=
  decide (0x87800000 ≤ k ∧ k < 0x88000000) ||
    decide (interpObject + 16 ≤ k ∧ k < interpObject + 128)

theorem prologueMask_false {k : Nat} (h : prologueMask k = false) :
    ¬ interpRunWriteFootprint (BitVec.ofNat 64 interpObject) k := by
  unfold prologueMask at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  unfold interpRunWriteFootprint
  have hlo : stackSL.lo = 0x87800000 := rfl
  have hhi : stackSL.hi = 0x88000000 := rfl
  have hi : (BitVec.ofNat 64 interpObject).toNat = interpObject := by decide
  rw [hlo, hhi, hi]
  omega

/-- The initial store and its survival through the prologue, from one check
of the global frame at `e` over the masked view. -/
theorem store_of_check {m : Mem} {v : Nat → Option (BitVec 8)} (hv : ViewOf m v)
    {N : NativeAddrs} {A : Arena} {φf φc : Addr → Nat} {e : Nat} (he : φf 0 = e)
    (ha : A.contains e 32 ∧ e % 8 = 0)
    (hf : frameCheck (maskView prologueMask v) N e initFrame = true) :
    StoreRepr m N A φf φc initSt.store ∧
      ∀ m' : Mem, (∀ k, ¬ interpRunWriteFootprint (BitVec.ofNat 64 interpObject) k →
        m[k]? = m'[k]?) → StoreRepr m' N A φf φc initSt.store := by
  have hsurv : ∀ m' : Mem, (∀ k, ¬ interpRunWriteFootprint (BitVec.ofNat 64 interpObject) k →
      m[k]? = m'[k]?) → StoreRepr m' N A φf φc initSt.store := by
    intro m' hag
    have hpv := maskView_partial hv (fun k hk => hag k (prologueMask_false hk))
    rw [← he] at hf ha
    exact storeRepr_initSt (frameCheck_sound hpv φf φc hf) ha
  exact ⟨hsurv m (fun _ _ => rfl), hsurv⟩

/-- The entry's memory read facts. `rodata`, `console` and `stackBytes` are
the fields REVIEW.md P2, P1 and P3 restate; the boot traces discharge the
restated forms (`bootMem_rodata`, `ConsoleBoot`, densification). -/
structure BootMemFacts (m : Mem) (e : Nat) : Prop where
  mainRa : read64 m 0x87fffff8 = some 0x80000038
  text : Code.FixedTextLoaded m
  rodata : Code.FixedRodataLoaded m
  statics : Code.ImageStaticsLoaded m
  console : ConsoleStream m
  exitRuntime : ExitRuntimeData m
  globals : read64 m interpObject = some e
  depth : read32 m (interpObject + 8) = some 0
  stackBytes : ∀ k, stackSL.lo ≤ k → k < stackSL.hi → ∃ b : BitVec 8, m[k]? = some b

/-- The entry's general registers and the statement array they pass. -/
structure BootRegs (g : Nat → BitVec 64) (stmts count : Nat) : Prop where
  ra : g 1 = 0x800045ec#64
  sp : g 2 = BitVec.ofNat 64 spEntry
  gp : g 3 = BitVec.ofNat 64 gpEntry
  s0 : g 8 = 0x8001b970#64
  a0 : g 10 = BitVec.ofNat 64 interpObject
  a1 : g 11 = BitVec.ofNat 64 stmts
  a2 : g 12 = BitVec.ofNat 64 count
  a3 : g 13 = 0#64
  stmts_align : stmts % 8 = 0
  stmts_ram : 0x80000000 ≤ stmts ∧ stmts + 8 * count ≤ 0x100000000
  stmts_win : 0x8001ad00 + 16 ≤ stmts
  stmts_stack : stmts + 8 * count ≤ 0x87800000 ∨ spEntry ≤ stmts

/-- The native entry addresses (`nm`). -/
def bootNatives : NativeAddrs := ⟨0x80002ed4, 0x80002f7c, 0x80002df4⟩

theorem bootArena_protected :
    ∀ a, ProtectedInitialByte a → ¬ (bootArena.lo ≤ a ∧ a < bootArena.hi) := by
  intro a ha hin
  obtain ⟨r, hr, hlo, hhi⟩ := ha
  have hb : ∀ r ∈ exitProtectedRegions, r.1 + r.2 ≤ 0x8001c170 ∨ 0x87800000 ≤ r.1 := by
    decide
  have := hb r hr
  simp only [bootArena, DlHeap.heapStart, DlHeap.heapEnd] at hin
  omega

/-- **The boundary at a boot trace's entry**, from the per-trace facts. -/
theorem readyFacts_of {m : Mem} {v : Nat → Option (BitVec 8)} (hv : ViewOf m v)
    {g : Nat → BitVec 64} {steps stmts count : Nat} {B : BootOwn}
    (M : BootMemFacts m B.env) (R : BootRegs g stmts count)
    (ho : OwnOk B) (hf : FrameOk v B)
    (hstore : frameCheck (maskView prologueMask v) bootNatives B.env initFrame = true)
    {top brkv : Nat} {chunks : List DlHeap.Chunk} {L : List (List Nat)}
    (hh : heapCheck v B.exts [(B.pn, 8 * B.cap), (B.pv, 24 * B.cap)] top brkv chunks L = true)
    {sblk nblk vblk : Nat × Nat} (hH : HeapFactsOk v B top brkv chunks sblk nblk vblk)
    (hgeom : SharedGeom B.shared stackSL)
    (hprog : ∀ p : Program, ProgramRepr m stmts count p →
      ProgramReprWithin m B.shared stmts count p)
    (hcap : ∀ p : Program, ProgramRepr m stmts count p →
      ∀ st' n, ExecSeqCost initSt 0 0 p st' .normal n →
        2 * n + DlHeap.extendSlack ≤ DlHeap.heapEnd - top)
    (hfit : StackAdmissible m stmts count) :
    InterpRunReadyFacts (bootConfig m g steps) stmts count (BitVec.ofNat 64 interpObject)
      bootNatives bootArena (fun _ => B.env) (fun _ => 0) 0 := by
  have hgpr : ∀ i, i < 31 → (bootConfig m g steps).σ.regs.get? (gprReg (i + 1)) =
      some (gprRT (i + 1) (g (i + 1))) := fun i hi => bootRegs_gpr g i hi
  have harena : bootArena.contains B.env 32 ∧ B.env % 8 = 0 := by
    have := ho.rolesArena (B.env, 32) (by simp [BootOwn.roleExts])
    exact ⟨⟨this.2.1, this.2.2⟩, ho.envAligned⟩
  obtain ⟨hst, hsurv⟩ := store_of_check hv (φf := fun _ => B.env) (φc := fun _ => (0 : Nat))
    (A := bootArena) rfl harena hstore
  have hpv : PartialView m v := hv.partial
  refine
    { good := bootState_good m g
      tick := Nat.mod_lt _ (by decide)
      pc := bootState_pc m g
      interp_arg := by rw [← R.a0]; exact hgpr 9 (by decide)
      interp_local := rfl
      stmts_arg := by rw [← R.a1]; exact hgpr 10 (by decide)
      count_arg := by rw [← R.a2]; exact hgpr 11 (by decide)
      repl_arg := by rw [← R.a3]; exact hgpr 12 (by decide)
      ra := by rw [← R.ra]; exact hgpr 0 (by decide)
      sp := by rw [← R.sp]; exact hgpr 1 (by decide)
      gp := by rw [← R.gp]; exact hgpr 2 (by decide)
      main_ra := M.mainRa
      htif_payload := bootState_htif_payload m g
      s0 := ⟨_, hgpr 7 (by decide)⟩
      s1 := ⟨_, hgpr 8 (by decide)⟩
      s2 := ⟨_, hgpr 17 (by decide)⟩
      s3 := ⟨_, hgpr 18 (by decide)⟩
      s4 := ⟨_, hgpr 19 (by decide)⟩
      s5 := ⟨_, hgpr 20 (by decide)⟩
      s6 := ⟨_, hgpr 21 (by decide)⟩
      s7 := ⟨_, hgpr 22 (by decide)⟩
      s8 := ⟨_, hgpr 23 (by decide)⟩
      s9 := ⟨_, hgpr 24 (by decide)⟩
      s10 := ⟨_, hgpr 25 (by decide)⟩
      s11 := ⟨_, hgpr 26 (by decide)⟩
      text_image := M.text
      rodata_image := M.rodata
      statics := M.statics
      console := M.console
      exit_runtime := M.exitRuntime
      arena_protected := bootArena_protected
      out := rfl
      globals := by
        show read64 m (BitVec.ofNat 64 interpObject).toNat = some B.env
        exact M.globals
      call_depth := by
        show read32 m ((BitVec.ofNat 64 interpObject).toNat + 8) = some 0
        exact M.depth
      interp_geom := ⟨by decide, by unfold RSub; decide, by decide, by decide⟩
      setjmp_geom := ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      stack_ok := by unfold Vsa.Alloc.StackOK; decide
      stack_bytes := M.stackBytes
      stmts_align := R.stmts_align
      stmts_ram := R.stmts_ram
      stmts_win := by rw [tohostAddr_val]; exact R.stmts_win
      stmts_stack := R.stmts_stack
      store := hst
      native_addrs := ⟨rfl, rfl, rfl⟩
      store_survives := hsurv
      arena_budget := by decide
      boot := ⟨B.data, top, brkv, chunks, binsOf L, B.frame sblk nblk vblk,
        initialOwned_of hpv ho hf rfl hh hprog hcap,
        ⟨heapAt_of_check hpv hh (fun e _ hr => B.realloc_mem hr), hcap⟩,
        bootHeapFacts_of hpv hf hH hgeom⟩
      stack_admissible := hfit
      gprs := bootState_gprs m g
      s0_impure := by rw [← R.s0]; exact hgpr 7 (by decide) }

end Vsa.Sim.Boot
