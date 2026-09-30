import VsaIris.Vsa.StrlenOwned
import VsaIris.Vsa.StrcmpSeg
import Vsa.While.StringOrder

namespace VsaIris.Inst.Strcmp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail
open Vsa.Machine (Config)
open Vsa.Sim Vsa.MemRepr
open VsaIris.Inst.Strlen (codeText memFoot mem_memFoot memFoot_mem)

abbrev cmpBase : Nat := 0x80006ea0

def strcmpCodeA : List (BitVec 8) :=
  [0x33#8, 0x67#8, 0xb5#8, 0x00#8, 0x93#8, 0x03#8, 0xf0#8, 0xff#8, 0x13#8, 0x77#8, 0x77#8, 0x00#8,
   0x63#8, 0x1c#8, 0x07#8, 0x0c#8, 0x97#8, 0x47#8, 0x01#8, 0x00#8, 0x83#8, 0xb7#8, 0x07#8, 0xdd#8,
   0x03#8, 0x36#8, 0x05#8, 0x00#8, 0x83#8, 0xb6#8, 0x05#8, 0x00#8, 0xb3#8, 0x72#8, 0xf6#8, 0x00#8,
   0x33#8, 0x63#8, 0xf6#8, 0x00#8, 0xb3#8, 0x82#8, 0xf2#8, 0x00#8, 0xb3#8, 0xe2#8, 0x62#8, 0x00#8,
   0x63#8, 0x9e#8, 0x72#8, 0x0c#8, 0x63#8, 0x16#8, 0xd6#8, 0x04#8, 0x03#8, 0x36#8, 0x85#8, 0x00#8]

def strcmpCodeB : List (BitVec 8) :=
  [0x83#8, 0xb6#8, 0x85#8, 0x00#8, 0xb3#8, 0x72#8, 0xf6#8, 0x00#8, 0x33#8, 0x63#8, 0xf6#8, 0x00#8,
   0xb3#8, 0x82#8, 0xf2#8, 0x00#8, 0xb3#8, 0xe2#8, 0x62#8, 0x00#8, 0x63#8, 0x9a#8, 0x72#8, 0x0a#8,
   0x63#8, 0x16#8, 0xd6#8, 0x02#8, 0x03#8, 0x36#8, 0x05#8, 0x01#8, 0x83#8, 0xb6#8, 0x05#8, 0x01#8,
   0xb3#8, 0x72#8, 0xf6#8, 0x00#8, 0x33#8, 0x63#8, 0xf6#8, 0x00#8, 0xb3#8, 0x82#8, 0xf2#8, 0x00#8,
   0xb3#8, 0xe2#8, 0x62#8, 0x00#8, 0x63#8, 0x94#8, 0x72#8, 0x0a#8, 0x13#8, 0x05#8, 0x85#8, 0x01#8]

def strcmpCodeC : List (BitVec 8) :=
  [0x93#8, 0x85#8, 0x85#8, 0x01#8, 0xe3#8, 0x0e#8, 0xd6#8, 0xf8#8, 0x13#8, 0x17#8, 0x06#8, 0x03#8,
   0x93#8, 0x97#8, 0x06#8, 0x03#8, 0x63#8, 0x1a#8, 0xf7#8, 0x02#8, 0x13#8, 0x17#8, 0x06#8, 0x02#8,
   0x93#8, 0x97#8, 0x06#8, 0x02#8, 0x63#8, 0x14#8, 0xf7#8, 0x02#8, 0x13#8, 0x17#8, 0x06#8, 0x01#8,
   0x93#8, 0x97#8, 0x06#8, 0x01#8, 0x63#8, 0x1e#8, 0xf7#8, 0x00#8, 0x13#8, 0x57#8, 0x06#8, 0x03#8,
   0x93#8, 0xd7#8, 0x06#8, 0x03#8, 0x33#8, 0x05#8, 0xf7#8, 0x40#8, 0x93#8, 0x75#8, 0xf5#8, 0x0f#8]

def strcmpCodeD : List (BitVec 8) :=
  [0x63#8, 0x90#8, 0x05#8, 0x02#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x57#8, 0x07#8, 0x03#8,
   0x93#8, 0xd7#8, 0x07#8, 0x03#8, 0x33#8, 0x05#8, 0xf7#8, 0x40#8, 0x93#8, 0x75#8, 0xf5#8, 0x0f#8,
   0x63#8, 0x94#8, 0x05#8, 0x00#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x77#8, 0xf7#8, 0x0f#8,
   0x93#8, 0xf7#8, 0xf7#8, 0x0f#8, 0x33#8, 0x05#8, 0xf7#8, 0x40#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8,
   0x03#8, 0x46#8, 0x05#8, 0x00#8, 0x83#8, 0xc6#8, 0x05#8, 0x00#8, 0x13#8, 0x05#8, 0x15#8, 0x00#8]

def strcmpCodeE : List (BitVec 8) :=
  [0x93#8, 0x85#8, 0x15#8, 0x00#8, 0x63#8, 0x14#8, 0xd6#8, 0x00#8, 0xe3#8, 0x16#8, 0x06#8, 0xfe#8,
   0x33#8, 0x05#8, 0xd6#8, 0x40#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x05#8, 0x85#8, 0x00#8,
   0x93#8, 0x85#8, 0x85#8, 0x00#8, 0xe3#8, 0x1c#8, 0xd6#8, 0xfc#8, 0x13#8, 0x05#8, 0x00#8, 0x00#8,
   0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x13#8, 0x05#8, 0x05#8, 0x01#8, 0x93#8, 0x85#8, 0x05#8, 0x01#8,
   0xe3#8, 0x12#8, 0xd6#8, 0xfc#8, 0x13#8, 0x05#8, 0x00#8, 0x00#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8]

def strcmpCode : List (BitVec 8) :=
  strcmpCodeA ++ strcmpCodeB ++ strcmpCodeC ++ strcmpCodeD ++ strcmpCodeE

theorem strcmpLoaded_of_code {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ q ∈ codeText cmpBase strcmpCode, m[q.1]? = some q.2) :
    Code.StrcmpLoaded m := by
  unfold Code.StrcmpLoaded Code.strcmpChunk0 Code.strcmpChunk1 Code.strcmpChunk2
    Code.strcmpChunk3 Code.strcmpChunk4
  repeat' apply And.intro
  all_goals (apply h (_, _); decide)

def cmpRegs : List Nat := [1, 5, 6, 7, 10, 11, 12, 13, 14, 15]

def cmpRs : List Nat := VsaIris.PC :: cmpRegs

def cmpL (rv : Nat → BitVec 64) : GRegs :=
  [(1, rv 1), (5, rv 5), (6, rv 6), (7, rv 7), (10, rv 10), (11, rv 11), (12, rv 12),
   (13, rv 13), (14, rv 14), (15, rv 15)]

theorem cmpL_eq (rv : Nat → BitVec 64) : cmpL rv = leafL cmpRegs rv := rfl

def cmpQ (r : BitVec 64) (cx cy : List Char) (rv : Nat → BitVec 64) (_ : Nat → BitVec 8) :
    Prop :=
  rv VsaIris.PC = r ∧ rv 1 = r ∧ strcmpSign (rv 10) = strcmpSpecSign cx cy

def CRun (live : Nat → Prop) (T : List (Nat × BitVec 8)) (r : BitVec 64) (cx cy : List Char)
    (n : Nat) (rv : Nat → BitVec 64) : Prop :=
  ∀ mv, LocalRun (vsaModel live) [] T cmpRs (fun _ => False) (cmpQ r cx cy) n rv mv

theorem CRun.mono {live T r cx cy} {n n' : Nat} {rv : Nat → BitVec 64} (hn : n ≤ n')
    (h : CRun live T r cx cy n rv) : CRun live T r cx cy n' rv :=
  fun mv => localRun_le hn (h mv)

theorem CRun.done {live T r cx cy} {n : Nat} {rv : Nat → BitVec 64}
    (h : cmpQ r cx cy rv (fun _ => 0)) : CRun live T r cx cy n rv := by
  intro mv
  cases n with
  | zero => exact h
  | succ n => exact .inl h

theorem cmpStep {live : Nat → Prop} {T : List (Nat × BitVec 8)} {r : BitVec 64}
    {cx cy : List Char} {rv : Nat → BitVec 64} (m : Nat)
    (hcodeL : ∀ q ∈ codeText cmpBase strcmpCode, live q.1)
    (hcodeT : ∀ q ∈ codeText cmpBase strcmpCode, q ∈ T)
    (bs : List BBlock) (peek : List Nat) (lds : (Nat → BitVec 8) → List (List (BitVec 8)))
    (pc0 : BitVec 64) (n : Nat)
    (hlen : evalBlocksFuel bs = n + 1) (hwf : ChainOK pc0 cmpRegs bs)
    (hwr : ∀ k ∈ wrChain bs, k ∈ cmpRegs)
    (hsilent : ∀ vals, (segOut bs (cmpL rv) (lds vals)).log = [])
    (hpc : rv VsaIris.PC = pc0)
    (hfacts : ∀ (vals : Nat → BitVec 8), (∀ t ∈ T, vals t.1 = t.2) →
      ∀ m : Std.ExtHashMap Nat (BitVec 8), Code.StrcmpLoaded m → (∀ a ∈ peek, (m[a]?).getD 0 = vals a) →
      ChainFacts m m (cmpL rv) (lds vals) bs)
    (hnext : ∀ (vals : Nat → BitVec 8), (∀ t ∈ T, vals t.1 = t.2) →
      ∀ rv' : Nat → BitVec 64,
      rv' VsaIris.PC = evalBlocksPC pc0 (SegEvalState.init (cmpL rv) (lds vals)) bs →
      (∀ k ∈ cmpRegs, rv' k = finReg bs (cmpL rv) (lds vals) k) →
      CRun live T r cx cy m rv') :
    CRun live T r cx cy (m + 1) rv := by
  intro mv
  refine .inr ⟨n, fun σ hok hro hr hm => ?_⟩
  let vals : Nat → BitVec 8 := fun a => (vsaModel live).mem σ a
  let PT : List (Nat × BitVec 8) := peek.map fun a => (a, vals a)
  have hseg : SegFrom (vsaModel live) [] (T ++ PT) cmpRs (fun _ => False) n rv mv
      (LocalRun (vsaModel live) [] T cmpRs (fun _ => False) (cmpQ r cx cy) m) := by
    refine segFrom_of_segW bs (cmpL rv) (lds vals) pc0
      (memFoot (codeText cmpBase strcmpCode ++ PT)) [] n hlen
      (by rw [cmpL_eq, keysG_leafL]; exact hwf) (by rw [cmpL_eq, keysG_leafL]; decide)
      (by rw [cmpL_eq, keysG_leafL]; exact hwr) (fun a _ => by rw [hsilent]; trivial)
      (fun c hok' hfoot => ?_) (fun q hq => ?_) (fun q hq => nomatch hq) List.mem_cons_self hpc
      (fun q hq => ?_) (fun rv' mv' h1 h2 _ _ _ => ?_)
    · have hmr := hfoot.2.1
      have hpres := code_present hok' (memFoot (codeText cmpBase strcmpCode))
        (fun q hq => hmr q (by unfold memFoot at hq ⊢; rw [List.map_append]; exact List.mem_append_left _ hq))
        (fun q hq => hcodeL _ (mem_memFoot hq))
      refine hfacts vals (fun t ht => hro.2 t ht) c.σ.mem (strcmpLoaded_of_code fun q hq => hpres _ (memFoot_mem hq))
        fun a ha => ?_
      have := hmr (a, DFrac.discard, vals a) (by
        unfold memFoot; rw [List.map_append]
        exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_map_of_mem ha)))
      exact this
    · exact .inl (by
        rcases List.mem_append.mp (mem_memFoot (t := codeText cmpBase strcmpCode ++ PT) hq) with h | h
        · exact List.mem_append_left _ (hcodeT _ h)
        · exact List.mem_append_right _ h)
    · rw [cmpL_eq] at hq
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
      exact ⟨.tail _ hk, rfl⟩
    · refine hnext vals (fun t ht => hro.2 t ht) rv' h1 (fun k hk => h2 (k, rv k) ?_) mv'
      exact List.mem_map_of_mem (f := fun k => (k, rv k)) hk
  exact hseg σ hok ⟨hro.1, fun p hp => by
    rcases List.mem_append.mp hp with h | h
    · exact hro.2 p h
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp h; rfl⟩ hr hm

structure SBytes (img : Nat → BitVec 8) (p : Nat) (cs : List Char) : Prop where
  byte : ∀ k, k ≤ cs.length → (img (p + k)).toNat = byteVal cs k
  ascii : ∀ k, k < cs.length → 0 < byteVal cs k ∧ byteVal cs k < 128

structure SWin (p len : Nat) : Prop where
  lo : 0x80000000 ≤ p
  hi : p + len + 8 ≤ 0x100000000
  htif : p + len + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ p

def maskText : List (Nat × BitVec 8) := (List.range 8).map fun k => (0x8001ac80 + k, 0x7f#8)

def strT (p len : Nat) (img : Nat → BitVec 8) : List (Nat × BitVec 8) :=
  (List.range (len + 1)).map fun k => (p + k, img (p + k))

def cmpText (p lx : Nat) (ix : Nat → BitVec 8) (q ly : Nat) (iy : Nat → BitVec 8) :
    List (Nat × BitVec 8) :=
  codeText cmpBase strcmpCode ++ maskText ++ strT p lx ix ++ strT q ly iy

structure Ctx (live : Nat → Prop) (p q r : BitVec 64) (cx cy : List Char)
    (ix iy : Nat → BitVec 8) : Prop where
  codeL : ∀ t ∈ codeText cmpBase strcmpCode, live t.1
  bx : SBytes ix p.toNat cx
  by_ : SBytes iy q.toNat cy
  wx : SWin p.toNat cx.length
  wy : SWin q.toNat cy.length
  ret : r.toNat % 4 = 0

section Run

variable {live : Nat → Prop} {p q r : BitVec 64} {cx cy : List Char} {ix iy : Nat → BitVec 8}

abbrev TT (p q : BitVec 64) (cx cy : List Char) (ix iy : Nat → BitVec 8) :=
  cmpText p.toNat cx.length ix q.toNat cy.length iy

theorem codeT : ∀ t ∈ codeText cmpBase strcmpCode, t ∈ TT p q cx cy ix iy := by
  intro t ht; unfold TT cmpText
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ht))

theorem valsX {vals : Nat → BitVec 8} (hv : ∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2)
    (k : Nat) (hk : k ≤ cx.length) : vals (p.toNat + k) = ix (p.toNat + k) :=
  hv (p.toNat + k, ix (p.toNat + k)) (by
    unfold TT cmpText
    refine List.mem_append_left _ (List.mem_append_right _ ?_)
    exact List.mem_map_of_mem (f := fun k => (p.toNat + k, ix (p.toNat + k)))
      (List.mem_range.mpr (by omega)))

theorem valsY {vals : Nat → BitVec 8} (hv : ∀ t ∈ TT p q cx cy ix iy, vals t.1 = t.2)
    (k : Nat) (hk : k ≤ cy.length) : vals (q.toNat + k) = iy (q.toNat + k) :=
  hv (q.toNat + k, iy (q.toNat + k)) (by
    unfold TT cmpText
    refine List.mem_append_right _ ?_
    exact List.mem_map_of_mem (f := fun k => (q.toNat + k, iy (q.toNat + k)))
      (List.mem_range.mpr (by omega)))

structure ByteSt (p q r : BitVec 64) (cx cy : List Char) (k : Nat) (rv : Nat → BitVec 64) :
    Prop where
  pc : rv VsaIris.PC = 0x80006f84#64
  ra : rv 1 = r
  a0 : rv 10 = p + BitVec.ofNat 64 k
  a1 : rv 11 = q + BitVec.ofNat 64 k
  pre : BytePrefix cx cy k

def bytesAt (f : Nat → BitVec 8) (a n : Nat) : List (BitVec 8) :=
  (List.range n).map fun j => f (a + j)

theorem bytesAt_getD (f : Nat → BitVec 8) (a : Nat) {n j : Nat} (h : j < n) :
    (bytesAt f a n).getD j 0#8 = f (a + j) := by
  simp [bytesAt, h]

theorem lbuF {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {line : MInstr}
    {bs : List (BitVec 8)} (hkind : line.kind = .lbu) {ea : Nat}
    (haddr : (eaddrM line L).toNat = ea) (hlo : 0x80000000 ≤ ea) (hhi : ea + 1 ≤ 0x100000000)
    (hh : ea + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea)
    (hb : (m[ea]?).getD 0 = bs.getD 0 0#8) : MemFacts m L bs line := by
  unfold MemFacts
  rw [hkind]
  change (0x80000000 ≤ _ ∧ _ + 1 ≤ 0x100000000 ∧ (_ + 1 ≤ tohostAddr ∨ tohostAddr + 8 ≤ _)) ∧ _
  rw [haddr]
  exact ⟨⟨hlo, hhi, hh⟩, hb⟩

theorem ldF {m : Std.ExtHashMap Nat (BitVec 8)} {L : GRegs} {line : MInstr}
    (hkind : line.kind = .ld) {ea : Nat} (f : Nat → BitVec 8)
    (haddr : (eaddrM line L).toNat = ea) (hlo : 0x80000000 ≤ ea) (hhi : ea + 8 ≤ 0x100000000)
    (hh : ea + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ ea)
    (hb : ∀ j, j < 8 → (m[ea + j]?).getD 0 = f (ea + j)) :
    MemFacts m L (bytesAt f ea 8) line := by
  unfold MemFacts
  rw [hkind]
  change (0x80000000 ≤ _ ∧ _ + 8 ≤ 0x100000000 ∧ (_ + 8 ≤ tohostAddr ∨ tohostAddr + 8 ≤ _)) ∧ _
  rw [haddr]
  refine ⟨⟨hlo, hhi, hh⟩, ?_⟩
  have g := fun j (hj : j < 8) => (hb j hj).trans (bytesAt_getD f ea hj).symm
  exact ⟨by simpa using g 0 (by omega), g 1 (by omega), g 2 (by omega), g 3 (by omega),
    g 4 (by omega), g 5 (by omega), g 6 (by omega), g 7 (by omega)⟩

theorem ldWord_byte (f : Nat → BitVec 8) (a k : Nat) (hk : k < 8) :
    (bytesVal .ld (bytesAt f a 8)).extractLsb' (8 * k) 8 = f (a + k) := by
  have hshow : bytesVal .ld (bytesAt f a 8) =
      sign_extend (m := 64) ((((((((f (a + 7)).append (f (a + 6))).append (f (a + 5))).append
        (f (a + 4))).append (f (a + 3))).append (f (a + 2))).append (f (a + 1))).append
        (f (a + 0)) : BitVec (8 * 8)) := rfl
  rw [hshow, show ∀ w : BitVec (8 * 8), sign_extend (m := 64) w = w from fun w => by
    simp [sign_extend, Sail.BitVec.signExtend]]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_extractLsb', BitVec.append_eq, BitVec.getLsbD_append]
  rw [decide_eq_true (show i < 8 from hi), Bool.true_and]
  match k, hk with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ =>
    repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]
    congr 1 <;> omega

end Run

end VsaIris.Inst.Strcmp
