import VsaIris.Vsa.SymData
import Vsa.Sim.DecodeNF
import Vsa.Sim.BlockDecode

/-!
# A reflective symbolic executor for `SWP`

`symRun F cfg n s` executes a whole straight-line / branching run as ONE closed
computation over a deeply embedded symbolic state (`SE` values over the entry
registers and memory, a symbolic store list, and a residual obligation list).
`symRun_swp` (proved once, generic in the fetch function, the code ranges and the
tracked register list) turns the residual weakest precondition of the run into
`SWP` at the entry state. Consumers keep their `SWP`/`IW` statements.

Layers:
* code image: `CodeAt T img rT` (every byte of `rT` is pinned by `TextLoaded T`);
* generic machine rules `swpx_line` (any body line), `swpx_br` (conditional branch),
  `swpx_j` (direct jump), each an instance of `swp_stepD`;
* the executor `symRun` and its soundness `symRun_swp`;
* the reflective obligation checker `obCheck` over a `Geom` of per-atom interval facts, and
  `symRun_auto`, whose residual is the continuations plus the undecided obligations.
-/

namespace VsaIris.SymExec

open Vsa.Sim Vsa.MemRepr VsaIris.Sym VsaIris.MallocFast VsaIris.Inst
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

/-! ## Code image -/

def InRanges (rs : List (Nat × Nat)) (a : Nat) : Prop := ∃ r ∈ rs, r.1 ≤ a ∧ a < r.2

instance (rs : List (Nat × Nat)) (a : Nat) : Decidable (InRanges rs a) := by
  unfold InRanges; infer_instance

/-- The text list pins every byte of the ranges `rT` to the image `img`. -/
def CodeAt (T : List (Nat × BitVec 8)) (img : Nat → BitVec 8) (rT : List (Nat × Nat)) : Prop :=
  ∀ m : Mem, TextLoaded T m → ∀ a, InRanges rT a → m[a]? = some (img a)

def rangeText (img : Nat → BitVec 8) (rs : List (Nat × Nat)) : List (Nat × BitVec 8) :=
  rs.flatMap fun r => (List.range (r.2 - r.1)).map fun k => (r.1 + k, img (r.1 + k))

theorem mem_rangeText {img : Nat → BitVec 8} {rs : List (Nat × Nat)} {a : Nat}
    (h : InRanges rs a) : (a, img a) ∈ rangeText img rs := by
  obtain ⟨r, hr, h1, h2⟩ := h
  refine List.mem_flatMap.2 ⟨r, hr, List.mem_map.2 ⟨a - r.1, List.mem_range.2 (by omega), ?_⟩⟩
  rw [show r.1 + (a - r.1) = a by omega]

theorem codeAt_of_eq {T : List (Nat × BitVec 8)} {img : Nat → BitVec 8} {rT : List (Nat × Nat)}
    (h : T = rangeText img rT) : CodeAt T img rT := by
  intro m hm a ha; subst h; exact hm _ (mem_rangeText ha)

/-- Tail-recursive list equality (kernel-friendly on long literal lists). -/
def eqB : List (Nat × BitVec 8) → List (Nat × BitVec 8) → Bool
  | [], [] => true
  | p :: l, q :: l' => (p.1 == q.1 && p.2 == q.2) && eqB l l'
  | _, _ => false

theorem eqB_eq : ∀ {l l' : List (Nat × BitVec 8)}, eqB l l' = true → l = l'
  | [], [], _ => rfl
  | p :: l, q :: l', h => by
    simp only [eqB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Prod.ext h1 h2, eqB_eq h3]
  | [], _ :: _, h => by cases h
  | _ :: _, [], h => by cases h

/-- Little-endian instruction word of the image at `a`. -/
def wordAt (img : Nat → BitVec 8) (a : Nat) : BitVec 32 :=
  (((img (a + 3)).append (img (a + 2))).append (img (a + 1))).append (img a)

def Pins4OK (img : Nat → BitVec 8) (rs : List (Nat × Nat)) (a : Nat)
    (b0 b1 b2 b3 : BitVec 8) : Prop :=
  InRanges rs a ∧ InRanges rs (a + 1) ∧ InRanges rs (a + 2) ∧ InRanges rs (a + 3) ∧
  img a = b0 ∧ img (a + 1) = b1 ∧ img (a + 2) = b2 ∧ img (a + 3) = b3

instance : Decidable (Pins4OK img rs a b0 b1 b2 b3) := by unfold Pins4OK; infer_instance

theorem mkLine_fields (pc : BitVec 64) (w : BitVec 32) :
    (mkLine pc w).pc = pc ∧ (mkLine pc w).word = w ∧
    (mkLine pc w).b0 = w.extractLsb' 0 8 ∧ (mkLine pc w).b1 = w.extractLsb' 8 8 ∧
    (mkLine pc w).b2 = w.extractLsb' 16 8 ∧ (mkLine pc w).b3 = w.extractLsb' 24 8 := by
  unfold mkLine; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem bytePinsM_of {T : List (Nat × BitVec 8)} {img : Nat → BitVec 8} {rT : List (Nat × Nat)}
    (hc : CodeAt T img rT) {m : Mem} (hm : TextLoaded T m) {a : MInstr}
    (hb : Pins4OK img rT a.pc.toNat a.b0 a.b1 a.b2 a.b3) : BytePinsM m a := by
  obtain ⟨r0, r1, r2, r3, i0, i1, i2, i3⟩ := hb
  unfold BytePinsM
  rw [← i0, ← i1, ← i2, ← i3]
  exact ⟨hc m hm _ r0, hc m hm _ r1, hc m hm _ r2, hc m hm _ r3⟩

theorem bytePinsT_of {T : List (Nat × BitVec 8)} {img : Nat → BitVec 8} {rT : List (Nat × Nat)}
    (hc : CodeAt T img rT) {m : Mem} (hm : TextLoaded T m) {t : TInstr}
    (hb : Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3) : BytePinsT m t := by
  obtain ⟨r0, r1, r2, r3, i0, i1, i2, i3⟩ := hb
  unfold BytePinsT
  rw [← i0, ← i1, ← i2, ← i3]
  exact ⟨hc m hm _ r0, hc m hm _ r1, hc m hm _ r2, hc m hm _ r3⟩

/-- Decode obligation for a body line: closed per word by `fun _ => rfl` on `decodeN`. -/
def DecM (a : MInstr) : Prop := ∀ σ, decodeN a.word σ = .ok (astOfM a) σ

/-- Decode obligation for a terminator. -/
def DecT (t : TInstr) : Prop := ∀ σ, decodeN t.word σ = .ok (astOfT t) σ

theorem decodeFactM_of {a : MInstr} (h : DecM a) : DecodeFactM a :=
  fun s h1 h2 h3 => decodeW s h1 h2 h3 (h s)

theorem decodeFactT_of {t : TInstr} (h : DecT t) : DecodeFactT t :=
  fun s h1 h2 h3 => decodeW s h1 h2 h3 (h s)

/-! ## Generic machine rules -/

def isStoreK : MKind → Bool
  | .sw | .sd | .sb | .sh => true
  | _ => false

theorem lookupG_eraseG_ne {x n : Nat} (h : n ≠ x) : ∀ L, lookupG x (eraseG n L) = lookupG x L
  | [] => rfl
  | (m, v) :: L => by
    unfold eraseG
    by_cases hm : m = n
    · subst hm; rw [if_pos rfl]; conv => rhs; unfold lookupG
      rw [if_neg h]; exact lookupG_eraseG_ne h L
    · rw [if_neg hm]; unfold lookupG; split
      · rfl
      · exact lookupG_eraseG_ne h L

theorem lookupG_pinsOf {R : Nat → BitVec 64} {x : Nat} :
    ∀ {ks : List Nat}, x ∈ ks → lookupG x (pinsOf ks R) = some (if x = gp then gpV else R x)
  | k :: ks, h => by
    simp only [pinsOf, List.map_cons, lookupG]
    by_cases hk : k = x
    · subst hk; rw [if_pos rfl]
    · rw [if_neg hk]
      exact lookupG_pinsOf (List.mem_of_ne_of_mem (fun e => hk e.symm) h)

theorem stepGM_nonstore {a : MInstr} (h : isStoreK a.kind = false) (L : GRegs)
    (l0 : List (BitVec 8)) : stepGM a L l0 = (a.rd, wvalM a L l0) :: eraseG a.rd L := by
  unfold stepGM; revert h; cases a.kind <;> intro h <;> first | rfl | cases h

theorem stepGM_store {a : MInstr} (h : isStoreK a.kind = true) (L : GRegs) (l0 : List (BitVec 8)) :
    stepGM a L l0 = L := by
  unfold stepGM; revert h; cases a.kind <;> intro h <;> first | rfl | cases h

/-- Register continuation of one line. -/
def lineR (a : MInstr) (L : GRegs) (l0 : List (BitVec 8)) (R : Nat → BitVec 64) :
    Nat → BitVec 64 :=
  if isStoreK a.kind then R else upd R a.rd (wvalM a L l0)

theorem finReg_line (a : MInstr) (ks : List Nat) (R : Nat → BitVec 64)
    (lds : List (List (BitVec 8))) (x : Nat) (hx : x ∈ ks) (hg : x ≠ gp) :
    finReg [⟨[a], none⟩] (pinsOf ks R) lds x = lineR a (pinsOf ks R) (lds.headD []) R x := by
  unfold finReg lineR
  show (lookupG x (stepGM a (pinsOf ks R) (lds.headD []))).getD 0 = _
  cases hs : isStoreK a.kind
  · rw [stepGM_nonstore hs]
    simp only [Bool.false_eq_true, ite_false]
    unfold upd lookupG
    by_cases hr : a.rd = x
    · subst hr; simp
    · rw [if_neg hr, if_neg (Ne.symm hr), lookupG_eraseG_ne hr, lookupG_pinsOf hx, if_neg hg]; rfl
  · rw [stepGM_store hs, lookupG_pinsOf hx, if_neg hg]; simp

theorem finReg_gp (a : MInstr) (ks : List Nat) (R : Nat → BitVec 64)
    (lds : List (List (BitVec 8))) (hx : gp ∈ ks) (hw : ∀ x ∈ wrChain [⟨[a], none⟩], x ≠ gp) :
    finReg [⟨[a], none⟩] (pinsOf ks R) lds gp = gpV := by
  unfold finReg
  show (lookupG gp (stepGM a (pinsOf ks R) (lds.headD []))).getD 0 = _
  cases hs : isStoreK a.kind
  · rw [stepGM_nonstore hs]
    have hrd : a.rd ≠ gp := hw a.rd (by
      show a.rd ∈ wrRegsM [a] ++ []
      unfold wrRegsM; revert hs; cases a.kind <;> intro hs <;> first | (cases hs; done) | simp)
    unfold lookupG
    rw [if_neg hrd, lookupG_eraseG_ne hrd, lookupG_pinsOf hx, if_pos rfl]; rfl
  · rw [stepGM_store hs, lookupG_pinsOf hx, if_pos rfl]; rfl

theorem log_line (a : MInstr) (L : GRegs) (lds : List (List (BitVec 8))) :
    (segOut [⟨[a], none⟩] L lds).log =
      (if isStoreK a.kind then [wentryM a L] else []) := by
  show [] ++ wlogM [a] L lds = _
  unfold wlogM
  cases a.kind <;> rfl

section rules
variable {live : Nat → Prop} {T D : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- Every body line, any kind: the continuation is `lineR`/`writeLog` of the line's log. -/
theorem swpx_line (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (hc : CodeAt T img rT)
    (a : MInstr) {R : Nat → BitVec 64} {Mt : Mem}
    (ks : List Nat) (lds : List (List (BitVec 8))) (LD W : List Nat)
    (hwf : ChainOK a.pc ks [⟨[a], none⟩]) (hkeys : KeysOK ks)
    (hwr : ∀ x ∈ wrChain [⟨[a], none⟩], x ∈ ks)
    (hcover : ∀ b, b ∉ W → OutL (if isStoreK a.kind then [wentryM a (pinsOf ks R)] else []) b)
    (hlive : ∀ p ∈ T, live p.1)
    (hb : Pins4OK img rT a.pc.toNat a.b0 a.b1 a.b2 a.b3)
    (hdec : DecM a)
    (hmf : ∀ m : Mem, TextLoaded T m → DataReads D m → (∀ b ∈ LD, (m[b]?).getD 0 = imgM Mt b) →
      MemFacts m (pinsOf ks R) (lds.headD []) a)
    (hPC : VsaIris.PC ∈ rs)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))
    (hgpw : ∀ x ∈ wrChain [⟨[a], none⟩], x ≠ gp) (hgprs : gp ∉ rs)
    (hLD : ∀ b ∈ LD, S b) (hW : ∀ b ∈ W, S b)
    (hRo : ∀ x ∈ rs, x ≠ VsaIris.PC → x ∉ ks → lineR a (pinsOf ks R) (lds.headD []) R x = R x)
    (hk : SWP live (T ++ D) rs S Q (BitVec.addInt a.pc 4)
      (lineR a (pinsOf ks R) (lds.headD []) R)
      (writeLog Mt (if isStoreK a.kind then [wentryM a (pinsOf ks R)] else []))) :
    SWP live (T ++ D) rs S Q a.pc R Mt :=
  swp_stepD [⟨[a], none⟩] ks lds LD W 0 rfl hwf hkeys hwr
    (fun b hb' => by rw [log_line]; exact hcover b hb') hlive
    (fun m hT hD hLD' => ⟨⟨⟨bytePinsM_of hc hT hb, decodeFactM_of hdec, hmf m hT hD hLD', trivial⟩,
      trivial, trivial⟩, trivial⟩)
    hPC hks (fun h => finReg_gp _ ks R lds h hgpw) hgprs hLD hW rfl
    (fun x hx hg => finReg_line _ ks R lds x hx hg) hRo (by rw [log_line]) hk

/-- A conditional branch, either outcome (`taken` decided by the guard). -/
theorem swpx_br (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (hc : CodeAt T img rT)
    (t : TInstr) (op : bop) (taken : Bool) (ht : t.kind = .br op taken)
    {R : Nat → BitVec 64} {Mt : Mem} (ks : List Nat)
    (hwf : ChainOK t.pc ks [⟨[], some t⟩]) (hkeys : KeysOK ks)
    (hlive : ∀ p ∈ T, live p.1)
    (hb : Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3)
    (hdec : DecT t)
    (hg : guardB op (srcVal t.rs1 (pinsOf ks R)) (srcVal t.rs2 (pinsOf ks R)) = taken)
    (hPC : VsaIris.PC ∈ rs)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC)) (hgprs : gp ∉ rs)
    (hk : SWP live (T ++ D) rs S Q (tgtPC0 t) R Mt) :
    SWP live (T ++ D) rs S Q t.pc R Mt := by
  refine swp_stepD [⟨[], some t⟩] ks [] [] [] 0 rfl hwf hkeys (fun x hx => by cases hx)
    (fun _ _ => trivial) hlive
    (fun m hT _ _ => ⟨⟨trivial, ⟨bytePinsT_of hc hT hb, decodeFactT_of hdec⟩, ?_⟩, trivial⟩)
    hPC hks (fun h => by
      show (lookupG gp (pinsOf ks R)).getD 0 = gpV
      rw [lookupG_pinsOf h, if_pos rfl]; rfl) hgprs
    (fun _ h => by cases h) (fun _ h => by cases h) ?_ ?_ (fun _ _ _ _ => rfl) rfl hk
  · show TermFactsT (pinsOf ks R) t
    unfold TermFactsT; rw [ht]; exact hg
  · show tgtPCT t (pinsOf ks R) = tgtPC0 t
    unfold tgtPCT; rw [ht]
  · intro x hx hgx
    show (lookupG x (pinsOf ks R)).getD 0 = R x
    rw [lookupG_pinsOf hx, if_neg hgx]; rfl

/-- A direct jump `j`. -/
theorem swpx_j (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (hc : CodeAt T img rT)
    (t : TInstr) (ht : t.kind = .j) {R : Nat → BitVec 64} {Mt : Mem}
    (hwf : ChainOK t.pc [] [⟨[], some t⟩])
    (hlive : ∀ p ∈ T, live p.1)
    (hb : Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3)
    (hdec : DecT t) (hPC : VsaIris.PC ∈ rs) (hgprs : gp ∉ rs)
    (hk : SWP live (T ++ D) rs S Q (tgtPC0 t) R Mt) :
    SWP live (T ++ D) rs S Q t.pc R Mt := by
  refine swp_stepD [⟨[], some t⟩] [] [] [] [] 0 rfl hwf (fun _ h => by cases h)
    (fun x hx => by cases hx) (fun _ _ => trivial) hlive
    (fun m hT _ _ => ⟨⟨trivial, ⟨bytePinsT_of hc hT hb, decodeFactT_of hdec⟩, ?_⟩, trivial⟩)
    hPC (fun x hx => by cases hx) (fun h => by cases h) hgprs
    (fun _ h => by cases h) (fun _ h => by cases h) ?_ (fun _ h => by cases h)
    (fun _ _ _ _ => rfl) rfl hk
  · show TermFactsT [] t
    unfold TermFactsT; rw [ht]; trivial
  · show tgtPCT t [] = tgtPC0 t
    unfold tgtPCT; rw [ht]

/-- An indirect jump `jalr x0, 0(rs1)`: the continuation is at the (aligned) register value. -/
theorem swpx_jr (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (hc : CodeAt T img rT)
    (t : TInstr) (ht : t.kind = .jr) (hi : t.imm12 = 0) {R : Nat → BitVec 64} {Mt : Mem}
    (ks : List Nat) (hwf : ChainOK t.pc ks [⟨[], some t⟩]) (hkeys : KeysOK ks)
    (hlive : ∀ p ∈ T, live p.1)
    (hb : Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3)
    (hdec : DecT t) (hPC : VsaIris.PC ∈ rs)
    (hks : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC)) (hgprs : gp ∉ rs)
    (hal : (srcVal t.rs1 (pinsOf ks R)).toNat % 4 = 0)
    (hk : SWP live (T ++ D) rs S Q (srcVal t.rs1 (pinsOf ks R)) R Mt) :
    SWP live (T ++ D) rs S Q t.pc R Mt := by
  have htg : Sail.BitVec.update (srcVal t.rs1 (pinsOf ks R) + sign_extend (m := 64) t.imm12) 0 0#1
      = srcVal t.rs1 (pinsOf ks R) := by rw [hi]; exact ret_tgt _ hal
  refine swp_stepD [⟨[], some t⟩] ks [] [] [] 0 rfl hwf hkeys (fun x hx => by cases hx)
    (fun _ _ => trivial) hlive
    (fun m hT _ _ => ⟨⟨trivial, ⟨bytePinsT_of hc hT hb, decodeFactT_of hdec⟩, ?_⟩, trivial⟩)
    hPC hks (fun h => by
      show (lookupG gp (pinsOf ks R)).getD 0 = gpV
      rw [lookupG_pinsOf h, if_pos rfl]; rfl) hgprs
    (fun _ h => by cases h) (fun _ h => by cases h) ?_ ?_ (fun _ _ _ _ => rfl) rfl hk
  · show TermFactsT (pinsOf ks R) t
    unfold TermFactsT; rw [ht]; show (Sail.BitVec.update _ 0 0#1).toNat % 4 = 0
    rw [htg]; exact hal
  · show tgtPCT t (pinsOf ks R) = _
    unfold tgtPCT; rw [ht]; exact htg
  · intro x hx hgx
    show (lookupG x (pinsOf ks R)).getD 0 = R x
    rw [lookupG_pinsOf hx, if_neg hgx]; rfl

end rules


/-! ## Symbolic values -/

deriving instance DecidableEq for MInstr

inductive SE where
  | c (v : BitVec 64)
  | r (i : Nat)
  | add (a b : SE)
  | sub (a b : SE)
  | ld (k : MKind) (a : SE)
  | ldD (k : MKind) (a : SE)
  | alu (i : MInstr) (x y : SE)
deriving DecidableEq

/-- `wvalM` of a register-only line, with the two source values given. -/
def aluVal (a : MInstr) (X Y : BitVec 64) : BitVec 64 :=
  match a.kind with
  | .addi => X + sign_extend (m := 64) a.imm
  | .add  => X + Y
  | .sub  => X - Y
  | .or   => X ||| Y
  | .and  => X &&& Y
  | .srl  => shift_bits_right (X) (Sail.BitVec.extractLsb (Y) 5 0)
  | .xor  => X ^^^ Y
  | .sll  => shift_bits_left (X) (Sail.BitVec.extractLsb (Y) 5 0)
  | .addiw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (X + sign_extend (m := 64) a.imm) 31 0)
  | .slli => shift_bits_left (X) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .srli => shift_bits_right (X) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .srai => shift_bits_right_arith (X) (Sail.BitVec.extractLsb (shamtOf a) 5 0)
  | .slti => zero_extend (m := 64)
      (bool_to_bit (zopz0zI_s (X) (sign_extend (m := 64) a.imm)))
  | .slt  => zero_extend (m := 64) (bool_to_bit (zopz0zI_s (X) (Y)))
  | .subw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (X) 31 0
        - Sail.BitVec.extractLsb (Y) 31 0)
  | .addw => sign_extend (m := 64)
      (Sail.BitVec.extractLsb (X) 31 0
        + Sail.BitVec.extractLsb (Y) 31 0)
  | .sllw => sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb (X) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (Y) 31 0) 4 0))
  | .srlw => sign_extend (m := 64)
      (shift_bits_right (Sail.BitVec.extractLsb (X) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (Y) 31 0) 4 0))
  | .sraw => sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb (X) 31 0)
        (Sail.BitVec.extractLsb (Sail.BitVec.extractLsb (Y) 31 0) 4 0))
  | .auipc => a.pc + sign_extend (m := 64) (imm20Of a +++ (0x000#12))
  | .lui => sign_extend (m := 64) (imm20Of a +++ (0x000#12))
  | .xori => X ^^^ sign_extend (m := 64) a.imm
  | .andi => X &&& sign_extend (m := 64) a.imm
  | .ori => X ||| sign_extend (m := 64) a.imm
  | .slliw => sign_extend (m := 64)
      (shift_bits_left (Sail.BitVec.extractLsb (X) 31 0) (shamt5Of a))
  | .srliw => sign_extend (m := 64)
      (shift_bits_right (Sail.BitVec.extractLsb (X) 31 0) (shamt5Of a))
  | .sraiw => sign_extend (m := 64)
      (shift_bits_right_arith (Sail.BitVec.extractLsb (X) 31 0) (shamt5Of a))
  | _ => 0#64

/-- Entry registers and entry memory. -/
structure Env where
  R0 : Nat → BitVec 64
  M0 : Mem
  D0 : Mem

def SE.den (ρ : Env) : SE → BitVec 64
  | .c v => v
  | .r i => ρ.R0 i
  | .add a b => a.den ρ + b.den ρ
  | .sub a b => a.den ρ - b.den ρ
  | .ld k a => ldv k ρ.M0 (a.den ρ).toNat
  | .ldD k a => ldv k ρ.D0 (a.den ρ).toNat
  | .alu i x y => aluVal i (x.den ρ) (y.den ρ)

/-- `e + k`, built as the per-step normaliser (`sx_norm`) leaves it: literals fold, `+ 0`
vanishes, nothing reassociates. -/
def addC (e : SE) (k : BitVec 64) : SE :=
  match e with
  | .c v => .c (v + k)
  | e => if k = 0 then e else .add e (.c k)

theorem addC_den (ρ : Env) (e : SE) (k : BitVec 64) : (addC e k).den ρ = e.den ρ + k := by
  unfold addC
  split
  · rfl
  · split
    · rename_i h; subst h; simp
    · rfl

def addS : SE → SE → SE
  | .c x, .c y => .c (x + y)
  | a, .c k => if k = 0 then a else .add a (.c k)
  | a, b => .add a b

theorem addS_den (ρ : Env) (a b : SE) : (addS a b).den ρ = a.den ρ + b.den ρ := by
  unfold addS
  split
  · rfl
  · split
    · rename_i h; subst h; simp [SE.den]
    · rfl
  · rfl

def subS (a b : SE) : SE := .sub a b

theorem subS_den (ρ : Env) (a b : SE) : (subS a b).den ρ = a.den ρ - b.den ρ := rfl

/-- Base atom and accumulated constant offset. -/
def base : SE → SE × BitVec 64
  | .add a (.c v) => ((base a).1, (base a).2 + v)
  | .c v => (.c 0, v)
  | e => (e, 0)

theorem base_den (ρ : Env) : ∀ e : SE, e.den ρ = (base e).1.den ρ + (base e).2
  | .add a (.c v) => by
    show a.den ρ + v = (base a).1.den ρ + ((base a).2 + v)
    rw [base_den ρ a, BitVec.add_assoc]
  | .c v => by simp [base, SE.den]
  | .r _ => by simp [base]
  | .add _ (.r _) => by simp [base]
  | .add _ (.add _ _) => by simp [base]
  | .add _ (.sub _ _) => by simp [base]
  | .add _ (.ld _ _) => by simp [base]
  | .add _ (.ldD _ _) => by simp [base]
  | .add _ (.alu _ _ _) => by simp [base]
  | .sub _ _ => by simp [base]
  | .ld _ _ => by simp [base]
  | .ldD _ _ => by simp [base]
  | .alu _ _ _ => by simp [base]

/-! ## Symbolic registers -/

def lookupS (r : Nat) : List (Nat × SE) → SE
  | [] => .r r
  | (k, e) :: L => if k = r then e else lookupS r L

def rdS (L : List (Nat × SE)) (r : Nat) : SE :=
  if r = 0 then .c 0 else if r = gp then .c gpV else lookupS r L

def regsDen (ρ : Env) : List (Nat × SE) → Nat → BitVec 64
  | [] => ρ.R0
  | (k, e) :: L => upd (regsDen ρ L) k (e.den ρ)

def rdR (R : Nat → BitVec 64) (r : Nat) : BitVec 64 := if r = 0 then 0 else if r = gp then gpV else R r

theorem lookupS_den (ρ : Env) (r : Nat) :
    ∀ L : List (Nat × SE), (lookupS r L).den ρ = regsDen ρ L r
  | [] => rfl
  | (k, e) :: L => by
    unfold lookupS regsDen upd
    by_cases h : k = r
    · subst h; simp
    · rw [if_neg h, if_neg (Ne.symm h)]; exact lookupS_den ρ r L

theorem rdS_den (ρ : Env) (L : List (Nat × SE)) (r : Nat) :
    (rdS L r).den ρ = rdR (regsDen ρ L) r := by
  unfold rdS rdR; by_cases h : r = 0
  · simp [h, SE.den]
  · simp only [h, if_false]
    by_cases hg : r = gp
    · simp [hg, SE.den]
    · simp only [hg, if_false]; exact lookupS_den ρ r L

theorem srcVal_pins {ks : List Nat} {R : Nat → BitVec 64} {r : Nat} (h : r = 0 ∨ r ∈ ks) :
    srcVal r (pinsOf ks R) = rdR R r := by
  cases r with
  | zero => rfl
  | succ n =>
    rcases h with h | h
    · cases h
    · simp only [srcVal, lookupG_pinsOf h, rdR, Option.getD_some]
      rfl

/-! ## Symbolic memory and store forwarding -/

/-- Symbolic write log, newest first: `(address, width, value)`. -/
abbrev SMem := List (SE × Nat × SE)

def memDen (ρ : Env) : SMem → Mem
  | [] => ρ.M0
  | (a, w, v) :: t => writeLog (memDen ρ t) [((a.den ρ).toNat, w, v.den ρ)]

/-- Residual obligations; `den` is the proposition the consumer discharges. -/
inductive SOb where
  | ld (e : SE) (w : Nat)
  | ldD (e : SE) (w : Nat)
  | st (e : SE) (w : Nat)
  | disj (a : SE) (wa : Nat) (b : SE) (wb : Nat)
  | al4 (e : SE)
  | decM (pc : BitVec 64) (w : BitVec 32)
  | decT (t : TInstr)

def SOb.den (ρ : Env) (S : Nat → Prop) (DA : List Nat) : SOb → Prop
  | .ld e w => LdOK (e.den ρ).toNat w ∧ ∀ b ∈ accAddrs (e.den ρ).toNat w, S b
  | .ldD e w => LdOK (e.den ρ).toNat w ∧ ∀ b ∈ accAddrs (e.den ρ).toNat w, b ∈ DA
  | .st e w => StOK (e.den ρ).toNat w ∧ ∀ b ∈ accAddrs (e.den ρ).toNat w, S b
  | .disj a wa b wb => (a.den ρ).toNat + wa ≤ (b.den ρ).toNat ∨ (b.den ρ).toNat + wb ≤ (a.den ρ).toNat
  | .al4 e => (e.den ρ).toNat % 4 = 0
  | .decM pc w => DecM (mkLine pc w)
  | .decT t => DecT t

def ObsOK (ρ : Env) (S : Nat → Prop) (DA : List Nat) (obs : List SOb) : Prop :=
  ∀ o ∈ obs, o.den ρ S DA

/-- Same base, constant offsets: disjoint by the offset difference alone. -/
def sepC (c1 : BitVec 64) (w1 : Nat) (c2 : BitVec 64) (w2 : Nat) : Bool :=
  decide (0 < w1 ∧ w1 ≤ (c2 - c1).toNat ∧ w2 ≤ (c1 - c2).toNat)

theorem sepC_sound {b c1 c2 : BitVec 64} {w1 w2 : Nat} (h : sepC c1 w1 c2 w2 = true) :
    (b + c1).toNat + w1 ≤ (b + c2).toNat ∨ (b + c2).toNat + w2 ≤ (b + c1).toNat := by
  simp only [sepC, decide_eq_true_eq] at h
  obtain ⟨h0, h1, h2⟩ := h
  rw [BitVec.toNat_sub] at h1 h2
  rw [BitVec.toNat_add, BitVec.toNat_add]
  have := b.isLt; have := c1.isLt; have := c2.isLt
  omega

def symLoad (k : MKind) (a : SE) : SMem → Option (SE × List SOb)
  | [] => some (.ld k a, [])
  | (sa, sw, sv) :: t =>
    if base a = base sa ∧ k = .ld ∧ sw = 8 then some (sv, [])
    else if (base a).1 = (base sa).1 then
      (if sepC (base a).2 (widthOfM k) (base sa).2 sw then symLoad k a t else none)
    else (symLoad k a t).map fun p => (p.1, .disj a (widthOfM k) sa sw :: p.2)

theorem symLoad_sound (ρ : Env) (S : Nat → Prop) (DA : List Nat) (k : MKind) (a : SE) :
    ∀ (st : SMem) (e : SE) (obs : List SOb), symLoad k a st = some (e, obs) →
      ObsOK ρ S DA obs → e.den ρ = ldv k (memDen ρ st) (a.den ρ).toNat
  | [], e, obs, h, _ => by cases h; rfl
  | (sa, sw, sv) :: t, e, obs, h, hob => by
    unfold symLoad at h
    by_cases h1 : base a = base sa ∧ k = .ld ∧ sw = 8
    · rw [if_pos h1] at h; cases h
      obtain ⟨hb, rfl, rfl⟩ := h1
      show sv.den ρ = ldv .ld (writeLog (memDen ρ t) [((sa.den ρ).toNat, 8, sv.den ρ)]) (a.den ρ).toNat
      rw [base_den ρ a, hb, ← base_den ρ sa]
      exact (ldv_store_hit _ _ _).symm
    · rw [if_neg h1] at h
      by_cases h2 : (base a).1 = (base sa).1
      · rw [if_pos h2] at h
        by_cases h3 : sepC (base a).2 (widthOfM k) (base sa).2 sw = true
        · rw [if_pos h3] at h
          rw [symLoad_sound ρ S DA k a t e obs h hob]
          show _ = ldv k (writeLog (memDen ρ t) [((sa.den ρ).toNat, sw, sv.den ρ)]) _
          rw [ldv_store_miss]
          have := sepC_sound (b := (base a).1.den ρ) h3
          rw [base_den ρ a, base_den ρ sa, ← h2]
          exact this
        · rw [if_neg h3] at h; cases h
      · rw [if_neg h2] at h
        cases hl : symLoad k a t with
        | none => rw [hl] at h; cases h
        | some p =>
          rw [hl] at h; cases h
          rw [symLoad_sound ρ S DA k a t p.1 p.2 hl (fun o ho => hob o (List.mem_cons_of_mem _ ho))]
          show _ = ldv k (writeLog (memDen ρ t) [((sa.den ρ).toNat, sw, sv.den ρ)]) _
          rw [ldv_store_miss]
          exact hob _ List.mem_cons_self


/-! ## One body line, symbolically -/

def isLoadK : MKind → Bool
  | .lw | .lwu | .ld | .lbu | .lh | .lhu => true
  | _ => false

theorem not_store_of_load {k : MKind} (h : isLoadK k = true) : isStoreK k = false := by
  cases k <;> first | rfl | cases h

/-- Nonzero, duplicate-free register list. -/
def nzd : List Nat → List Nat
  | [] => []
  | x :: l => if x = 0 ∨ x ∈ nzd l then nzd l else x :: nzd l

theorem mem_nzd {x : Nat} : ∀ {l : List Nat}, x ∈ l → x = 0 ∨ x ∈ nzd l
  | y :: l, h => by
    unfold nzd
    rcases List.mem_cons.1 h with rfl | h
    · by_cases hc : x = 0 ∨ x ∈ nzd l
      · rw [if_pos hc]; exact hc
      · rw [if_neg hc]; exact .inr List.mem_cons_self
    · rcases mem_nzd h with h0 | h1
      · exact .inl h0
      · split
        · exact .inr h1
        · exact .inr (List.mem_cons_of_mem _ h1)

def lineKs (a : MInstr) : List Nat :=
  match a.kind with
  | .sw | .sd | .sb | .sh => nzd [a.rs1, a.rs2]
  | _ => nzd [a.rs1, a.rs2, a.rd]

theorem rs1_mem (a : MInstr) : a.rs1 = 0 ∨ a.rs1 ∈ lineKs a := by
  unfold lineKs; split <;> exact mem_nzd (by simp)

theorem rs2_mem (a : MInstr) : a.rs2 = 0 ∨ a.rs2 ∈ lineKs a := by
  unfold lineKs; split <;> exact mem_nzd (by simp)

abbrev sext12 (i : BitVec 12) : BitVec 64 := sign_extend (m := 64) i

def eaS (a : MInstr) (L : List (Nat × SE)) : SE := addC (rdS L a.rs1) (sext12 a.imm)

/-- Static configuration: code image, code ranges, tracked registers, stop points, the
address bases whose loads read the data view (`dataOf Dt DA`) instead of owned memory, and known
data-view words `(kind, address, value)`. -/
structure Cfg where
  img : Nat → BitVec 8
  rT : List (Nat × Nat)
  rs : List Nat
  stops : List (BitVec 64)
  dbase : List SE
  kv : List (MKind × SE × BitVec 64) := []

/-- A load at a constant address inside the code ranges reads the image. -/
def imgOK (C : Cfg) (v : BitVec 64) (w : Nat) : Bool :=
  decide (LdOK v.toNat w) && (List.range w).all fun j => decide (InRanges C.rT (v.toNat + j))

def kvFind (kv : List (MKind × SE × BitVec 64)) (k : MKind) (a : SE) : Option (BitVec 64) :=
  (kv.find? fun e => decide (e.1 = k ∧ e.2.1 = a)).map (·.2.2)

/-- Symbolic effect of a supported body line: new registers, new store list, obligations. -/
def symBody (C : Cfg) (a : MInstr) (L : List (Nat × SE)) (M : SMem) :
    Option (List (Nat × SE) × SMem × List SOb) :=
  if isLoadK a.kind then
    if hI : (match eaS a L with | .c v => imgOK C v (widthOfM a.kind) | _ => false) = true then
      match eaS a L with
      | .c v => some ((a.rd, .c (bytesVal a.kind (bytesAt C.img v.toNat (widthOfM a.kind)))) :: L, M, [])
      | _ => none
    else if decide ((base (eaS a L)).1 ∈ C.dbase) then
      some ((a.rd, (kvFind C.kv a.kind (eaS a L)).elim (.ldD a.kind (eaS a L)) .c) :: L, M,
        [.ldD (eaS a L) (widthOfM a.kind)])
    else
    (symLoad a.kind (eaS a L) M).map fun p =>
      ((a.rd, p.1) :: L, M, .ld (eaS a L) (widthOfM a.kind) :: p.2)
  else if isStoreK a.kind then
    some (L, (eaS a L, widthOfM a.kind, rdS L a.rs2) :: M, [.st (eaS a L) (widthOfM a.kind)])
  else
    match a.kind with
    | .addi => some ((a.rd, eaS a L) :: L, M, [])
    | .add => some ((a.rd, addS (rdS L a.rs1) (rdS L a.rs2)) :: L, M, [])
    | .sub => some ((a.rd, subS (rdS L a.rs1) (rdS L a.rs2)) :: L, M, [])
    | _ => some ((a.rd, match rdS L a.rs1, rdS L a.rs2 with
        | .c x, .c y => .c (aluVal a x y)
        | x, y => .alu a x y) :: L, M, [])

/-- The decidable per-line side conditions of `swpx_line`. -/
structure LineOK (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (a : MInstr) :
    Prop where
  wf : ChainOK a.pc (lineKs a) [⟨[a], none⟩]
  keys : KeysOK (lineKs a)
  wr : ∀ x ∈ wrChain [⟨[a], none⟩], x ∈ lineKs a
  pins : Pins4OK img rT a.pc.toNat a.b0 a.b1 a.b2 a.b3
  regs : ∀ x ∈ lineKs a, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC)
  nogp : ∀ x ∈ wrChain [⟨[a], none⟩], x ≠ gp

def lineChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (a : MInstr) : Bool :=
  decide (ChainOK a.pc (lineKs a) [⟨[a], none⟩]) && decide (KeysOK (lineKs a)) &&
  decide (∀ x ∈ wrChain [⟨[a], none⟩], x ∈ lineKs a) &&
  decide (Pins4OK img rT a.pc.toNat a.b0 a.b1 a.b2 a.b3) &&
  decide (∀ x ∈ lineKs a, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC)) &&
  decide (∀ x ∈ wrChain [⟨[a], none⟩], x ≠ gp)

theorem LineOK.of_chk {img : Nat → BitVec 8} {rT : List (Nat × Nat)} {rs : List Nat} {a : MInstr}
    (h : lineChk img rT rs a = true) : LineOK img rT rs a := by
  simp only [lineChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem eaddrM_eq (ρ : Env) {a : MInstr} {L : List (Nat × SE)} {ks : List Nat}
    (h1 : a.rs1 = 0 ∨ a.rs1 ∈ ks) :
    eaddrM a (pinsOf ks (regsDen ρ L)) = (eaS a L).den ρ := by
  unfold eaddrM eaS
  rw [addC_den, rdS_den, srcVal_pins h1]

theorem wvalM_load {a : MInstr} (h : isLoadK a.kind = true) (L : GRegs) (l0 : List (BitVec 8)) :
    wvalM a L l0 = bytesVal a.kind l0 := by
  unfold wvalM; revert h; cases a.kind <;> intro h <;> first | rfl | cases h

theorem wrChain_nonstore {a : MInstr} (h : isStoreK a.kind = false) :
    wrChain [⟨[a], none⟩] = [a.rd] := by
  show wrRegsM [a] ++ [] = _
  unfold wrRegsM; revert h; cases a.kind <;> intro h <;> first | rfl | cases h

theorem lpins2_fn {m : Mem} {f : Nat → BitVec 8} {a : Nat}
    (h : ∀ b ∈ accAddrs a 2, (m[b]?).getD 0 = f b) :
    (m[a]?).getD 0 = (bytesAt f a 2).getD 0 0#8 ∧ (m[a + 1]?).getD 0 = (bytesAt f a 2).getD 1 0#8 := by
  have h0 := (h _ (mem_accAddrs (j := 0) (by omega))).trans (bytesAt_getD f a (n := 2) (by omega)).symm
  exact ⟨by simpa using h0, (h _ (mem_accAddrs (j := 1) (by omega))).trans
    (bytesAt_getD f a (n := 2) (by omega)).symm⟩

theorem memFacts_loadF {a : MInstr} (h : isLoadK a.kind = true) {m : Mem} {L : GRegs}
    {f : Nat → BitVec 8}
    (hea : LdOK (eaddrM a L).toNat (widthOfM a.kind))
    (hp : ∀ b ∈ accAddrs (eaddrM a L).toNat (widthOfM a.kind), (m[b]?).getD 0 = f b) :
    MemFacts m L ((bytesAt f (eaddrM a L).toNat (widthOfM a.kind) :: []).headD []) a := by
  unfold MemFacts
  revert h hea hp
  cases a.kind <;> intro h hea hp <;> first
    | exact And.intro hea (lpins4_fn hp)
    | exact And.intro hea (lpins8_fn hp)
    | exact And.intro hea (lpins1_fn hp)
    | exact And.intro hea (lpins2_fn hp)
    | cases h

theorem memFacts_load {a : MInstr} (h : isLoadK a.kind = true) {m Mt : Mem} {L : GRegs}
    (hea : LdOK (eaddrM a L).toNat (widthOfM a.kind))
    (hp : ∀ b ∈ accAddrs (eaddrM a L).toNat (widthOfM a.kind), (m[b]?).getD 0 = imgM Mt b) :
    MemFacts m L ((bytesAt (imgM Mt) (eaddrM a L).toNat (widthOfM a.kind) :: []).headD []) a := by
  unfold MemFacts
  revert h hea hp
  cases a.kind <;> intro h hea hp <;> first
    | exact And.intro hea (lpins4_img hp)
    | exact And.intro hea (lpins8_img hp)
    | exact And.intro hea (lpins1_img hp)
    | exact And.intro hea (lpins2_img hp)
    | cases h

theorem memFacts_store {a : MInstr} (h : isStoreK a.kind = true) {m : Mem} {L : GRegs}
    {l0 : List (BitVec 8)} (hea : StOK (eaddrM a L).toNat (widthOfM a.kind)) :
    MemFacts m L l0 a := by
  unfold MemFacts
  revert h hea
  cases a.kind <;> intro h hea <;> first
    | exact hea
    | exact And.intro hea.1 (And.intro hea.2.1 hea.2.2.1)
    | cases h

section body
variable {live : Nat → Prop} {T D : List (Nat × BitVec 8)} {rs : List Nat} {S : Nat → Prop}
  {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

theorem lineR_nonstore {a : MInstr} (h : isStoreK a.kind = false) (L : GRegs) (l0 : List (BitVec 8))
    (R : Nat → BitVec 64) : lineR a L l0 R = upd R a.rd (wvalM a L l0) := by
  unfold lineR; rw [h]; rfl

theorem wvalM_alu {a : MInstr} (h : isLoadK a.kind = false) (L : GRegs) (l0 : List (BitVec 8)) :
    wvalM a L l0 = aluVal a (srcVal a.rs1 L) (srcVal a.rs2 L) := by
  obtain ⟨pc, w, b0, b1, b2, b3, k, rd, rs1, rs2, imm⟩ := a
  cases k <;> first | rfl | cases h

theorem body_sound (img : Nat → BitVec 8) (rT : List (Nat × Nat)) {Dt : Mem} {DA : List Nat}
    (hc : CodeAt T img rT) (hlive : ∀ p ∈ T, live p.1) (hPC : VsaIris.PC ∈ rs) (hgprs : gp ∉ rs)
    (ρ : Env) (hD : ρ.D0 = Dt) (C : Cfg) (hCi : C.img = img) (hCr : C.rT = rT)
    (hkv : ∀ e ∈ C.kv, ldv e.1 ρ.D0 (e.2.1.den ρ).toNat = e.2.2)
    (a : MInstr) (L L' : List (Nat × SE)) (M M' : SMem) (obs : List SOb)
    (hs : symBody C a L M = some (L', M', obs)) (hok : LineOK img rT rs a) (hdec : DecM a)
    (hob : ObsOK ρ S DA obs)
    (hk : SWP live (T ++ dataOf Dt DA) rs S Q (BitVec.addInt a.pc 4) (regsDen ρ L') (memDen ρ M')) :
    SWP live (T ++ dataOf Dt DA) rs S Q a.pc (regsDen ρ L) (memDen ρ M) := by
  subst hD
  have h1 := rs1_mem a
  have h2 := rs2_mem a
  have hea := eaddrM_eq ρ (L := L) h1
  have hRo : ∀ l0, isStoreK a.kind = false → ∀ x ∈ rs, x ≠ VsaIris.PC → x ∉ lineKs a →
      lineR a (pinsOf (lineKs a) (regsDen ρ L)) l0 (regsDen ρ L) x = regsDen ρ L x := by
    intro l0 hst x _ _ hx
    rw [lineR_nonstore hst]
    refine upd_other _ _ (fun e => hx ?_)
    exact e ▸ hok.wr _ (by rw [wrChain_nonstore hst]; exact List.mem_singleton_self _)
  unfold symBody at hs
  by_cases hl : isLoadK a.kind = true
  · rw [if_pos hl] at hs
    have hst := not_store_of_load hl
    by_cases hI : (match eaS a L with | .c v => imgOK C v (widthOfM a.kind) | _ => false) = true
    · -- load from the code image at a constant address
      rw [dif_pos hI] at hs
      obtain ⟨v, hE⟩ : ∃ v, eaS a L = .c v := by
        revert hI; cases eaS a L <;> simp
      rw [hE] at hs hI hea
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl, rfl⟩ := hs
      · simp only [imgOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hI
        have hv : (eaddrM a (pinsOf (lineKs a) (regsDen ρ L))).toNat = v.toNat := by
          rw [hea]; rfl
        refine swpx_line img rT hc a (lineKs a)
          [bytesAt img (eaddrM a (pinsOf (lineKs a) (regsDen ρ L))).toNat (widthOfM a.kind)]
          [] [] hok.wf hok.keys hok.wr (fun b _ => by rw [hst]; trivial) hlive hok.pins hdec
          (fun m hT _ _ => memFacts_loadF hl (by rw [hv]; exact hI.1) (fun b hb => by
            rw [hv] at hb
            obtain ⟨h1, h2⟩ := of_mem_accAddrs hb
            have hr := hI.2 (b - v.toNat) (List.mem_range.2 (by omega))
            rw [show v.toNat + (b - v.toNat) = b by omega, hCr] at hr
            rw [hc m hT b hr]; rfl))
          hPC hok.regs hok.nogp hgprs (fun _ h => by cases h) (fun _ h => by cases h) (hRo _ hst) ?_
        rw [lineR_nonstore hst, wvalM_load hl, hst, hv, ← hCi]
        exact hk
    rw [dif_neg hI] at hs
    by_cases hdsp : decide ((base (eaS a L)).1 ∈ C.dbase) = true
    · -- load from the data view
      rw [if_pos hdsp] at hs; cases hs
      have hob0 := hob _ List.mem_cons_self
      simp only [SOb.den] at hob0
      rw [← hea] at hob0
      refine swpx_line img rT hc a (lineKs a)
        [bytesAt (imgM ρ.D0) (eaddrM a (pinsOf (lineKs a) (regsDen ρ L))).toNat (widthOfM a.kind)]
        [] [] hok.wf hok.keys hok.wr (fun b _ => by rw [hst]; trivial) hlive hok.pins hdec
        (fun m _ hDm _ => memFacts_load hl hob0.1 (fun b hb => dataReads_view hDm b (hob0.2 b hb)))
        hPC hok.regs hok.nogp hgprs (fun _ h => by cases h) (fun _ h => by cases h) (hRo _ hst) ?_
      rw [lineR_nonstore hst, wvalM_load hl, hst, hea]
      show SWP _ _ _ _ _ _ (upd _ _ (ldv a.kind ρ.D0 ((eaS a L).den ρ).toNat)) (writeLog (memDen ρ M) [])
      have hval : ((kvFind C.kv a.kind (eaS a L)).elim (.ldD a.kind (eaS a L)) SE.c).den ρ =
          ldv a.kind ρ.D0 ((eaS a L).den ρ).toNat := by
        cases hf : kvFind C.kv a.kind (eaS a L) with
        | none => rfl
        | some v =>
          unfold kvFind at hf
          obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.1 hf
          have hp := List.find?_some he
          simp only [decide_eq_true_eq] at hp
          have := hkv e (List.mem_of_find?_eq_some he)
          rw [hp.1, hp.2] at this
          exact this.symm
      rw [← hval]
      exact hk
    · -- load from the owned memory, with store forwarding
      rw [if_neg hdsp] at hs
      cases hsl : symLoad a.kind (eaS a L) M with
      | none => rw [hsl] at hs; cases hs
      | some p =>
        rw [hsl] at hs; cases hs
        have hob0 := hob _ List.mem_cons_self
        simp only [SOb.den] at hob0
        rw [← hea] at hob0
        refine swpx_line img rT hc a (lineKs a)
          [bytesAt (imgM (memDen ρ M)) (eaddrM a (pinsOf (lineKs a) (regsDen ρ L))).toNat
            (widthOfM a.kind)]
          (accAddrs (eaddrM a (pinsOf (lineKs a) (regsDen ρ L))).toNat (widthOfM a.kind)) []
          hok.wf hok.keys hok.wr (fun b _ => by rw [hst]; trivial) hlive hok.pins hdec
          (fun m _ _ hp => memFacts_load hl hob0.1 hp) hPC hok.regs hok.nogp hgprs hob0.2
          (fun _ h => by cases h) (hRo _ hst) ?_
        rw [lineR_nonstore hst, wvalM_load hl, hst]
        have hv := symLoad_sound ρ S DA a.kind (eaS a L) M p.1 p.2 hsl
          (fun o ho => hob o (List.mem_cons_of_mem _ ho))
        rw [hea]
        show SWP _ _ _ _ _ _ (upd _ _ (ldv a.kind (memDen ρ M) ((eaS a L).den ρ).toNat))
          (writeLog (memDen ρ M) [])
        rw [← hv]
        exact hk
  · rw [if_neg hl] at hs
    have hl' : isLoadK a.kind = false := by simpa using hl
    by_cases hsto : isStoreK a.kind = true
    · -- store family
      rw [if_pos hsto] at hs; cases hs
      have hob0 := hob _ List.mem_cons_self
      simp only [SOb.den] at hob0
      rw [← hea] at hob0
      have hw : wentryM a (pinsOf (lineKs a) (regsDen ρ L)) =
          (((eaS a L).den ρ).toNat, widthOfM a.kind, (rdS L a.rs2).den ρ) := by
        unfold wentryM; rw [hea, rdS_den, srcVal_pins h2]
      refine swpx_line img rT hc a (lineKs a) [] []
        (accAddrs (eaddrM a (pinsOf (lineKs a) (regsDen ρ L))).toNat (widthOfM a.kind))
        hok.wf hok.keys hok.wr ?_ hlive hok.pins hdec
        (fun m _ _ _ => memFacts_store hsto hob0.1) hPC hok.regs hok.nogp hgprs
        (fun _ h => by cases h) hob0.2 (fun _ _ _ _ => by unfold lineR; rw [hsto]; rfl) ?_
      · intro b hb
        rw [hsto]
        unfold wentryM
        exact outL_single _ hb
      · unfold lineR; rw [hsto]
        simp only [ite_true]
        rw [hw]
        exact hk
    · -- register-only family
      have hst : isStoreK a.kind = false := by simpa using hsto
      rw [if_neg hsto] at hs
      have hval : ∀ e : SE, ((a.rd, e) :: L, M, ([] : List SOb)) = (L', M', obs) →
          wvalM a (pinsOf (lineKs a) (regsDen ρ L)) [] = e.den ρ →
          SWP live (T ++ dataOf ρ.D0 DA) rs S Q a.pc (regsDen ρ L) (memDen ρ M) := by
        intro e he hv
        cases he
        refine swpx_line img rT hc a (lineKs a) [] [] [] hok.wf hok.keys hok.wr
          (fun b _ => by rw [hst]; trivial) hlive hok.pins hdec ?_ hPC hok.regs hok.nogp hgprs
          (fun _ h => by cases h) (fun _ h => by cases h) (hRo _ hst) ?_
        · intro m _ _ _
          unfold MemFacts; revert hl' hst; cases a.kind <;> intro hl' hst <;>
            first | trivial | (cases hl'; done) | (cases hst; done)
        · rw [lineR_nonstore hst, hst]
          show SWP _ _ _ _ _ _ (upd _ _ (wvalM a (pinsOf (lineKs a) (regsDen ρ L)) [])) _
          rw [hv]; exact hk
      have hsrc : ∀ r, (r = 0 ∨ r ∈ lineKs a) →
          srcVal r (pinsOf (lineKs a) (regsDen ρ L)) = (rdS L r).den ρ := fun r hr => by
        rw [rdS_den, srcVal_pins hr]
      split at hs
      · rename_i hk'
        cases hs
        refine hval _ rfl ?_
        unfold wvalM; rw [hk']
        rw [← eaddrM_eq ρ h1]; rfl
      · rename_i hk'
        cases hs
        refine hval _ rfl ?_
        unfold wvalM; rw [hk']
        rw [addS_den, hsrc _ h1, hsrc _ h2]
      · rename_i hk'
        cases hs
        refine hval _ rfl ?_
        unfold wvalM; rw [hk']
        rw [subS_den, hsrc _ h1, hsrc _ h2]
      · cases hs
        refine hval _ rfl ?_
        rw [wvalM_alu hl', hsrc _ h1, hsrc _ h2]
        split
        · rename_i x y hx hy; rw [hx, hy]; rfl
        · rfl

end body


/-! ## Terminators -/

def brOp (f3 : Nat) : Option bop :=
  if f3 = 0 then some .BEQ else if f3 = 1 then some .BNE else if f3 = 4 then some .BLT
  else if f3 = 5 then some .BGE else if f3 = 6 then some .BLTU else if f3 = 7 then some .BGEU
  else none

/-- Conditional branch fields: `(op, rs1, rs2, imm13)`. -/
def decB (w : BitVec 32) : Option (bop × Nat × Nat × BitVec 13) :=
  if (w.extractLsb' 0 7).toNat = 0x63 then
    (brOp (w.extractLsb' 12 3).toNat).map fun op =>
      (op, (w.extractLsb' 15 5).toNat, (w.extractLsb' 20 5).toNat,
        (((w.extractLsb' 31 1).append (w.extractLsb' 7 1)).append (w.extractLsb' 25 6)).append
          ((w.extractLsb' 8 4).append (0#1)))
  else none

/-- `jal x0, imm21` (a `j`). -/
def decJ (w : BitVec 32) : Option (BitVec 21) :=
  if (w.extractLsb' 0 7).toNat = 0x6f ∧ (w.extractLsb' 7 5).toNat = 0 then
    some ((((w.extractLsb' 31 1).append (w.extractLsb' 12 8)).append (w.extractLsb' 20 1)).append
      ((w.extractLsb' 21 10).append (0#1)))
  else none

def mkT (pc : BitVec 64) (w : BitVec 32) (k : TKind) (rs1 rs2 : Nat) (i13 : BitVec 13)
    (i21 : BitVec 21) : TInstr :=
  ⟨pc, w, w.extractLsb' 0 8, w.extractLsb' 8 8, w.extractLsb' 16 8, w.extractLsb' 24 8,
    k, rs1, rs2, i13, i21, 0⟩

/-- Decidable side conditions of `swpx_br` for both outcomes. -/
structure BrOK (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat)
    (t f : TInstr) (ks : List Nat) : Prop where
  wft : ChainOK t.pc ks [⟨[], some t⟩]
  wff : ChainOK f.pc ks [⟨[], some f⟩]
  keys : KeysOK ks
  pins : Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3
  regs : ∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC)

def brChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (t f : TInstr)
    (ks : List Nat) : Bool :=
  decide (ChainOK t.pc ks [⟨[], some t⟩]) && decide (ChainOK f.pc ks [⟨[], some f⟩]) &&
  decide (KeysOK ks) && decide (Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3) &&
  decide (∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))

theorem BrOK.of_chk {img rT rs t f ks} (h : brChk img rT rs t f ks = true) :
    BrOK img rT rs t f ks := by
  simp only [brChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  exact ⟨h1, h2, h3, h4, h5⟩

def jChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (t : TInstr) : Bool :=
  decide (ChainOK t.pc [] [⟨[], some t⟩]) && decide (Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3)

/-! ## The executor -/

structure SS where
  pc : BitVec 64
  regs : List (Nat × SE)
  mem : SMem
  obs : List SOb

inductive Tree where
  | leaf (s : SS)
  | br (pc : BitVec 64) (op : bop) (a b : SE) (t f : Tree)
  | jr (s : SS) (tgt : SE)

inductive StepR where
  | next (s : SS)
  | br (op : bop) (a b : SE) (t f : SS)
  | jr (s : SS) (tgt : SE)
  | stop


/-- A branch whose operands are both constants is decided during execution. -/
def brNext (op : bop) (x y : SE) (t f : SS) : StepR :=
  match x, y with
  | .c u, .c v => .next (if guardB op u v then t else f)
  | _, _ => .br op x y t f

theorem brNext_next {op : bop} {x y : SE} {t f s' : SS} (ρ : Env) (h : brNext op x y t f = .next s') :
    s' = (if guardB op (x.den ρ) (y.den ρ) then t else f) := by
  unfold brNext at h
  split at h
  · cases h; rfl
  · cases h

theorem brNext_br {op op' : bop} {x y a b : SE} {t f t' f' : SS}
    (h : brNext op x y t f = .br op' a b t' f') : op' = op ∧ a = x ∧ b = y ∧ t' = t ∧ f' = f := by
  unfold brNext at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- `jalr x0, 0(rs1)`. -/
def decJR (w : BitVec 32) : Option Nat :=
  if (w.extractLsb' 0 7).toNat = 0x67 ∧ (w.extractLsb' 7 5).toNat = 0 ∧
      (w.extractLsb' 12 3).toNat = 0 ∧ (w.extractLsb' 20 12).toNat = 0 then
    some (w.extractLsb' 15 5).toNat
  else none

def jrChk (img : Nat → BitVec 8) (rT : List (Nat × Nat)) (rs : List Nat) (t : TInstr)
    (ks : List Nat) : Bool :=
  decide (ChainOK t.pc ks [⟨[], some t⟩]) && decide (KeysOK ks) &&
  decide (Pins4OK img rT t.pc.toNat t.b0 t.b1 t.b2 t.b3) &&
  decide (∀ x ∈ ks, x = gp ∨ (x ∈ rs ∧ x ≠ VsaIris.PC))

/-- An indirect jump: a constant target continues the run, a symbolic one ends it. -/
def jrStep (C : Cfg) (s : SS) (w : BitVec 32) : StepR :=
  match decJR w with
  | some r1 =>
    if jrChk C.img C.rT C.rs (mkT s.pc w .jr r1 0 0 0) (nzd [r1]) then
      match rdS s.regs r1 with
      | .c v => .next ⟨v, s.regs, s.mem, .al4 (.c v) :: .decT (mkT s.pc w .jr r1 0 0 0) :: s.obs⟩
      | x => .jr ⟨s.pc, s.regs, s.mem, .al4 x :: .decT (mkT s.pc w .jr r1 0 0 0) :: s.obs⟩ x
    else .stop
  | none => .stop

theorem jrStep_cases {C : Cfg} {s : SS} {w : BitVec 32} {r : StepR} (h : jrStep C s w = r) :
    r = .stop ∨ ∃ r1, decJR w = some r1 ∧
      jrChk C.img C.rT C.rs (mkT s.pc w .jr r1 0 0 0) (nzd [r1]) = true ∧
      ((∃ v, rdS s.regs r1 = .c v ∧ r = .next ⟨v, s.regs, s.mem,
          .al4 (.c v) :: .decT (mkT s.pc w .jr r1 0 0 0) :: s.obs⟩) ∨
       r = .jr ⟨s.pc, s.regs, s.mem,
          .al4 (rdS s.regs r1) :: .decT (mkT s.pc w .jr r1 0 0 0) :: s.obs⟩ (rdS s.regs r1)) := by
  unfold jrStep at h
  split at h
  · rename_i r1 hd
    split at h
    · rename_i hc
      refine .inr ⟨r1, hd, hc, ?_⟩
      split at h
      · rename_i v hv; exact .inl ⟨v, hv, h.symm⟩
      · rename_i x hx; rw [← h]; exact .inr rfl
    · exact .inl h.symm
  · exact .inl h.symm

def symStep (C : Cfg) (s : SS) : StepR :=
  let w := wordAt C.img s.pc.toNat
  if (decodeM w).isSome then
    let a := mkLine s.pc w
    match symBody C a s.regs s.mem with
    | some (L', M', o) =>
      if lineChk C.img C.rT C.rs a then
        .next ⟨BitVec.addInt s.pc 4, L', M', o ++ .decM s.pc w :: s.obs⟩
      else .stop
    | none => .stop
  else
    match decB w with
    | some (op, r1, r2, i13) =>
      let t := mkT s.pc w (.br op true) r1 r2 i13 0
      let f := mkT s.pc w (.br op false) r1 r2 i13 0
      if brChk C.img C.rT C.rs t f (nzd [r1, r2]) then
        brNext op (rdS s.regs r1) (rdS s.regs r2)
          ⟨tgtPC0 t, s.regs, s.mem, .decT t :: s.obs⟩ ⟨tgtPC0 f, s.regs, s.mem, .decT t :: s.obs⟩
      else .stop
    | none =>
      match decJ w with
      | some i21 =>
        let t := mkT s.pc w .j 0 0 0 i21
        if jChk C.img C.rT t then .next ⟨tgtPC0 t, s.regs, s.mem, .decT t :: s.obs⟩ else .stop
      | none => jrStep C s w

def symRun (C : Cfg) : Nat → SS → Tree
  | 0, s => .leaf s
  | n + 1, s =>
    if s.pc ∈ C.stops then .leaf s else
    match symStep C s with
    | .next s' => symRun C n s'
    | .br op a b t f => .br s.pc op a b (symRun C n t) (symRun C n f)
    | .jr s' x => .jr s' x
    | .stop => .leaf s

/-- The residual weakest precondition: each live leaf's obligations and continuation. -/
def Tree.WP (ρ : Env) (S : Nat → Prop) (DA : List Nat)
    (K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop) : Tree → Prop
  | .leaf s => ObsOK ρ S DA s.obs ∧ K s.pc (regsDen ρ s.regs) (memDen ρ s.mem)
  | .br _ op a b t f => (guardB op (a.den ρ) (b.den ρ) = true → t.WP ρ S DA K) ∧
      (guardB op (a.den ρ) (b.den ρ) = false → f.WP ρ S DA K)
  | .jr s x => ObsOK ρ S DA s.obs ∧ K (x.den ρ) (regsDen ρ s.regs) (memDen ρ s.mem)

/-! ## Soundness -/

theorem symStep_obs (C : Cfg) (s : SS) {s' : SS} (h : symStep C s = .next s') :
    ∀ o ∈ s.obs, o ∈ s'.obs := by
  intro o ho
  unfold symStep at h
  simp only at h
  split at h
  · split at h
    · split at h
      · cases h; simp [ho]
      · cases h
    · cases h
  · split at h
    · split at h
      · rw [brNext_next ⟨fun _ => 0, ∅, ∅⟩ h]
        split <;> exact List.mem_cons_of_mem _ ho
      · cases h
    · split at h
      · split at h
        · cases h; simp [ho]
        · cases h
      · rcases jrStep_cases h with h | ⟨r1, -, -, ⟨v, -, h⟩ | h⟩
        · cases h
        · cases h; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)
        · cases h

theorem symStep_br_obs (C : Cfg) (s : SS) {op a b t f}
    (h : symStep C s = .br op a b t f) : (∀ o ∈ s.obs, o ∈ t.obs) ∧ (∀ o ∈ s.obs, o ∈ f.obs) := by
  unfold symStep at h
  simp only at h
  split at h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    · split at h
      · obtain ⟨-, -, -, rfl, rfl⟩ := brNext_br h
        exact ⟨fun o ho => List.mem_cons_of_mem _ ho, fun o ho => List.mem_cons_of_mem _ ho⟩
      · cases h
    · split at h
      · split at h <;> cases h
      · rcases jrStep_cases h with h | ⟨r1, -, -, ⟨v, -, h⟩ | h⟩ <;> cases h

theorem symStep_jr_obs (C : Cfg) (s : SS) {s' : SS} {x : SE}
    (h : symStep C s = .jr s' x) : ∀ o ∈ s.obs, o ∈ s'.obs := by
  intro o ho
  unfold symStep at h
  simp only at h
  split at h
  · split at h
    · split at h <;> cases h
    · cases h
  · split at h
    · split at h
      · unfold brNext at h; split at h <;> cases h
      · cases h
    · split at h
      · split at h <;> cases h
      · rcases jrStep_cases h with h | ⟨r1, -, -, ⟨v, -, h⟩ | h⟩
        · cases h
        · cases h
        · cases h; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ ho)

theorem symRun_obs (C : Cfg) (ρ : Env) (S : Nat → Prop) (DA : List Nat) (K) :
    ∀ (n : Nat) (s : SS), (symRun C n s).WP ρ S DA K → ObsOK ρ S DA s.obs
  | 0, s, h => h.1
  | n + 1, s, h => by
    unfold symRun at h
    by_cases hs : s.pc ∈ C.stops
    · rw [if_pos hs] at h; exact h.1
    · rw [if_neg hs] at h
      cases hst : symStep C s with
      | stop => rw [hst] at h; exact h.1
      | next s' =>
        rw [hst] at h
        intro o ho
        exact symRun_obs C ρ S DA K n s' h o (symStep_obs C s hst o ho)
      | jr s' x =>
        rw [hst] at h
        intro o ho
        exact h.1 o (symStep_jr_obs C s hst o ho)
      | br op a b t f =>
        rw [hst] at h
        obtain ⟨ht, hf⟩ := symStep_br_obs C s hst
        intro o ho
        cases hc : guardB op (a.den ρ) (b.den ρ)
        · exact symRun_obs C ρ S DA K n f (h.2 hc) o (hf o ho)
        · exact symRun_obs C ρ S DA K n t (h.1 hc) o (ht o ho)

section run
variable {live : Nat → Prop} {T : List (Nat × BitVec 8)} {S : Nat → Prop} {Dt : Mem}
  {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- One conditional branch, outcome chosen by the guard on the symbolic operands. -/
theorem br_sound (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (ρ : Env) (s : SS)
    (op : bop) (r1 r2 : Nat) (i13 : BitVec 13)
    (hchk : brChk C.img C.rT C.rs (mkT s.pc (wordAt C.img s.pc.toNat) (.br op true) r1 r2 i13 0)
      (mkT s.pc (wordAt C.img s.pc.toNat) (.br op false) r1 r2 i13 0) (nzd [r1, r2]) = true)
    (hdec : DecT (mkT s.pc (wordAt C.img s.pc.toNat) (.br op true) r1 r2 i13 0))
    (hk : SWP live (T ++ dataOf Dt DA) C.rs S Q
      (if guardB op ((rdS s.regs r1).den ρ) ((rdS s.regs r2).den ρ) then
        tgtPC0 (mkT s.pc (wordAt C.img s.pc.toNat) (.br op true) r1 r2 i13 0)
      else tgtPC0 (mkT s.pc (wordAt C.img s.pc.toNat) (.br op false) r1 r2 i13 0))
      (regsDen ρ s.regs) (memDen ρ s.mem)) :
    SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem) := by
  have hok := BrOK.of_chk hchk
  have h1 : r1 = 0 ∨ r1 ∈ nzd [r1, r2] := mem_nzd (by simp)
  have h2 : r2 = 0 ∨ r2 ∈ nzd [r1, r2] := mem_nzd (by simp)
  cases hg : guardB op ((rdS s.regs r1).den ρ) ((rdS s.regs r2).den ρ)
  · rw [hg] at hk
    refine swpx_br C.img C.rT hc
      (mkT s.pc (wordAt C.img s.pc.toNat) (.br op false) r1 r2 i13 0) op false rfl
      (nzd [r1, r2]) hok.wff hok.keys hlive hok.pins hdec ?_ hPC hok.regs hgprs hk
    show guardB op (srcVal r1 _) (srcVal r2 _) = false
    rw [srcVal_pins h1, srcVal_pins h2, ← rdS_den, ← rdS_den]; exact hg
  · rw [hg] at hk
    refine swpx_br C.img C.rT hc
      (mkT s.pc (wordAt C.img s.pc.toNat) (.br op true) r1 r2 i13 0) op true rfl
      (nzd [r1, r2]) hok.wft hok.keys hlive hok.pins hdec ?_ hPC hok.regs hgprs hk
    show guardB op (srcVal r1 _) (srcVal r2 _) = true
    rw [srcVal_pins h1, srcVal_pins h2, ← rdS_den, ← rdS_den]; exact hg

theorem jr_sound (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (ρ : Env) (s : SS) (w : BitVec 32) (r1 : Nat)
    (hchk : jrChk C.img C.rT C.rs (mkT s.pc w .jr r1 0 0 0) (nzd [r1]) = true)
    (hdec : DecT (mkT s.pc w .jr r1 0 0 0))
    (hal : ((rdS s.regs r1).den ρ).toNat % 4 = 0)
    (hk : SWP live (T ++ dataOf Dt DA) C.rs S Q ((rdS s.regs r1).den ρ)
      (regsDen ρ s.regs) (memDen ρ s.mem)) :
    SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem) := by
  simp only [jrChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨hwf, hkeys⟩, hpins⟩, hregs⟩ := hchk
  have h1 : r1 = 0 ∨ r1 ∈ nzd [r1] := mem_nzd (by simp)
  have hsv : srcVal r1 (pinsOf (nzd [r1]) (regsDen ρ s.regs)) = (rdS s.regs r1).den ρ := by
    rw [rdS_den, srcVal_pins h1]
  exact swpx_jr C.img C.rT hc (mkT s.pc w .jr r1 0 0 0) rfl rfl (nzd [r1]) hwf hkeys hlive hpins
    hdec hPC hregs hgprs (by show (srcVal r1 _).toNat % 4 = 0; rw [hsv]; exact hal)
    (by show SWP _ _ _ _ _ (srcVal r1 _) _ _; rw [hsv]; exact hk)

theorem symStep_sound (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (ρ : Env) (hD : ρ.D0 = Dt)
    (hkv : ∀ e ∈ C.kv, ldv e.1 ρ.D0 (e.2.1.den ρ).toNat = e.2.2) (s : SS) :
    (∀ s', symStep C s = .next s' → ObsOK ρ S DA s'.obs →
      SWP live (T ++ dataOf Dt DA) C.rs S Q s'.pc (regsDen ρ s'.regs) (memDen ρ s'.mem) →
      SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem)) ∧
    (∀ op a b t f, symStep C s = .br op a b t f →
      (guardB op (a.den ρ) (b.den ρ) = true → ObsOK ρ S DA t.obs ∧
        SWP live (T ++ dataOf Dt DA) C.rs S Q t.pc (regsDen ρ t.regs) (memDen ρ t.mem)) →
      (guardB op (a.den ρ) (b.den ρ) = false → ObsOK ρ S DA f.obs ∧
        SWP live (T ++ dataOf Dt DA) C.rs S Q f.pc (regsDen ρ f.regs) (memDen ρ f.mem)) →
      SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem)) ∧
    (∀ s' x, symStep C s = .jr s' x → ObsOK ρ S DA s'.obs →
      SWP live (T ++ dataOf Dt DA) C.rs S Q (x.den ρ) (regsDen ρ s'.regs) (memDen ρ s'.mem) →
      SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem)) := by
  refine ⟨fun s' h hob hk => ?_, fun op a b t f h ht hf => ?_, fun s' x h hob hk => ?_⟩
  · unfold symStep at h
    simp only at h
    split at h
    · split at h
      · rename_i L' M' o hsb
        split at h
        · rename_i hchk
          cases h
          have hp := (mkLine_fields s.pc (wordAt C.img s.pc.toNat)).1
          have hb := body_sound (Q := Q) C.img C.rT hc hlive hPC hgprs ρ hD C rfl rfl hkv _ s.regs L' s.mem M' o
            hsb (LineOK.of_chk hchk)
            (hob _ (List.mem_append_right _ List.mem_cons_self))
            (fun x hx => hob x (List.mem_append_left _ hx))
          rw [hp] at hb
          exact hb hk
        · cases h
      · cases h
    · split at h
      · rename_i op' r1 r2 i13 _
        split at h
        · rename_i hchk
          have e := brNext_next ρ h
          refine br_sound C hc hlive hPC hgprs ρ s op' r1 r2 i13 hchk ?_ ?_
          · subst e; split at hob <;> exact hob _ List.mem_cons_self
          · subst e; split at hk <;> rename_i hg <;> simp only [hg] <;> exact hk
        · cases h
      · split at h
        · rename_i i21 _
          split at h
          · rename_i hchk
            cases h
            simp only [jChk, Bool.and_eq_true, decide_eq_true_eq] at hchk
            exact swpx_j C.img C.rT hc (mkT s.pc (wordAt C.img s.pc.toNat) .j 0 0 0 i21) rfl
              hchk.1 hlive hchk.2 (hob _ List.mem_cons_self) hPC hgprs hk
          · cases h
        · rcases jrStep_cases h with h | ⟨r1, -, hchk, ⟨v, hv, h⟩ | h⟩
          · cases h
          · cases h
            refine jr_sound C hc hlive hPC hgprs ρ s _ r1 hchk (hob _ (List.mem_cons_of_mem _
              List.mem_cons_self)) ?_ ?_
            · rw [hv]; exact hob _ List.mem_cons_self
            · rw [hv]; exact hk
          · cases h
  · unfold symStep at h
    simp only at h
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · split at h
      · rename_i op' r1 r2 i13 _
        split at h
        · rename_i hchk
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := brNext_br h
          refine br_sound C hc hlive hPC hgprs ρ s op r1 r2 i13 hchk ?_ ?_
          · cases hg : guardB op ((rdS s.regs r1).den ρ) ((rdS s.regs r2).den ρ)
            · exact (hf hg).1 _ List.mem_cons_self
            · exact (ht hg).1 _ List.mem_cons_self
          · cases hg : guardB op ((rdS s.regs r1).den ρ) ((rdS s.regs r2).den ρ)
            · exact (hf hg).2
            · exact (ht hg).2
        · cases h
      · split at h
        · split at h <;> cases h
        · rcases jrStep_cases h with h | ⟨r1, -, -, ⟨v, -, h⟩ | h⟩ <;> cases h
  · unfold symStep at h
    simp only at h
    split at h
    · split at h
      · split at h <;> cases h
      · cases h
    · split at h
      · split at h
        · unfold brNext at h; split at h <;> cases h
        · cases h
      · split at h
        · split at h <;> cases h
        · rcases jrStep_cases h with h | ⟨r1, -, hchk, ⟨v, -, h⟩ | h⟩
          · cases h
          · cases h
          · cases h
            exact jr_sound C hc hlive hPC hgprs ρ s _ r1 hchk
              (hob _ (List.mem_cons_of_mem _ List.mem_cons_self)) (hob _ List.mem_cons_self) hk

/-- **Soundness of the executor against the real `SWP`.** -/
theorem symRun_swp (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (ρ : Env) (hD : ρ.D0 = Dt)
    (hkv : ∀ e ∈ C.kv, ldv e.1 ρ.D0 (e.2.1.den ρ).toNat = e.2.2) :
    ∀ (n : Nat) (s : SS),
      (symRun C n s).WP ρ S DA (fun pc R M => SWP live (T ++ dataOf Dt DA) C.rs S Q pc R M) →
      SWP live (T ++ dataOf Dt DA) C.rs S Q s.pc (regsDen ρ s.regs) (memDen ρ s.mem)
  | 0, s, h => h.2
  | n + 1, s, h => by
    have hsnd := symStep_sound (S := S) (DA := DA) (Q := Q) C hc hlive hPC hgprs ρ hD hkv s
    unfold symRun at h
    by_cases hs : s.pc ∈ C.stops
    · rw [if_pos hs] at h; exact h.2
    · rw [if_neg hs] at h
      cases hst : symStep C s with
      | stop => rw [hst] at h; exact h.2
      | next s' =>
        rw [hst] at h
        exact hsnd.1 s' hst (symRun_obs C ρ S DA _ n s' h)
          (symRun_swp C hc hlive hPC hgprs ρ hD hkv n s' h)
      | jr s' x =>
        rw [hst] at h
        exact hsnd.2.2 s' x hst h.1 h.2
      | br op a b t f =>
        rw [hst] at h
        exact hsnd.2.1 op a b t f hst
          (fun hg => ⟨symRun_obs C ρ S DA _ n t (h.1 hg),
            symRun_swp C hc hlive hPC hgprs ρ hD hkv n t (h.1 hg)⟩)
          (fun hg => ⟨symRun_obs C ρ S DA _ n f (h.2 hg),
            symRun_swp C hc hlive hPC hgprs ρ hD hkv n f (h.2 hg)⟩)

/-- Entry form: the empty symbolic state denotes `R`/`Mt` exactly. -/
theorem regsDen_of_known {ρ : Env} :
    ∀ L : List (Nat × SE), (∀ p ∈ L, ρ.R0 p.1 = p.2.den ρ) → regsDen ρ L = ρ.R0
  | [], _ => rfl
  | (k, e) :: L, h => by
    show upd (regsDen ρ L) k (e.den ρ) = ρ.R0
    rw [regsDen_of_known L (fun p hp => h p (List.mem_cons_of_mem _ hp))]
    exact upd_self_eq (h (k, e) List.mem_cons_self)

/-- Entry form: the entry symbolic state (known register values `L0`) denotes `R`/`Mt`. -/
theorem symRun_entry (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (n : Nat) (pc : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (L0 : List (Nat × SE))
    (hL0 : ∀ p ∈ L0, R p.1 = p.2.den ⟨R, Mt, Dt⟩)
    (hkv : ∀ e ∈ C.kv, ldv e.1 Dt (e.2.1.den ⟨R, Mt, Dt⟩).toNat = e.2.2)
    (h : (symRun C n ⟨pc, L0, [], []⟩).WP ⟨R, Mt, Dt⟩ S DA
      (fun pc R M => SWP live (T ++ dataOf Dt DA) C.rs S Q pc R M)) :
    SWP live (T ++ dataOf Dt DA) C.rs S Q pc R Mt := by
  have := symRun_swp C hc hlive hPC hgprs ⟨R, Mt, Dt⟩ rfl hkv n ⟨pc, L0, [], []⟩ h
  rwa [regsDen_of_known L0 hL0] at this

end run

/-! ## Reflective obligation checker

Every address `SE` normalises to `atom + off`. A `Geom` records, per atom, an interval of its
value, an alignment modulus and the (atom-relative) ranges covered by `S` and by the data view
`DA`. `obCheck` decides an obligation from these facts with wrap-aware arithmetic; the run's
obligations are then filtered by one kernel evaluation (`Tree.prune`). -/

/-- Facts about one address atom `A = atom.den`: `lo ≤ A ≤ hi`, `A % amod = 0`, every byte
`A + j` with `(l, h) ∈ sc`, `l ≤ j < h` satisfies `S` (resp. `∈ DA` for `dc`), and, when
`gap = some (g₁, g₂)`, the object avoids the HTIF window: `A + g₁ ≤ tohost ∨ tohost + g₂ ≤ A`. -/
structure AFact where
  atom : SE
  lo : Nat
  hi : Nat
  amod : Nat
  sc : List (Nat × Nat)
  dc : List (Nat × Nat)
  gap : Option (Nat × Nat) := none
  shift : BitVec 64 := 0#64

/-- The facts are about `A = (atom + shift).toNat`; offsets are relative to that point. -/
def AFact.holds (ρ : Env) (S : Nat → Prop) (DA : List Nat) (f : AFact) : Prop :=
  f.lo ≤ (f.atom.den ρ + f.shift).toNat ∧ (f.atom.den ρ + f.shift).toNat ≤ f.hi ∧
  (f.atom.den ρ + f.shift).toNat % f.amod = 0 ∧
  (∀ r ∈ f.sc, ∀ b, (f.atom.den ρ + f.shift).toNat + r.1 ≤ b →
    b < (f.atom.den ρ + f.shift).toNat + r.2 → S b) ∧
  (∀ r ∈ f.dc, ∀ b, (f.atom.den ρ + f.shift).toNat + r.1 ≤ b →
    b < (f.atom.den ρ + f.shift).toNat + r.2 → b ∈ DA) ∧
  (∀ g, f.gap = some g → (f.atom.den ρ + f.shift).toNat + g.1 ≤ tohostAddr ∨
    tohostAddr + g.2 ≤ (f.atom.den ρ + f.shift).toNat)

abbrev Geom := List AFact

def Geom.holds (ρ : Env) (S : Nat → Prop) (DA : List Nat) (Γ : Geom) : Prop :=
  ∀ f ∈ Γ, f.holds ρ S DA

/-- The constant base: `A = 0`. -/
def constFact : AFact := ⟨.c 0, 0, 0, 0, [], [], none, 0⟩

def findF (Γ : Geom) (a : SE) : Option AFact :=
  if a = .c 0 then some constFact else Γ.find? (fun f => decide (f.atom = a))

theorem findF_sound {ρ : Env} {S : Nat → Prop} {DA : List Nat} {Γ : Geom} (hΓ : Γ.holds ρ S DA)
    {a : SE} {f : AFact} (h : findF Γ a = some f) : f.atom = a ∧ f.holds ρ S DA := by
  unfold findF at h
  split at h
  · rename_i ha; cases h; subst ha
    refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [constFact, SE.den]
  · have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    exact ⟨hp, hΓ f hm⟩

/-- Interval address of `e`: its atom's fact and the constant offset, when adding the offset
cannot wrap. -/
def addrOf (Γ : Geom) (e : SE) : Option (AFact × Nat) :=
  match findF Γ (base e).1 with
  | some f => if f.hi + ((base e).2 - f.shift).toNat < 2 ^ 64 then
      some (f, ((base e).2 - f.shift).toNat) else none
  | none => none

theorem addrOf_sound {ρ : Env} {S : Nat → Prop} {DA : List Nat} {Γ : Geom} (hΓ : Γ.holds ρ S DA)
    {e : SE} {f : AFact} {o : Nat} (h : addrOf Γ e = some (f, o)) :
    f.holds ρ S DA ∧ (e.den ρ).toNat = (f.atom.den ρ + f.shift).toNat + o := by
  unfold addrOf at h
  split at h
  · rename_i f' hf
    split at h
    · rename_i hw
      cases h
      obtain ⟨ha, hh⟩ := findF_sound hΓ hf
      refine ⟨hh, ?_⟩
      have e1 : (base e).1.den ρ + (base e).2 = (f.atom.den ρ + f.shift) + ((base e).2 - f.shift) := by
        rw [ha, BitVec.add_assoc, BitVec.add_comm f.shift, BitVec.sub_add_cancel]
      rw [base_den ρ e, e1, BitVec.toNat_add]
      have := hh.2.1
      exact Nat.mod_eq_of_lt (by omega)
    · cases h
  · cases h

def gapB (g : Option (Nat × Nat)) (o w : Nat) : Bool :=
  match g with
  | some g => decide (o + w ≤ g.1 ∧ 8 ≤ g.2 + o)
  | none => false

def ldOKb (l h w : Nat) (g : Option (Nat × Nat)) (o : Nat) : Bool :=
  decide (0x80000000 ≤ l ∧ h + w ≤ 0x100000000) &&
    (decide (h + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ l) || gapB g o w)

def stOKb (l h w : Nat) : Bool :=
  decide (0x80000000 ≤ l ∧ h + w ≤ 0x100000000 ∧ tohostAddr + 16 ≤ l)

def covB (rs : List (Nat × Nat)) (o w : Nat) : Bool := rs.any fun r => decide (r.1 ≤ o ∧ o + w ≤ r.2)

def obCheck (Γ : Geom) : SOb → Bool
  | .ld e w => match addrOf Γ e with
    | some (f, o) => ldOKb (f.lo + o) (f.hi + o) w f.gap o && covB f.sc o w
    | none => false
  | .ldD e w => match addrOf Γ e with
    | some (f, o) => ldOKb (f.lo + o) (f.hi + o) w f.gap o && covB f.dc o w
    | none => false
  | .st e w => match addrOf Γ e with
    | some (f, o) => stOKb (f.lo + o) (f.hi + o) w && decide (0 < w) && decide (f.amod % w = 0) &&
        decide (o % w = 0) && covB f.sc o w
    | none => false
  | .disj a wa b wb => match addrOf Γ a, addrOf Γ b with
    | some (f, o), some (g, p) =>
      decide (f.hi + o + wa ≤ g.lo + p) || decide (g.hi + p + wb ≤ f.lo + o)
    | _, _ => false
  | .al4 e => match addrOf Γ e with
    | some (f, o) => decide (f.amod % 4 = 0) && decide (o % 4 = 0)
    | none => false
  | _ => false

theorem covB_sound {rs : List (Nat × Nat)} {o w : Nat} {A : Nat} {P : Nat → Prop}
    (hr : ∀ r ∈ rs, ∀ b, A + r.1 ≤ b → b < A + r.2 → P b) (h : covB rs o w = true) :
    ∀ b ∈ accAddrs (A + o) w, P b := by
  intro b hb
  obtain ⟨h1, h2⟩ := of_mem_accAddrs hb
  obtain ⟨r, hr', hc⟩ := List.any_eq_true.1 h
  simp only [decide_eq_true_eq] at hc
  exact hr r hr' b (by omega) (by omega)

theorem ldGap {A lo hi o w : Nat} {g : Option (Nat × Nat)} (hl : lo ≤ A) (hh : A ≤ hi)
    (hg : ∀ g', g = some g' → A + g'.1 ≤ tohostAddr ∨ tohostAddr + g'.2 ≤ A)
    (h : (hi + o + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ lo + o) ∨ gapB g o w = true) :
    A + o + w ≤ tohostAddr ∨ tohostAddr + 8 ≤ A + o := by
  rcases h with h | h
  · omega
  · unfold gapB at h
    split at h
    · rename_i g'
      simp only [decide_eq_true_eq] at h
      have := hg g' rfl
      omega
    · cases h

theorem obCheck_sound {ρ : Env} {S : Nat → Prop} {DA : List Nat} {Γ : Geom} (hΓ : Γ.holds ρ S DA)
    (o : SOb) (h : obCheck Γ o = true) : o.den ρ S DA := by
  cases o with
  | ld e w =>
    simp only [obCheck] at h
    split at h
    · rename_i f off ha
      obtain ⟨hf, hx⟩ := addrOf_sound hΓ ha
      simp only [ldOKb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨hl, hh, -, hs, -, hg⟩ := hf
      refine ⟨?_, ?_⟩
      · rw [hx]; exact ⟨by omega, by omega, ldGap hl hh hg h3⟩
      · rw [hx]; exact covB_sound hs h4
    · cases h
  | ldD e w =>
    simp only [obCheck] at h
    split at h
    · rename_i f off ha
      obtain ⟨hf, hx⟩ := addrOf_sound hΓ ha
      simp only [ldOKb, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      obtain ⟨hl, hh, -, -, hd, hg⟩ := hf
      refine ⟨?_, ?_⟩
      · rw [hx]; exact ⟨by omega, by omega, ldGap hl hh hg h3⟩
      · rw [hx]; exact covB_sound hd h4
    · cases h
  | st e w =>
    simp only [obCheck] at h
    split at h
    · rename_i f off ha
      obtain ⟨hf, hx⟩ := addrOf_sound hΓ ha
      simp only [stOKb, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨h1, h2, h3⟩, h0⟩, hal⟩, hoff⟩, h4⟩ := h
      obtain ⟨hl, hh, hA, hs, -, -⟩ := hf
      refine ⟨?_, ?_⟩
      · rw [hx]
        refine ⟨by omega, by omega, by omega, ?_⟩
        have hwA : w ∣ (f.atom.den ρ + f.shift).toNat :=
          Nat.dvd_trans (Nat.dvd_of_mod_eq_zero hal) (Nat.dvd_of_mod_eq_zero hA)
        exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add hwA (Nat.dvd_of_mod_eq_zero hoff))
      · rw [hx]; exact covB_sound hs h4
    · cases h
  | disj a wa b wb =>
    simp only [obCheck] at h
    split at h
    · rename_i f off g p ha hb
      obtain ⟨hf, hx⟩ := addrOf_sound hΓ ha
      obtain ⟨hg, hy⟩ := addrOf_sound hΓ hb
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      show (a.den ρ).toNat + wa ≤ (b.den ρ).toNat ∨ (b.den ρ).toNat + wb ≤ (a.den ρ).toNat
      rw [hx, hy]
      have := hf.1; have := hf.2.1; have := hg.1; have := hg.2.1
      omega
    · cases h
  | al4 e =>
    simp only [obCheck] at h
    split at h
    · rename_i f off ha
      obtain ⟨hf, hx⟩ := addrOf_sound hΓ ha
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      show (e.den ρ).toNat % 4 = 0
      rw [hx]
      have h4A : 4 ∣ (f.atom.den ρ + f.shift).toNat :=
        Nat.dvd_trans (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_of_mod_eq_zero hf.2.2.1)
      exact Nat.mod_eq_zero_of_dvd (Nat.dvd_add h4A (Nat.dvd_of_mod_eq_zero h.2))
    · cases h
  | decM _ _ => cases h
  | decT _ => cases h

/-- Drop every obligation the checker decides. -/
def Tree.prune (Γ : Geom) : Tree → Tree
  | .leaf s => .leaf { s with obs := s.obs.filter fun o => !obCheck Γ o }
  | .br pc op a b t f => .br pc op a b (t.prune Γ) (f.prune Γ)
  | .jr s x => .jr { s with obs := s.obs.filter fun o => !obCheck Γ o } x

theorem Tree.WP_of_prune {ρ : Env} {S : Nat → Prop} {DA : List Nat} {Γ : Geom}
    (hΓ : Γ.holds ρ S DA) {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} :
    ∀ T : Tree, (T.prune Γ).WP ρ S DA K → T.WP ρ S DA K
  | .leaf s, h => by
    refine ⟨fun o ho => ?_, h.2⟩
    cases hc : obCheck Γ o
    · exact h.1 o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
    · exact obCheck_sound hΓ o hc
  | .br _ op a b t f, h => ⟨fun hg => Tree.WP_of_prune hΓ t (h.1 hg),
      fun hg => Tree.WP_of_prune hΓ f (h.2 hg)⟩
  | .jr s x, h => by
    refine ⟨fun o ho => ?_, h.2⟩
    cases hc : obCheck Γ o
    · exact h.1 o (List.mem_filter.2 ⟨ho, by simp [hc]⟩)
    · exact obCheck_sound hΓ o hc

section auto
variable {live : Nat → Prop} {T : List (Nat × BitVec 8)} {S : Nat → Prop} {Dt : Mem}
  {DA : List Nat} {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop}

/-- Entry form with the obligation checker: the residual is only the continuations plus the
obligations `obCheck` could not decide. -/
theorem symRun_auto (C : Cfg) (hc : CodeAt T C.img C.rT) (hlive : ∀ p ∈ T, live p.1)
    (hPC : VsaIris.PC ∈ C.rs) (hgprs : gp ∉ C.rs) (Γ : Geom) (n : Nat) (pc : BitVec 64)
    (R : Nat → BitVec 64) (Mt : Mem) (L0 : List (Nat × SE))
    (hL0 : ∀ p ∈ L0, R p.1 = p.2.den ⟨R, Mt, Dt⟩)
    (hkv : ∀ e ∈ C.kv, ldv e.1 Dt (e.2.1.den ⟨R, Mt, Dt⟩).toNat = e.2.2)
    (hΓ : Γ.holds ⟨R, Mt, Dt⟩ S DA)
    (h : ((symRun C n ⟨pc, L0, [], []⟩).prune Γ).WP ⟨R, Mt, Dt⟩ S DA
      (fun pc R M => SWP live (T ++ dataOf Dt DA) C.rs S Q pc R M)) :
    SWP live (T ++ dataOf Dt DA) C.rs S Q pc R Mt :=
  symRun_entry C hc hlive hPC hgprs n pc R Mt L0 hL0 hkv (Tree.WP_of_prune hΓ _ h)

end auto

/-! ## Driver: evaluate the run once, hand the kernel one conversion -/

deriving instance Lean.ToExpr for MKind
deriving instance Lean.ToExpr for MInstr
deriving instance Lean.ToExpr for bop
deriving instance Lean.ToExpr for TKind
deriving instance Lean.ToExpr for TInstr
deriving instance Lean.ToExpr for SE
deriving instance Lean.ToExpr for SOb
deriving instance Lean.ToExpr for SS
deriving instance Lean.ToExpr for Tree
deriving instance Lean.ToExpr for AFact

theorem Tree.WP_leaf {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {s : SS} (h1 : ObsOK ρ S DA s.obs)
    (h2 : K s.pc (regsDen ρ s.regs) (memDen ρ s.mem)) : (Tree.leaf s).WP ρ S DA K := ⟨h1, h2⟩

theorem Tree.WP_br {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {pc : BitVec 64} {op : bop} {a b : SE}
    {t f : Tree}
    (h1 : guardB op (a.den ρ) (b.den ρ) = true → t.WP ρ S DA K)
    (h2 : guardB op (a.den ρ) (b.den ρ) = false → f.WP ρ S DA K) :
    (Tree.br pc op a b t f).WP ρ S DA K := ⟨h1, h2⟩

theorem Tree.WP_jr {ρ : Env} {S : Nat → Prop} {DA : List Nat}
    {K : BitVec 64 → (Nat → BitVec 64) → Mem → Prop} {s : SS} {x : SE} (h1 : ObsOK ρ S DA s.obs)
    (h2 : K (x.den ρ) (regsDen ρ s.regs) (memDen ρ s.mem)) : (Tree.jr s x).WP ρ S DA K := ⟨h1, h2⟩

theorem ObsOK_nil {ρ : Env} {S : Nat → Prop} {DA : List Nat} : ObsOK ρ S DA [] :=
  fun _ h => nomatch h

theorem ObsOK_cons {ρ : Env} {S : Nat → Prop} {DA : List Nat} {o : SOb} {l : List SOb}
    (h1 : o.den ρ S DA) (h2 : ObsOK ρ S DA l) : ObsOK ρ S DA (o :: l) := by
  intro x hx
  rcases List.mem_cons.1 hx with rfl | hx
  · exact h1
  · exact h2 x hx

open Lean Meta Elab Tactic in
/-- `sym_eval` replaces the (closed) `Tree.prune Γ (symRun C n s)` (or `symRun C n s`) in the goal by its value, computed by
compiled evaluation; the kernel re-checks the replacement as one definitional unfolding. -/
elab "sym_eval" : tactic => do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let closed (e : Expr) := !e.hasFVar && !e.hasMVar
  let some e := (tgt.find? (fun e => e.isAppOfArity ``Tree.prune 2 && closed e)).orElse
      (fun _ => tgt.find? (fun e => e.isAppOfArity ``symRun 3 && closed e))
    | throwError "sym_eval: no closed `symRun`/`Tree.prune` in the goal"
  let v ← unsafe evalExpr Tree (mkConst ``Tree) e
  let te := toExpr v
  let tgt' := tgt.replace fun x => if x == e then some te else none
  replaceMainGoal [← g.replaceTargetDefEq tgt']

theorem mem_accAddrs_iff' {a w b : Nat} : b ∈ accAddrs a w ↔ a ≤ b ∧ b < a + w :=
  ⟨of_mem_accAddrs, fun ⟨h1, h2⟩ => by
    have e : a + (b - a) = b := by omega
    rw [← e]; exact mem_accAddrs (by omega)⟩

open Lean Meta Elab Tactic in
/-- `sym_dec` closes every goal `DecM _` / `DecT _` by `rfl` on the partially evaluated decoder,
leaving the conversion to the kernel. -/
elab "sym_dec" : tactic => do
  let gs ← getGoals
  let mut rest := #[]
  for g in gs do
    let ty ← instantiateMVars (← g.getType)
    if ty.isAppOfArity ``DecM 1 || ty.isAppOfArity ``DecT 1 then
      let some ty' ← unfoldDefinition? ty | rest := rest.push g; continue
      let v ← forallTelescope ty' fun xs body => do
        let some (_, _, rhs) := body.eq? | throwError "sym_dec: unexpected goal"
        mkLambdaFVars xs (← mkEqRefl rhs)
      g.assign v
    else rest := rest.push g
  setGoals rest.toList

/-- `geom_auto [facts]` proves `Geom.holds` for a literal fact list: it unfolds every fact,
rewrites the atoms with the given hypotheses and closes each arithmetic conjunct by `omega`. -/
macro "geom_auto" " [" ts:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic| (
  simp only [Geom.holds, List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_implies,
    implies_true, and_true, AFact.holds, SE.den, reduceCtorEq, Option.some.injEq, forall_eq',
    List.mem_append, mem_accAddrs_iff', Nat.mod_one, forall_const, BitVec.add_zero, $ts,*] <;>
  (and_intros <;> (try intros) <;> first | exact True.intro | omega)))

end VsaIris.SymExec
