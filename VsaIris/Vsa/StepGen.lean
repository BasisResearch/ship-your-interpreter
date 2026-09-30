import VsaIris.Interp.IRun
import VsaIris.Vsa.SymObs
import VsaIris.Vsa.SymJalr
import VsaIris.Vsa.SymHavoc
import VsaIris.Vsa.AllocRun
import VsaIris.Interp.EnvRun
import VsaIris.Vsa.Stdout.NRun
import VsaIris.Vsa.SnpRunDef
import Vsa.Sim.DecodeNF

/-!
# Step lemmas from the code image, on demand

A symbolic run (`SWP` over a text) advances one instruction at a time. The step lemma
for the instruction at a literal `pc` is determined by the four code bytes at `pc` in
the loaded image, the run predicate (its text, register list and data view) and the
lemma family (owned/data/table/havoc load, observed ALU step, call, ...). This module
reads the word from the image, classifies it, and elaborates the step lemma for that
`pc` when a driver or a proof asks for it (`stepLemma`, `step% fam pc`). A lemma is
elaborated once per module and kept as an auxiliary theorem.

Everything specific to one binary and run predicate is a `Tbl` value: the code
pieces, the run predicate, the text and its code-footprint lemma, the `gp` value and
the initialised data words it reads. A sibling binary supplies its own tables.
-/

namespace VsaIris.Sym.StepGen

open Lean Elab Term Meta

/-! ## Words from the image -/

/-- The byte a piece list claims at `a`. -/
def piecesByte? (ps : List Vsa.Sim.TextPiece) (a : Nat) : Option (BitVec 8) :=
  (ps.find? fun p => Vsa.Sim.inRangesB p.ranges a).map fun p => p.img a

/-- The little-endian word at `pc`, when all four bytes are claimed. -/
def piecesWord? (ps : List Vsa.Sim.TextPiece) (pc : Nat) : Option Nat := do
  let b0 ← piecesByte? ps pc
  let b1 ← piecesByte? ps (pc + 1)
  let b2 ← piecesByte? ps (pc + 2)
  let b3 ← piecesByte? ps (pc + 3)
  return b0.toNat + 256 * b1.toNat + 65536 * b2.toNat + 16777216 * b3.toNat

/-- The word at `pc` in the pieces named `ps`, computed by the compiled image function. -/
def wordAt? (ps : Name) (pc : Nat) : MetaM (Option Nat) := do
  let e := mkApp2 (mkConst ``piecesWord?) (mkConst ps) (mkNatLit pc)
  unsafe evalExpr (Option Nat) (mkApp (mkConst ``Option [0]) (mkConst ``Nat)) e

/-! ## Literal syntax -/

def hx (n : Nat) : String := String.ofList (Nat.toDigits 16 n)

def hxw (w n : Nat) : String :=
  let s := hx n
  String.ofList (List.replicate (w - s.length) '0') ++ s

def m64 : Nat := 2 ^ 64

def sext (v b : Nat) : Int := if (v >>> (b - 1)) % 2 = 1 then (v : Int) - 2 ^ b else v

def modN (v : Int) (m : Nat) : Nat := (v % (m : Int)).toNat

def lit64 (v : Int) : String := s!"0x{hx (modN v m64)}#64"

def i12 (v : Int) : String := s!"(0x{hxw 3 (modN v 4096)}#12)"

def sx12 (v : Int) : String := s!"sign_extend (m := 64) {i12 v}"

def lst (xs : List Nat) : String := "[" ++ ", ".intercalate (xs.map toString) ++ "]"

def ksOf (rs : List Nat) : List Nat :=
  ((rs.filter (· ≠ 0)).eraseDups).mergeSort (· ≤ ·)

/-! ## Classification -/

/-- The instruction classes the step families cover. Values (`val`) are stated in the
    form the reflected segment computes, so `rfl` closes them. -/
inductive Cls where
  | alu (rd : Nat) (srcs : List Nat) (val : String)
  | load (rd rs1 : Nat) (imm : Int) (kind : String) (width : Nat)
  | store (rs1 rs2 : Nat) (imm : Int) (kind : String) (width : Nat)
  | br (op : String) (rs1 rs2 : Nat) (imm : Int) (tgt : Nat)
  | j (imm : Int) (tgt : Nat)
  | jal (imm : Int) (tgt : Nat)
  | ret
  | jr (rs1 : Nat)
  | jri (rs1 imm : Nat)
  | jalr (rs1 imm : Nat)
  | jalrn (rs1 : Nat)
  | obs (sltu : Bool) (rd rs1 rs2 imm : Nat)
  | unsupported

structure Fields where
  op : Nat
  rd : Nat
  f3 : Nat
  rs1 : Nat
  rs2 : Nat
  f7 : Nat
  immI : Int
  immS : Int
  immB : Int
  immJ : Int

def fields (w : Nat) : Fields where
  op := w % 128
  rd := (w >>> 7) % 32
  f3 := (w >>> 12) % 8
  rs1 := (w >>> 15) % 32
  rs2 := (w >>> 20) % 32
  f7 := w >>> 25
  immI := sext (w >>> 20) 12
  immS := sext (((w >>> 25) <<< 5) ||| ((w >>> 7) % 32)) 12
  immB := sext ((((w >>> 31) % 2) <<< 12) ||| (((w >>> 7) % 2) <<< 11) |||
    (((w >>> 25) % 64) <<< 5) ||| (((w >>> 8) % 16) <<< 1)) 13
  immJ := sext ((((w >>> 31) % 2) <<< 20) ||| (((w >>> 12) % 256) <<< 12) |||
    (((w >>> 20) % 2) <<< 11) ||| (((w >>> 21) % 1024) <<< 1)) 21

/-- A source register as the segment reads it (`gp` is the constant `gpv`). -/
def src (gpv r : Nat) : String :=
  if r = 0 then "(0#64)" else if r = 3 then s!"({lit64 gpv})" else s!"(R {r})"

/-- The base classifier (shared by every table). -/
def classifyWord (gpv pc w : Nat) : Cls :=
  let f := fields w
  let A := src gpv f.rs1
  let B := src gpv f.rs2
  let sh6 := (w >>> 20) % 64
  let sh5 := (w >>> 20) % 32
  let SH6 := s!"(Sail.BitVec.extractLsb (0x{hxw 2 sh6}#6) 5 0)"
  let SH5 := s!"(0x{hxw 2 sh5}#5)"
  let X32 := fun (e : String) => s!"(Sail.BitVec.extractLsb {e} 31 0)"
  let U := s!"(sign_extend (m := 64) ((0x{hxw 5 ((w >>> 12) % 1048576)}#20) +++ (0x000#12)))"
  if f.op = 0x13 then
    let i := f.immI
    let v? : Option String :=
      if f.f3 = 0 then some s!"{A} + {sx12 i}"
      else if f.f3 = 7 then some s!"{A} &&& {sx12 i}"
      else if f.f3 = 6 then some s!"{A} ||| {sx12 i}"
      else if f.f3 = 4 then some s!"{A} ^^^ {sx12 i}"
      else if f.f3 = 1 then some s!"shift_bits_left {A} {SH6}"
      else if f.f3 = 2 then some s!"sltiV {A} ({sx12 i})"
      else if f.f3 = 5 ∧ f.f7 / 2 = 0 then some s!"shift_bits_right {A} {SH6}"
      else if f.f3 = 5 ∧ f.f7 / 2 = 0x10 then some s!"shift_bits_right_arith {A} {SH6}"
      else none
    match v? with
    | some v => .alu f.rd [f.rs1] v
    | none => .unsupported
  else if f.op = 0x1b then
    let i := f.immI
    let v? : Option String :=
      if f.f3 = 0 then some s!"sign_extend (m := 64) {X32 s!"({A} + {sx12 i})"}"
      else if f.f3 = 1 then some s!"sign_extend (m := 64) (shift_bits_left {X32 A} {SH5})"
      else if f.f3 = 5 ∧ f.f7 = 0 then some s!"sign_extend (m := 64) (shift_bits_right {X32 A} {SH5})"
      else if f.f3 = 5 ∧ f.f7 = 0x20 then
        some s!"sign_extend (m := 64) (shift_bits_right_arith {X32 A} {SH5})"
      else none
    match v? with
    | some v => .alu f.rd [f.rs1] v
    | none => .unsupported
  else if f.op = 0x33 then
    let v? : Option String :=
      if f.f3 = 0 ∧ f.f7 = 0 then some s!"{A} + {B}"
      else if f.f3 = 0 ∧ f.f7 = 0x20 then some s!"{A} - {B}"
      else if f.f3 = 6 ∧ f.f7 = 0 then some s!"{A} ||| {B}"
      else if f.f3 = 7 ∧ f.f7 = 0 then some s!"{A} &&& {B}"
      else if f.f3 = 4 ∧ f.f7 = 0 then some s!"{A} ^^^ {B}"
      else if f.f3 = 1 ∧ f.f7 = 0 then some s!"shift_bits_left {A} (Sail.BitVec.extractLsb {B} 5 0)"
      else if f.f3 = 5 ∧ f.f7 = 0 then some s!"shift_bits_right {A} (Sail.BitVec.extractLsb {B} 5 0)"
      else if f.f3 = 2 ∧ f.f7 = 0 then some s!"sltV {A} {B}"
      else none
    match v? with
    | some v => .alu f.rd [f.rs1, f.rs2] v
    | none => .unsupported
  else if f.op = 0x3b then
    let v? : Option String :=
      if f.f3 = 0 ∧ f.f7 = 0 then some s!"sign_extend (m := 64) ({X32 A} + {X32 B})"
      else if f.f3 = 0 ∧ f.f7 = 0x20 then some s!"sign_extend (m := 64) ({X32 A} - {X32 B})"
      else none
    match v? with
    | some v => .alu f.rd [f.rs1, f.rs2] v
    | none => .unsupported
  else if f.op = 0x37 then .alu f.rd [] U
  else if f.op = 0x17 then .alu f.rd [] s!"(0x{hx pc}#64) + {U}"
  else if f.op = 0x03 then
    match f.f3 with
    | 3 => .load f.rd f.rs1 f.immI "ld" 8
    | 2 => .load f.rd f.rs1 f.immI "lw" 4
    | 6 => .load f.rd f.rs1 f.immI "lwu" 4
    | 4 => .load f.rd f.rs1 f.immI "lbu" 1
    | 1 => .load f.rd f.rs1 f.immI "lh" 2
    | 5 => .load f.rd f.rs1 f.immI "lhu" 2
    | _ => .unsupported
  else if f.op = 0x23 then
    match f.f3 with
    | 3 => .store f.rs1 f.rs2 f.immS "sd" 8
    | 2 => .store f.rs1 f.rs2 f.immS "sw" 4
    | 0 => .store f.rs1 f.rs2 f.immS "sb" 1
    | 1 => .store f.rs1 f.rs2 f.immS "sh" 2
    | _ => .unsupported
  else if f.op = 0x63 then
    let tgt := modN ((pc : Int) + f.immB) m64
    match f.f3 with
    | 0 => .br "BEQ" f.rs1 f.rs2 f.immB tgt
    | 1 => .br "BNE" f.rs1 f.rs2 f.immB tgt
    | 4 => .br "BLT" f.rs1 f.rs2 f.immB tgt
    | 5 => .br "BGE" f.rs1 f.rs2 f.immB tgt
    | 6 => .br "BLTU" f.rs1 f.rs2 f.immB tgt
    | 7 => .br "BGEU" f.rs1 f.rs2 f.immB tgt
    | _ => .unsupported
  else if f.op = 0x6f then
    let tgt := modN ((pc : Int) + f.immJ) m64
    if f.rd = 0 then .j f.immJ tgt else if f.rd = 1 then .jal f.immJ tgt else .unsupported
  else if f.op = 0x67 ∧ f.rd = 0 ∧ f.rs1 = 1 ∧ f.immI = 0 then .ret
  else .unsupported

/-- Which extra classes a run table recognises before the base classifier. -/
inductive Flavor where
  | interp
  | stdio
  | snp
  | alloc
  deriving BEq, Inhabited

def classify (fl : Flavor) (gpv pc w : Nat) : Cls :=
  if fl == .alloc then classifyWord gpv pc w else
  let f := fields w
  let hi := w >>> 20
  if f.op = 0x33 ∧ f.f3 = 3 ∧ f.f7 = 0 ∧ f.rd ≠ 0 then .obs true f.rd f.rs1 f.rs2 0
  else if f.op = 0x13 ∧ f.f3 = 3 ∧ f.rd ≠ 0 then .obs false f.rd f.rs1 0 (hi % 4096)
  else if f.op = 0x67 ∧ f.rd = 0 ∧ f.f3 = 0 ∧ hi = 0 ∧ f.rs1 ≠ 1 then .jr f.rs1
  else if fl == .snp ∧ f.op = 0x67 ∧ f.f3 = 0 ∧ f.rd = 0 ∧ hi ≠ 0 then .jri f.rs1 hi
  else if fl == .snp ∧ f.op = 0x67 ∧ f.f3 = 0 ∧ f.rd = 1 ∧ hi = 0 then .jalrn f.rs1
  else if fl == .stdio ∧ f.op = 0x67 ∧ f.rd = 1 ∧ f.f3 = 0 ∧ f.rs1 ≠ 0 ∧ f.rs1 ≠ 1 then
    .jalr f.rs1 (hi % 4096)
  else if fl == .stdio ∧ f.op = 0x67 ∧ f.rd = 0 ∧ f.f3 = 0 ∧ hi ≠ 0 ∧ f.rs1 ≠ 0 ∧ f.rs1 ≠ 1 then
    .jri f.rs1 (hi % 4096)
  else classifyWord gpv pc w

/-! ## Run tables -/

/-- A run predicate with its text: everything a step family needs to know about one
    code image. -/
structure Tbl where
  key : String
  flavor : Flavor
  /-- The code pieces the words are read from. -/
  pieces : Name
  /-- The run predicate applied to its fixed arguments, e.g. `IW live Dt DA S Q`. -/
  run : String
  /-- The implicit binders of a step lemma (the run's arguments, `R`, `Mt`). -/
  binders : String
  /-- The text (read-only footprint) of the run. -/
  text : String
  /-- The code-footprint lemma of the text (`codeFoot` of a literal site lies in it). -/
  code : String
  /-- The register list of the run. -/
  regs : String
  /-- The value of `gp`, a read-only constant of every run. -/
  gpv : Nat
  /-- A gp-relative doubleword the text carries as data, and its lemma and bytes. -/
  impure : Option (Nat × String × List Nat) := none
  /-- Loads from the constant tables, with the table image and footprint names. -/
  tableLoads : List Nat := []
  roImg : String := ""
  ro : String := ""
  /-- Code ranges without step lemmas (code-only leaves, printed stores). -/
  skip : List (Nat × Nat) := []

def Tbl.hasD (t : Tbl) : Bool := t.flavor != .alloc

def dBinders : String :=
  "{live : Nat → Prop} {Dt : Mem} {DA : List Nat} {S : Nat → Prop}\n    " ++
  "{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}"

def aBinders : String :=
  "{live : Nat → Prop} {S : Nat → Prop}\n    " ++
  "{Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}"

/-! ## Templates -/

/-- A step lemma: binders (implicit and hypotheses), conclusion and proof. -/
structure Lem where
  binders : String
  concl : String
  proof : String

section Templates

variable (t : Tbl) (pc w : Nat)

def bytes : List Nat := (List.range 4).map fun i => (w >>> (8 * i)) % 256

def codeLits : String := ", ".intercalate ((bytes w).map fun b => s!"0x{hxw 2 b}#8")

def nxt : String := s!"0x{hx (pc + 4)}#64"

def pcL : String := s!"0x{hx pc}#64"

def runAt (pcE R Mt : String) : String :=
  s!"{t.run} {pcE} {R} {Mt}"

def hdr : String := s!"{t.binders}\n    (hlive : ∀ p ∈ {t.text}, live p.1)"

def single : String :=
  s!"([\{ body := [mkLine 0x{hx pc}#64 0x{hxw 8 w}#32], term := none }] : List BBlock)"

def tinstr (kind : String) (rs1 rs2 : Nat) (i13 i21 : Int) (i12? : Option Nat := none) : String :=
  let bs := bytes w
  let bl := ", ".intercalate (bs.map fun b => s!"0x{hxw 2 b}#8")
  let last := match i12? with
    | none => "0#12"
    | some v => s!"0x{hxw 3 v}#12"
  s!"⟨0x{hx pc}#64, 0x{hxw 8 w}#32, {bl}, {kind}, {rs1}, {rs2}, 0x{hx (modN i13 8192)}#13, " ++
    s!"0x{hx (modN i21 2097152)}#21, {last}⟩"

def tseg (kind : String) (rs1 rs2 : Nat) (i13 i21 : Int) (i12? : Option Nat := none) : String :=
  s!"([⟨[], some ({tinstr pc w kind rs1 rs2 i13 i21 i12?} : TInstr)⟩] : List BBlock)"

def hR (ks : List Nat) : String :=
  let alts := " | ".intercalate (ks.map fun _ => "rfl")
  "(by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; " ++
    s!"rcases hx with {alts} <;> first | rfl | exact absurd rfl hg)"

def hRo (ks : List Nat) (rd? : Option Nat := none) : String :=
  match rd? with
  | none => "(fun _ _ _ _ => rfl)"
  | some rd => s!"(fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : {rd} ∈ {lst ks}))))"

def hgp (ks : List Nat) : String :=
  if ks.contains 3 then "(fun _ => rfl)" else "(fun h => absurd h (by decide))"

def nilCover : String := "(fun a _ => trivial)"

/-- The `swp_stepD`/`swp_step` application for one segment. -/
def step (seg : String) (ks : List Nat) (lds LD Wr cover tail hpc R Ro hk : String)
    (gp : Option String := none) : String :=
  let tl := if tail.isEmpty then "" else s!"; {tail}"
  let ld := if LD == "[]" then "(fun a h => by cases h)" else "hLDS"
  let wr := if Wr == "[]" then "(fun a h => by cases h)" else "hS"
  let base := if t.hasD then "swp_stepD" else "swp_step"
  let lam := if t.hasD then "fun m hm hD hLD" else "fun m hm hLD"
  let g := gp.getD (hgp ks)
  s!"{base} {seg} {lst ks} {lds} {LD} {Wr} 0 rfl (by decide) (by decide) (by decide)\n" ++
  s!"    {cover} hlive\n" ++
  s!"    ({lam} => by unfold ChainFacts; chain_facts hm{tl})\n" ++
  s!"    (by decide) (by decide) {g} (by decide) {ld}\n" ++
  s!"    {wr} {hpc}\n" ++
  s!"    {R}\n" ++
  s!"    {Ro} rfl {hk}"

def eaOf (rs1 : Nat) (imm : Int) : String := s!"({src t.gpv rs1} + {sx12 imm}).toNat"

def condOf (op : String) (A B : String) : String × String :=
  if op == "BEQ" then (s!"{A} = {B}", "guard_beq")
  else if op == "BNE" then (s!"{A} ≠ {B}", "guard_bne")
  else if op == "BLT" then (s!"{A}.toInt < {B}.toInt", "guard_blt")
  else if op == "BGE" then (s!"{B}.toInt ≤ {A}.toInt", "guard_bge")
  else if op == "BLTU" then (s!"{A}.toNat < {B}.toNat", "guard_bltu")
  else (s!"{B}.toNat ≤ {A}.toNat", "guard_bgeu")

/-- The code-footprint membership of the site at `pc` in the run's text (and in
    `text ++ data` for a run with a data view). -/
def codeIn : String := s!"(({t.code} (by decide)) p hp)"

def codeInT : String :=
  if t.hasD then s!"(fun p hp => List.mem_append_left _ {codeIn t})" else s!"({t.code} (by decide))"

/-- The four byte facts of a site, from the site's memory reads `hMR`. -/
def hbLines (h : String) (ind : String) : String :=
  "\n".intercalate ((List.range 4).map fun i =>
    s!"{ind}have hb{i} := {h} (0x{hx (pc + i)}, .discard, 0x{hxw 2 ((bytes w)[i]!)}#8) (by simp [codeFoot])")

def byteArgs : String := " ".intercalate ((bytes w).map fun b => s!"(0x{hxw 2 b}#8)")

def decodeArg (σ : String) (ind : String) : String :=
  s!"(Vsa.Sim.decodeW (w := 0x{hxw 8 w}#32) (afterPrelude {σ})\n" ++
  s!"{ind}  (by rw [get?_afterPrelude {σ} _ (by decide)]; exact hG.misa)\n" ++
  s!"{ind}  (by rw [get?_afterPrelude {σ} _ (by decide)]; exact hG.cur_privilege)\n" ++
  s!"{ind}  (by rw [get?_afterPrelude {σ} _ (by decide)]; exact hG.mseccfg))"

/-- `jal` at `pc`: its `JalExec` fact (independent of the run table). -/
def jalxLem (tgt : Nat) (imm : Int) : Lem :=
  let code := codeLits w
  { binders := s!"(live : Nat → Prop)\n    (hlive : ∀ p ∈ codeFoot 0x{hx pc} [{code}], live p.1)"
    concl := s!"JalExec (vsaModel live) 0x{hx pc} [{code}] 0x{hx tgt}#64"
    proof := "by\n" ++
      "  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_\n" ++
      "  obtain ⟨vm, hmi⟩ := hG.minstret\n" ++
      hbLines pc w "hb" "  " ++ "\n" ++
      "  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=\n" ++
      s!"    stepObs_jal c.σ c.tick c.steps (0x{hx pc}#64) vm (0x{hxw 8 w}#32) (0x{hxw 6 (modN imm 2097152)}#21)\n" ++
      s!"      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x{hx pc}#64) 4)\n" ++
      s!"      {byteArgs w}\n" ++
      "      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)\n" ++
      "      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)\n" ++
      s!"      {decodeArg w "c.σ" "      "}\n" ++
      "      (by decide)\n" ++
      "      (by decide) (by decide) (by decide) (by decide) (by decide)\n" ++
      s!"      (wX_bits_x1 _ (BitVec.addInt (0x{hx pc}#64) 4)) hi\n" ++
      s!"  have h := jalStep_of_obs (calleeEntry := 0x{hx tgt}#64) hs hi' hG' hmem hobs\n" ++
      "    (by apply BitVec.eq_of_toNat_eq; decide)\n" ++
      "  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩\n" ++
      s!"  rwa [show BitVec.addInt (0x{hx pc}#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x{hx pc} + 4) from by\n" ++
      "    apply BitVec.eq_of_toNat_eq; decide] at h" }

/-- `jalr ra,0(r)` at `pc`: its `JalrObs` fact. -/
def jalroLem (r : Nat) : Lem :=
  let code := codeLits w
  { binders := "(tgt : BitVec 64) (hal : tgt.toNat % 4 = 0)"
    concl := s!"JalrObs 0x{hx pc} [{code}] {r} tgt"
    proof := "by\n" ++
      "  intro σ ti u vm hG hpc hmi hrs hb hti\n" ++
      hbLines pc w "hb" "  " ++ "\n" ++
      s!"  have h := stepObs_jalr σ ti u (0x{hx pc}#64) vm tgt (0x{hxw 8 w}#32) (0x000#12)\n" ++
      s!"    (regidx.Regidx 0x{hxw 2 r}#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x{hx pc}#64) 4)\n" ++
      s!"    {byteArgs w}\n" ++
      "    hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)\n" ++
      "    (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)\n" ++
      s!"    {decodeArg w "σ" "    "}\n" ++
      s!"    (rX_bits_x{r} _ tgt (by rw [get?_afterNextPC σ (0x{hx pc}#64) _ (by decide) (by decide)]; exact hrs))\n" ++
      "    (by rw [ret_tgt _ hal]; exact hal)\n" ++
      "    (by decide) (by decide) (by decide) (by decide) (by decide)\n" ++
      s!"    (wX_bits_x1 _ (BitVec.addInt (0x{hx pc}#64) 4)) hti\n" ++
      "  rw [ret_tgt _ hal] at h\n" ++
      "  exact h" }

/-- The step lemma of family `kind` (`""` main, `"D"`, `"T"`, `"H"`, `"P"`, `"O"`, `"J"`,
    `"C"`) at `pc`, or `none` when the table has no such step there. -/
def lemOf (kind : String) : Option Lem := Id.run do
  let c := classify t.flavor t.gpv pc w
  let H := hdr t
  let run := fun (pcE : String) => runAt t pcE "R" "Mt"
  let runR := fun (pcE Rv : String) => runAt t pcE Rv "Mt"
  let runM := fun (pcE Mv : String) => runAt t pcE "R" Mv
  let ld (k : String) (rd rs1 : Nat) (imm : Int) (kn : String) (wd : Nat) : Option Lem := Id.run do
    let ea := eaOf t rs1 imm
    let ks := ksOf [rs1, rd]
    let sfx := toString wd
    if t.flavor == .alloc then
      if k != "" then return none
      let conc := rs1 = 3
      if let some (ia, ilem, ibytes) := t.impure then
        if conc ∧ modN ((t.gpv : Int) + imm) m64 = ia then
          let bl := ", ".intercalate (ibytes.map fun b => s!"0x{hxw 2 b}#8")
          return some { binders := H ++ s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} (bytesVal .ld [{bl}]))"})"
                        concl := run (pcL pc)
                        proof := step t (single pc w) ks s!"[[{bl}]]" "[]" "[]" nilCover
                          s!"exact ⟨(show LdOK {ea} 8 by decide), {ilem} hm⟩" "rfl" (hR ks)
                          (hRo ks (some rd)) "hk" }
      let okh := if conc then "" else s!"\n    (hea : LdOK {ea} {wd})"
      let okp := if conc then s!"(show LdOK {ea} {wd} by decide)" else "hea"
      return some { binders := H ++ okh ++ s!"\n    (hLDS : ∀ b ∈ accAddrs {ea} {wd}, S b)" ++
                      s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} (ldv .{kn} Mt {ea}))"})"
                    concl := run (pcL pc)
                    proof := step t (single pc w) ks s!"[bytesAt (imgM Mt) {ea} {wd}]"
                      s!"(accAddrs {ea} {wd})" "[]" nilCover s!"exact ⟨{okp}, lpins{sfx}_img hLD⟩"
                      "rfl" (hR ks) (hRo ks (some rd)) "hk" }
    let alts := " | ".intercalate (ks.map fun _ => "rfl")
    let havoc (lemma bodyHk : String) : Lem :=
      { binders := H ++ s!"\n    (hea : LdOK {ea} {wd})\n    (hk : {bodyHk})"
        concl := run (pcL pc)
        proof := s!"{lemma} (T := {t.text}) (D := dataOf Dt DA) (rs := {t.regs}) (S := S) (Q := Q) (R := R) (Mt := Mt)\n" ++
          s!"    {single pc w} {lst ks} {rd} (accAddrs {ea} {wd}) (fun f => [bytesAt f {ea} {wd}]) 0\n" ++
          "    (fun f g h => congrArg (· :: []) (List.map_congr_left fun j hj => h _ (mem_accAddrs (List.mem_range.mp hj))))\n" ++
          "    rfl (by decide) (by decide) (by decide) (fun _ _ => trivial) hlive\n" ++
          s!"    (fun m hm hD => by unfold ChainFacts; chain_facts hm; exact ⟨hea, lpins{sfx}_img (fun b _ => rfl)⟩)\n" ++
          s!"    (by decide) (by decide) (by decide) (fun _ => {hgp ks}) (by decide) (fun _ => rfl)\n" ++
          s!"    (fun _ x hx hg hr => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with {alts} <;> first | rfl | exact absurd rfl hg | exact absurd rfl hr)\n" ++
          "    hk" }
    if k == "" then
      return some { binders := H ++ s!"\n    (hea : LdOK {ea} {wd})\n    (hLDS : ∀ b ∈ accAddrs {ea} {wd}, S b)" ++
                      s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} (ldv .{kn} Mt {ea}))"})"
                    concl := run (pcL pc)
                    proof := step t (single pc w) ks s!"[bytesAt (imgM Mt) {ea} {wd}]"
                      s!"(accAddrs {ea} {wd})" "[]" nilCover s!"exact ⟨hea, lpins{sfx}_img hLD⟩"
                      "rfl" (hR ks) (hRo ks (some rd)) "hk" }
    if k == "D" then
      return some { binders := H ++ s!"\n    (hea : LdOK {ea} {wd})\n    (hLDD : ∀ b ∈ accAddrs {ea} {wd}, b ∈ DA)" ++
                      s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} (ldv .{kn} Dt {ea}))"})"
                    concl := run (pcL pc)
                    proof := step t (single pc w) ks s!"[bytesAt (imgM Dt) {ea} {wd}]" "[]" "[]" nilCover
                      s!"exact ⟨hea, lpins{sfx}_img (fun b hb => dataReads_view hD b (hLDD b hb))⟩"
                      "rfl" (hR ks) (hRo ks (some rd)) "hk" }
    if k == "H" then
      return some (havoc "swp_havocD" s!"∀ v, {runR (nxt pc) s!"(upd R {rd} v)"}")
    if k == "P" ∧ t.flavor != .interp then
      return some (havoc "swp_havocP"
        (s!"∀ v, (∃ f : Nat → BitVec 8, (∀ p ∈ dataOf Dt DA, f p.1 = p.2) ∧ (∀ a, S a → f a = imgM Mt a) ∧\n" ++
         s!"      v = ldvf .{kn} f {ea}) → {runR (nxt pc) s!"(upd R {rd} v)"}"))
    if k == "T" ∧ t.tableLoads.contains pc then
      return some { binders := H ++ s!"\n    (hea : LdOK {ea} {wd})" ++
                      s!"\n    (hLDT : ∀ b ∈ accAddrs {ea} {wd}, (b, {t.roImg} b) ∈ {t.ro})" ++
                      s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} (ldvf .{kn} {t.roImg} {ea}))"})"
                    concl := run (pcL pc)
                    proof := step t (single pc w) ks s!"[bytesAt {t.roImg} {ea} {wd}]" "[]" "[]" nilCover
                      s!"exact ⟨hea, lpins{sfx}_fn (fun b hb => by rw [hm _ (List.mem_append_right _ (hLDT b hb))]; rfl)⟩"
                      "rfl" (hR ks) (hRo ks (some rd)) "hk" }
    return none
  match c with
  | .unsupported => return none
  | .alu rd srcs v =>
    if kind != "" then return none
    let ks := ksOf (srcs ++ [rd])
    return some { binders := H ++ s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} ({v}))"})"
                  concl := run (pcL pc)
                  proof := step t (single pc w) ks "[]" "[]" "[]" nilCover "" "rfl" (hR ks) (hRo ks (some rd)) "hk" }
  | .load rd rs1 imm kn wd => return ld kind rd rs1 imm kn wd
  | .store rs1 rs2 imm kn wd =>
    if kind != "" then return none
    let ea := eaOf t rs1 imm
    let ks := ksOf [rs1, rs2]
    let ok := if kn == "sb" then s!"StOKb {ea}" else s!"StOK {ea} {wd}"
    let conc := t.flavor == .alloc ∧ rs1 = 3
    let okh := if conc then "" else s!"\n    (hea : {ok})"
    let okp := if conc then s!"(show {ok} by decide)" else "hea"
    return some { binders := H ++ okh ++ s!"\n    (hS : ∀ b ∈ accAddrs {ea} {wd}, S b)" ++
                    s!"\n    (hk : {runM (nxt pc) s!"(writeLog Mt [({ea}, {wd}, {src t.gpv rs2})])"})"
                  concl := run (pcL pc)
                  proof := step t (single pc w) ks "[]" "[]" s!"(accAddrs {ea} {wd})"
                    "(fun a ha => outL_single _ ha)" s!"exact {okp}" "rfl" (hR ks) (hRo ks) "hk" }
  | .br op rs1 rs2 imm tgt =>
    if kind != "" then return none
    let (cond, gl) := condOf op (src t.gpv rs1) (src t.gpv rs2)
    let ks := ksOf [rs1, rs2]
    let segT := tseg pc w s!".br bop.{op} true" rs1 rs2 imm 0
    let segF := tseg pc w s!".br bop.{op} false" rs1 rs2 imm 0
    return some { binders := H ++ s!"\n    (hT : {cond} → {run s!"0x{hx tgt}#64"}) (hF : ¬ ({cond}) → {run (nxt pc)})"
                  concl := run (pcL pc)
                  proof := s!"if hc : {cond} then\n    " ++
                    step t segT ks "[]" "[]" "[]" nilCover s!"exact ({gl} _ _).2 hc" "rfl" (hR ks) (hRo ks) "(hT hc)" ++
                    "\n  else\n    " ++
                    step t segF ks "[]" "[]" "[]" nilCover s!"exact (guard_false ({gl} _ _)).2 hc" "rfl" (hR ks) (hRo ks) "(hF hc)" }
  | .j imm tgt =>
    if kind != "" then return none
    let gp := if t.flavor == .alloc then some "(fun h => nomatch h)" else none
    return some { binders := H ++ s!"\n    (hk : {run s!"0x{hx tgt}#64"})"
                  concl := run (pcL pc)
                  proof := step t (tseg pc w ".j" 0 0 0 imm) [] "[]" "[]" "[]" nilCover "" "rfl"
                    "(fun _ h => nomatch h)" (hRo []) "hk" gp }
  | .ret | .jr _ =>
    if kind != "" then return none
    let r := match c with
      | .jr r => r
      | _ => 1
    return some { binders := H ++ s!"\n    (hal : (R {r}).toNat % 4 = 0) (hk : {run s!"(R {r})"})"
                  concl := run (pcL pc)
                  proof := step t (tseg pc w ".jr" r 0 0 0) [r] "[]" "[]" "[]" nilCover
                    (s!"show (Sail.BitVec.update (R {r} + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; " ++
                      "rw [ret_tgt _ hal]; exact hal")
                    "(ret_tgt _ hal)" (hR [r]) (hRo [r]) "hk" }
  | .jri r imm =>
    if kind != "" then return none
    let tgt := s!"(Sail.BitVec.update (R {r} + sign_extend (m := 64) (0x{hxw 3 imm}#12)) 0 0#1)"
    return some { binders := H ++ s!"\n    (hal : {tgt}.toNat % 4 = 0) (hk : {run tgt})"
                  concl := run (pcL pc)
                  proof := step t (tseg pc w ".jr" r 0 0 0 (some imm)) [r] "[]" "[]" "[]" nilCover
                    "exact hal" "rfl" (hR [r]) (hRo [r]) "hk" }
  | .obs sltu rd rs1 rs2 imm =>
    if kind != "O" then return none
    let A := src t.gpv rs1
    let (val, srcs, ast, ex) :=
      if sltu then
        let B := src t.gpv rs2
        let val := s!"zero_extend (m := 64) (bool_to_bit (zopz0zI_u {A} {B}))"
        (val, [rs1, rs2],
          s!"instruction.RTYPE (regidx.Regidx 0x{hxw 2 rs2}#5, regidx.Regidx 0x{hxw 2 rs1}#5, regidx.Regidx 0x{hxw 2 rd}#5, rop.SLTU)",
          fun (npc post rx : String → String) =>
            s!"execute_rtype_sltu_char (regidx.Regidx 0x{hxw 2 rs2}#5) (regidx.Regidx 0x{hxw 2 rs1}#5) " ++
            s!"(regidx.Regidx 0x{hxw 2 rd}#5) {A} {B} {npc ""} {post ""}\n" ++
            s!"        ({rx (toString rs1)})\n        ({rx (toString rs2)})\n" ++
            s!"        (wX_bits_x{rd} _ ({val}))")
      else
        let val := s!"zero_extend (m := 64) (bool_to_bit (zopz0zI_u {A} (sign_extend (m := 64) (0x{hxw 3 imm}#12))))"
        (val, [rs1],
          s!"instruction.ITYPE (0x{hxw 3 imm}#12, regidx.Regidx 0x{hxw 2 rs1}#5, regidx.Regidx 0x{hxw 2 rd}#5, iop.SLTIU)",
          fun (npc post rx : String → String) =>
            s!"execute_itype_sltiu_char (0x{hxw 3 imm}#12) (regidx.Regidx 0x{hxw 2 rs1}#5) " ++
            s!"(regidx.Regidx 0x{hxw 2 rd}#5) {A} {npc ""} {post ""}\n" ++
            s!"        ({rx (toString rs1)})\n" ++
            s!"        (wX_bits_x{rd} _ ({val}))")
    let ks := ksOf srcs
    let npc := fun (_ : String) => s!"(afterNextPC (afterPrelude c.σ) (0x{hx pc}#64))"
    let post := fun (_ : String) => s!"(sigma3_alu c.σ (0x{hx pc}#64) Register.x{rd} ({val}))"
    let rx := fun (r : String) =>
      if r == "0" then "rX_bits_zero _" else
      s!"rX_bits_x{r} _ (R {r}) (by rw [get?_afterNextPC c.σ (0x{hx pc}#64) _ (by decide) (by decide)]; " ++
        s!"exact hRR ({r}, Iris.DFrac.own 1, R {r}) (by simp))"
    return some
      { binders := H ++ s!"\n    (hk : {runR (nxt pc) s!"(upd R {rd} ({val}))"})"
        concl := run (pcL pc)
        proof := s!"swp_alu 0x{hx pc} [{codeLits w}] {rd} {lst ks} ({val})\n" ++
          "    (aluStep_of_obs (by decide) (by decide)\n" ++
          "      (fun q hq => by\n" ++
          "        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq\n" ++
          s!"        exact (show ∀ k ∈ {lst ks}, 1 ≤ k ∧ k ≤ 31 by decide) k hk)\n" ++
          s!"      (fun p hp => hlive _ {codeIn t})\n" ++
          "      (fun c hG hi hpc hRR hMR => by\n" ++
          "      obtain ⟨vm, hmi⟩ := hG.minstret\n" ++
          hbLines pc w "hMR" "      " ++ "\n" ++
          "      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=\n" ++
          s!"        stepObs_alu c.σ c.tick c.steps (0x{hx pc}#64) vm (0x{hxw 8 w}#32)\n" ++
          s!"          ({ast})\n" ++
          s!"          Register.x{rd} ({val})\n" ++
          s!"          {byteArgs w}\n" ++
          "          hG hpc hmi (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)\n" ++
          s!"          {decodeArg w "c.σ" "          "}\n" ++
          s!"          ({ex npc post rx})\n" ++
          "          (by decide) (by decide) (by decide) (by decide) (by decide)\n" ++
          "          hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide) hi\n" ++
          "      exact ⟨σ', i', vm, hs, hi', hG', hmem, hobs⟩))\n" ++
          s!"    {codeInT t}\n" ++
          "    (by decide) (by decide) (by decide) (by decide) rfl hk" }
  | .jalr rs1 imm =>
    if kind != "" then return none
    let tgt := s!"(Sail.BitVec.update (R {rs1} + sign_extend (m := 64) (0x{hxw 3 imm}#12)) 0 0#1)"
    return some
      { binders := H ++ s!"\n    (hal : {tgt}.toNat % 4 = 0)\n    (hk : {runR tgt s!"(upd R 1 (BitVec.ofNat 64 (0x{hx pc} + 4)))"})"
        concl := run (pcL pc)
        proof := s!"swp_jalr 0x{hx pc} [{codeLits w}] [{rs1}] {tgt}\n" ++
          "    (jalrStep_of_obs\n" ++
          "      (fun q hq => by\n" ++
          "        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq\n" ++
          s!"        exact (show ∀ k ∈ [{rs1}], 1 ≤ k ∧ k ≤ 31 by decide) k hk)\n" ++
          s!"      (fun p hp => hlive _ {codeIn t})\n" ++
          "      (fun c hG hi hpc hRR hMR => by\n" ++
          "      obtain ⟨vm, hmi⟩ := hG.minstret\n" ++
          hbLines pc w "hMR" "      " ++ "\n" ++
          "      obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=\n" ++
          s!"        stepObs_jalr c.σ c.tick c.steps (0x{hx pc}#64) vm (R {rs1}) (0x{hxw 8 w}#32) (0x{hxw 3 imm}#12)\n" ++
          s!"          (regidx.Regidx 0x{hxw 2 rs1}#5) (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x{hx pc}#64) 4)\n" ++
          s!"          {byteArgs w}\n" ++
          "          hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)\n" ++
          "          (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)\n" ++
          s!"          {decodeArg w "c.σ" "          "}\n" ++
          s!"          (rX_bits_x{rs1} _ (R {rs1}) (by rw [get?_afterNextPC c.σ (0x{hx pc}#64) _ (by decide) (by decide)]; exact hRR ({rs1}, Iris.DFrac.own 1, R {rs1}) (by simp)))\n" ++
          "          hal (by decide) (by decide) (by decide) (by decide) (by decide)\n" ++
          s!"          (wX_bits_x1 _ (BitVec.addInt (0x{hx pc}#64) 4)) hi\n" ++
          "      refine ⟨σ', i', vm, hs, hi', hG', hmem, ?_⟩\n" ++
          s!"      rwa [show BitVec.addInt (0x{hx pc}#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x{hx pc} + 4) from by\n" ++
          "        apply BitVec.eq_of_toNat_eq; decide] at hobs))\n" ++
          s!"    {codeInT t}\n" ++
          "    (by decide) (by decide) (by decide) rfl hk" }
  | .jalrn r =>
    if kind != "J" then return none
    return some
      { binders := H ++ s!"\n    (hal : (R {r}).toNat % 4 = 0)\n    (hk : {runR s!"(R {r})" s!"(upd R 1 (BitVec.ofNat 64 (0x{hx pc} + 4)))"})"
        concl := run (pcL pc)
        proof := s!"swp_nstep 0x{hx pc} _ _ 1 _ _\n" ++
          s!"    (nstep_of_jalrObs (fun p hp => hlive _ {codeIn t}) ((step% jalrn 0x{hx pc}) (R {r}) hal)\n" ++
          "      (by decide) (by decide))\n" ++
          s!"    {codeInT t}\n" ++
          "    (fun p hp => by\n" ++
          "      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp\n" ++
          "      subst hp; exact ⟨by dsimp only; decide, by dsimp only; decide, rfl⟩)\n" ++
          "    (by decide) (by decide) rfl hk" }
  | .jal _ tgt =>
    let follow := (t.flavor == .stdio ∧ kind == "") ∨ (t.flavor == .snp ∧ kind == "C") ∨
      (t.flavor == .alloc ∧ kind == "")
    if !follow then return none
    let ra := if t.flavor == .alloc then "VsaIris.ra" else "1"
    let jn := if t.flavor == .snp then "jalxn" else "jalx"
    let jx := s!"((step% {jn} 0x{hx pc}) live fun p hp => hlive _ {codeIn t})"
    return some
      { binders := H ++ s!"\n    (hk : {runR s!"0x{hx tgt}#64" s!"(upd R {ra} (BitVec.ofNat 64 (0x{hx pc} + 4)))"})"
        concl := run (pcL pc)
        proof := s!"swp_jal 0x{hx pc} [{codeLits w}] 0x{hx tgt}#64 {jx}\n" ++
          s!"    {codeInT t} (by decide) (by decide) rfl hk" }

end Templates

/-! ## The tables of this binary -/

def gpV : Nat := 0x8001b510

def interpTbl : Tbl where
  key := "interp"
  flavor := .interp
  pieces := ``VsaIris.Sym.interpCodePieces
  run := "IW live Dt DA S Q"
  binders := dBinders
  text := "interpText"
  code := "interp_code"
  regs := "iRegs"
  gpv := gpV
  tableLoads := [0x800031a4, 0x8000354c, 0x80004028, 0x80002880, 0x8000291c, 0x8000308c,
    0x80003094, 0x800029e8, 0x80003660]
  roImg := "interpROImg"
  ro := "interpRO"

def stdioTbl : Tbl where
  key := "stdio"
  flavor := .stdio
  pieces := ``VsaIris.Sym.stdioPieces
  run := "NW live Dt DA S Q"
  binders := dBinders
  text := "stdioText"
  code := "stdio_code"
  regs := "iRegs"
  gpv := gpV
  -- `strcpy` is a code-only leaf (run by its own symbolic run); `_write`'s putchar store
  -- is printed by `swp_putc`
  skip := [(0x80006dc4, 0x80006ea0), (0x8000005c, 0x80000060)]

def snpTbl : Tbl where
  key := "snp"
  flavor := .snp
  pieces := ``VsaIris.Sym.snpPieces
  run := "SnpW live Dt DA S Q"
  binders := dBinders
  text := "snpText"
  code := "snp_code"
  regs := "nRegs"
  gpv := gpV

def allocTbl : Tbl where
  key := "alloc"
  flavor := .alloc
  pieces := ``VsaIris.Sym.allocPieces
  run := "AW live S Q"
  binders := aBinders
  text := "allocText"
  code := "alloc_code"
  regs := "aRegs"
  gpv := gpV
  impure := some (0x8001b970, "alloc_impure", [0x38, 0xb5, 0x01, 0x80, 0, 0, 0, 0])

def envTbl : Tbl where
  key := "env"
  flavor := .alloc
  pieces := ``VsaIris.Sym.envPieces
  run := "EW live S Q"
  binders := aBinders
  text := "envText"
  code := "env_code"
  regs := "eRegs"
  gpv := gpV

def tables : List Tbl := [interpTbl, stdioTbl, snpTbl, allocTbl, envTbl]

/-- The table of a run whose text head constant is `c`. -/
def tblOfText? (c : Name) : Option Tbl :=
  if c == ``VsaIris.Sym.interpText then some interpTbl
  else if c == ``VsaIris.Sym.stdioText then some stdioTbl
  else if c == ``VsaIris.Sym.snpText then some snpTbl
  else if c == ``VsaIris.Sym.allocText then some allocTbl
  else if c == ``VsaIris.Sym.envText then some envTbl
  else none

/-- The run table of an `SWP` goal, from the head constant of its text. -/
def swpTbl? (ty : Expr) : MetaM (Option Tbl) := do
  let ty := (← whnfR ty).consumeMData
  unless ty.getAppFn.isConstOf ``VsaIris.Sym.SWP do return none
  let some text := ty.getAppArgs[1]? | return none
  let text := if text.isAppOfArity ``HAppend.hAppend 6 then text.getArg! 4 else text
  match text.getAppFn.constName? with
  | some c => return tblOfText? c
  | none => return none

/-- The family of a driver prefix: `it`/`nt`/`st` then the variant letter; a trailing `S`
    (the stdio name at a `pc` shared with the interpreter) names the same family. -/
def kindOfPrefix (p : String) : String :=
  let k := String.ofList (p.toList.drop 2)
  if k.endsWith "S" then String.ofList (k.toList.dropLast) else k

/-! ## Elaboration -/

/-- The declarations the templates are written against. -/
def stepOpens : List OpenDecl :=
  [`Vsa.Sim, `Vsa.MemRepr, `VsaIris.Inst, `VsaIris.MallocFast, `LeanRV64DExecutable,
   `LeanRV64DExecutable.Functions, `Sail, `VsaIris, `VsaIris.Sym].map (OpenDecl.simple · [])

initialize stepCache : IO.Ref (Std.HashMap String Name) ← IO.mkRef {}

private def parseTerm (s : String) : MetaM Syntax := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .ok stx => pure stx
  | .error e => throwError "step lemma: parse error {e}\n{s}"

/-- Elaborate a closed lemma `∀ binders, concl` with the given proof and keep it as an
    auxiliary theorem. -/
def elabLem (L : Lem) : MetaM Name := do
  let tyStx ← parseTerm s!"∀ {L.binders},\n    {L.concl}"
  let valStx ← parseTerm s!"fun {L.binders} =>\n  {L.proof}"
  let (ty, val) ← withLCtx {} {} <|
    withTheReader Core.Context (fun c => { c with currNamespace := `VsaIris.Sym, openDecls := stepOpens }) <|
    Term.TermElabM.run' (ctx := { errToSorry := false }) do
      let ty ← Term.elabType tyStx
      Term.synthesizeSyntheticMVarsNoPostponing
      let ty ← instantiateMVars ty
      let val ← Term.elabTermEnsuringType valStx ty
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (ty, ← instantiateMVars val)
  if ty.hasMVar || val.hasMVar then throwError "step lemma: unassigned metavariables"
  mkAuxLemma [] ty val (kind? := `_step)

/-- The lemma of family `kind` at `pc` for table `t`, or of the table-independent
    families `jalx`/`jalro` (`t` then only supplies the image). -/
def stepLemma (t : Tbl) (kind : String) (pc : Nat) : MetaM (Option Name) := do
  let key := s!"{t.key}/{kind}/{pc}"
  if let some nm := (← stepCache.get)[key]? then
    if (← getEnv).contains nm then return some nm
  if t.skip.any fun r => r.1 ≤ pc ∧ pc < r.2 then return none
  let some w ← wordAt? t.pieces pc | return none
  let L? : Option Lem :=
    if kind == "jalx" then
      match classify t.flavor t.gpv pc w with
      | .jal imm tgt => some (jalxLem pc w tgt imm)
      | _ => none
    else if kind == "jalro" then
      match classify t.flavor t.gpv pc w with
      | .jalrn r => some (jalroLem pc w r)
      | _ => none
    else lemOf t pc w kind
  let some L := L? | return none
  let nm ← elabLem L
  stepCache.modify (·.insert key nm)
  return some nm

/-- The table whose code contains `pc`, preferring `pref`. -/
def tblOfPc (pref : List Tbl) (pc : Nat) : MetaM (Option Tbl) := do
  for t in pref do
    if (← wordAt? t.pieces pc).isSome then return some t
  return none

/-- A named step family as the landed proofs refer to it: `it`, `itD`, …, `itS`
    (the stdio lemma at a `pc` shared with the interpreter), `nt…` (snprintf), `st`
    (allocator and environment helpers), `jalx`, `jalxn`, `jalrn`. -/
def resolveFam (fam : String) (pc : Nat) : MetaM (Option (Tbl × String)) := do
  if fam == "jalx" || fam == "jalxn" then
    return (← tblOfPc tables pc).map (·, "jalx")
  if fam == "jalrn" || fam == "jalro" then return some (snpTbl, "jalro")
  if fam.startsWith "st" then
    return (← tblOfPc [envTbl, allocTbl] pc).map (·, String.ofList (fam.toList.drop 2))
  if fam.startsWith "nt" then return some (snpTbl, String.ofList (fam.toList.drop 2))
  if fam.startsWith "it" then
    let k := String.ofList (fam.toList.drop 2)
    if k.endsWith "S" then return some (stdioTbl, String.ofList (k.toList.dropLast))
    return (← tblOfPc [interpTbl, stdioTbl] pc).map (·, k)
  return none

syntax (name := stepCore) "step_core% " ident num : term

/-- `step% fam pc`: the step lemma `fam_<pc>` of the landed step tables, elaborated from
    the image at `pc`. -/
macro "step% " f:ident n:num : term => `(step_core% $f $n)

@[term_elab stepCore] def elabStepCore : TermElab := fun stx expectedType? => do
  match stx with
  | `(step_core% $f:ident $n:num) =>
    let fam := f.getId.toString
    let pc := n.getNat
    let legacy := (`VsaIris.Sym).str s!"{fam}_{hxw 8 pc}"
    if (← getEnv).contains legacy then return ← Term.elabTerm (mkCIdent legacy) expectedType?
    let some (t, k) ← resolveFam fam pc | throwError "step%: no table for {fam} at {pc}"
    let some nm ← stepLemma t k pc | throwError "step%: no {fam} step at 0x{hx pc}"
    Term.elabTerm (mkCIdent nm) expectedType?
  | _ => throwUnsupportedSyntax

/-! ## Step tables

`#step_table tbl lo hi` elaborates, as ordinary theorems, the step lemma of every family
at every instruction of `tbl`'s code in `[lo, hi)`, under the names the drivers and
proofs use (`it_<pc>`, `itD_<pc>`, …, `st_<pc>`, `nt_<pc>`, `jalx_<pc>`). -/

/-- The families a table offers, in generation order (calls first: their lemmas are
    used by the call steps). -/
def Tbl.kinds (t : Tbl) : List String :=
  match t.flavor with
  | .interp => ["jalx", "", "D", "T", "H", "O"]
  | .stdio => ["jalx", "", "D", "H", "P", "O"]
  | .snp => ["jalx", "jalro", "", "D", "H", "O", "J", "C", "P"]
  | .alloc => ["jalx", ""]

/-- The landed name of family `kind` at `pc` in table `t`. -/
def famName (t : Tbl) (kind : String) (pc : Nat) : MetaM String := do
  let base :=
    if kind == "jalx" then (if t.flavor == .snp then "jalxn" else "jalx")
    else if kind == "jalro" then "jalrn"
    else (match t.flavor with
      | .snp => "nt"
      | .alloc => "st"
      | _ => "it") ++ kind
  -- a stdio lemma at a `pc` the interpreter's table also covers
  let sfx := if t.flavor == .stdio && (← wordAt? interpTbl.pieces pc).isSome then "S" else ""
  return s!"{base}{sfx}_{hxw 8 pc}"

def tblByKey? (k : String) : Option Tbl := tables.find? (·.key == k)

/-- The code addresses of `t` in `[lo, hi)`. -/
def Tbl.pcsIn (t : Tbl) (lo hi : Nat) : MetaM (List Nat) := do
  let ps ← unsafe evalExpr (List Vsa.Sim.TextPiece)
    (mkApp (mkConst ``List [0]) (mkConst ``Vsa.Sim.TextPiece)) (mkConst t.pieces)
  let rs := ps.flatMap (·.ranges)
  return rs.flatMap fun r =>
    ((List.range ((r.2 - r.1) / 4)).map (r.1 + 4 * ·)).filter fun pc =>
      lo ≤ pc ∧ pc < hi ∧ pc < 0x80018be0

open Command in
elab "#step_table " k:ident lo:num hi:num : command => do
  let some t := tblByKey? k.getId.toString | throwError "#step_table: no table {k.getId}"
  let pcs ← liftTermElabM (t.pcsIn lo.getNat hi.getNat)
  for pc in pcs do
    if t.skip.any fun r => r.1 ≤ pc ∧ pc < r.2 then continue
    let some w ← liftTermElabM (wordAt? t.pieces pc) | continue
    for kind in t.kinds do
      let L? : Option Lem :=
        if kind == "jalx" then
          match classify t.flavor t.gpv pc w with
          | .jal imm tgt => some (jalxLem pc w tgt imm)
          | _ => none
        else if kind == "jalro" then
          match classify t.flavor t.gpv pc w with
          | .jalrn r => some (jalroLem pc w r)
          | _ => none
        else lemOf t pc w kind
      let some L := L? | continue
      let nm ← liftTermElabM (famName t kind pc)
      if (← getEnv).contains ((← getCurrNamespace).str nm) then continue
      let src := s!"theorem {nm} {L.binders} :\n    {L.concl} :=\n  {L.proof}"
      match Parser.runParserCategory (← getEnv) `command src with
      | .ok stx => elabCommand stx
      | .error e => throwError "#step_table: parse error {e}\n{src}"

end VsaIris.Sym.StepGen
