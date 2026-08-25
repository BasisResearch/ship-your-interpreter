import Vsa.Sim.BlockDecode
import Vsa.Sim.BlockTactics
import Vsa.Sim.NegBlockProto

/-!
# `BlockGen` — the `#gen_block` meta-generator (Stage D)

Stage D of `experiments/block-abstractions-impl-plan.md`: authoring a basic
block should be *write the `(pc, word)` list and (optionally) the terminator* —
the `BBlock` def is then generated, its body reusing Stage B's `mkLine` so every
`kind/rd/rs1/rs2/imm` is *derived from the word* rather than transcribed.

## D1a — `#gen_block` (BBlock generation, REQUIRED)

```
#gen_block <name>
  [(<pc₀>, <word₀>), (<pc₁>, <word₁>), …]        -- straight-line body
  term <tinstrTerm>                              -- OPTIONAL terminator (hand TInstr)
```

emits

```
def <name> : BBlock := { body := [mkLine <pc₀> <word₀>, …], term := <termOpt> }
```

The `(pc, word)` inputs are ordinary numeric (hex) literals. The generator's
OUTPUT is exactly what a human writes by hand (a `mkLine`-based `BBlock`, cf.
`negLoadStoreBlk`), so a generated block is auditable and `rfl`-equal to the
hand block it replaces (see the D2 regeneration check below).

Terminators keep their hand `TInstr` literal (the B-type / J-type immediate
scatter is out of scope for the reflected decoder, exactly as in Stage B); pass
it via the optional `terminator` clause.

## D2 — regeneration check

`#gen_block negLoadStoreBlkGen …` regenerates `negLoadStoreBlk`; the
`example : negLoadStoreBlkGen = negLoadStoreBlk := by rfl` below is the diff (the
two blocks are *definitionally equal*, so the generator is transcription-free).

## D1b — soundness-theorem skeleton (STRETCH)

`#gen_block_sound` additionally emits a `theorem <name>_sound` for a
*straight-line, load-free, fall-through* block: it `obtain`s
`bblock_sound_bt <name> …`, runs `block_facts` (whose leaves are then all
mechanical — no memory/guard leaves for a load-free fall-through block), and
exposes the computed PC / frame. The data-dependent register projections stay as
the theorem's residual goals / the caller's job — they cannot be synthesised from
`(pc, word)` alone (the plan acknowledges this). Demonstrated on `genDemoBlk`
below (three `addi`s, fall-through).
-/

open Lean Elab Command Term Meta
open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Vsa.Machine (MState Config Step Steps)

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

/-! ## D1a — `#gen_block` -/

/-- One `(pc, word)` pair in a `#gen_block` body list. -/
syntax gbPair := "(" term:max ", " term:max ")"

/-- `#gen_block <name> [ (pc,word), … ] (term <tinstr>)?` — emit a `BBlock`
`def` whose body is a `mkLine`-per-pair list. -/
syntax (name := genBlockCmd)
  "#gen_block " ident " [" gbPair,* "]" (" terminator " term)? : command

/-- Build the `[mkLine pc₀ w₀, …]` body-list syntax from the parsed pairs. -/
private def mkBodyList (pairs : Array (TSyntax ``gbPair)) :
    CommandElabM (TSyntax `term) := do
  let lines ← pairs.mapM fun p => do
    match p with
    | `(gbPair| ($pc, $w)) => `(mkLine $pc $w)
    | _ => throwErrorAt p "malformed (pc, word) pair"
  `([$lines,*])

@[command_elab genBlockCmd]
def elabGenBlock : CommandElab := fun stx => do
  match stx with
  | `(command| #gen_block $name:ident [ $pairs,* ] $[terminator $t?]?) => do
    let body ← mkBodyList pairs.getElems
    let termStx : TSyntax `term ←
      match t? with
      | some t => `(some $t)
      | none   => `(none)
    let cmd ← `(command|
      def $name : BBlock := { body := $body, term := $termStx })
    elabCommand cmd
  | _ => throwUnsupportedSyntax

/-! ## D1b — `#gen_block_sound` (straight-line, load-free, fall-through) -/

/-- `#gen_block_sound <name> [ (pc,word), … ]` — emit the `BBlock` def AND a
soundness `theorem <name>_sound` for a load-free fall-through block. The
`block_facts` leaves for such a block are all mechanical (no `MemFacts`, no
terminator guard), so the emitted proof closes them with `<;> assumption` and
exposes the `Steps` chain, the computed end PC, the frame, and `GHolds`. The
per-register outputs stay as `GHolds σ' (runGM …)` for the caller to project. -/
syntax (name := genBlockSoundCmd)
  "#gen_block_sound " ident " [" gbPair,* "]" : command

@[command_elab genBlockSoundCmd]
def elabGenBlockSound : CommandElab := fun stx => do
  match stx with
  | `(command| #gen_block_sound $name:ident [ $pairs,* ]) => do
    -- emit the block def
    let body ← mkBodyList pairs.getElems
    let defCmd ← `(command|
      def $name : BBlock := { body := $body, term := none })
    elabCommand defCmd
    -- emit the soundness skeleton
    let soundName := mkIdent (name.getId.appendAfter "_sound")
    let thmCmd ← `(command|
      theorem $soundName (σ : MState) (i u : Nat) (pc0 vm : BitVec 64)
          (L : GRegs)
          (hG : GoodState σ)
          (hpc : σ.regs.get? Register.PC = some pc0)
          (hmi : σ.regs.get? Register.minstret = some vm)
          (hL : GHolds σ L) (hkeys : KeysOK (keysG L))
          (hfacts : BBlockFacts σ.mem σ.mem L [] $name)
          (hwf : BBlockOK pc0 (keysG L) $name)
          (hi : i < 2) :
          ∃ (σ' : MState) (i' : Nat),
            Vsa.Machine.Steps ⟨σ, i, u⟩ ⟨σ', i', u + blenB $name⟩ ∧ i' < 2 ∧
            GoodState σ' ∧
            σ'.regs.get? Register.PC = some (endPCB pc0 $name L []) ∧
            GHolds σ' (runGM ($name).body L []) ∧
            (∀ R : Register, (∀ rr ∈ noiseRegs, (rr == R) = false) →
              (∀ n ∈ wrRegsM ($name).body, (gprReg n == R) = false) →
              σ'.regs.get? R = σ.regs.get? R) := by
        obtain ⟨σ', i', hsteps, hi', hG', _hmem', _hout', hpc', _hmi', hGH, hframe⟩ :=
          bblock_sound_bt $name σ i u pc0 vm L [] hG hpc hmi hL hkeys hfacts hwf hi
        exact ⟨σ', i', hsteps, hi', hG', hpc', hGH, hframe⟩)
    elabCommand thmCmd
  | _ => throwUnsupportedSyntax

/-! ## D2 — regeneration check: regenerate `negLoadStoreBlk`, diff = `rfl`. -/

#gen_block negLoadStoreBlkGen
  [(0x800039ac#64, 0x09813583#32),   -- ld a1,152(sp)
   (0x800039b0#64, 0x0a013703#32),   -- ld a4,160(sp)
   (0x800039b4#64, 0x09012503#32),   -- lw a0,144(sp)
   (0x800039b8#64, 0x0ed13823#32),   -- sd a3,240(sp)
   (0x800039bc#64, 0x0eb13c23#32),   -- sd a1,248(sp)
   (0x800039c0#64, 0x10e13023#32)]  -- sd a4,256(sp)

/-- **D2**: the generated block is *definitionally equal* to the hand block —
`mkLine`-derived fields match transcription exactly, so the generator is sound
against the audited hand block. -/
example : negLoadStoreBlkGen = negLoadStoreBlk := by rfl

/-! D2, also on the prologue *body* (terminator supplied by hand). -/
#gen_block negPrologueBodyGen
  [(0x800035ec#64, 0x00842703#32),   -- lw a4,8(s0)
   (0x800035f0#64, 0x00c00793#32),   -- li a5,12
   (0x800035f4#64, 0x09013683#32)]   -- ld a3,144(sp)
  terminator ⟨0x800035f8#64, 0x3af70a63#32, 0x63#8, 0x0a#8, 0xf7#8, 0x3a#8,
    .br bop.BEQ true, 14, 15, 0x03b4#13, 0#21, 0#12⟩

example : negPrologueBodyGen = negPrologueBlk := by rfl

/-! ## D1b demo — a straight-line, load-free, fall-through block + soundness. -/

/-! Three `addi`s at a fabricated pc range, fall-through: `addi x5,x0,1;
addi x6,x0,2; addi x7,x0,3`. Load-free and terminator-free, so its
`block_facts` leaves are all mechanical — the ideal `#gen_block_sound` target. -/
#gen_block_sound genDemoBlk
  [(0x80000000#64, 0x00100293#32),   -- addi x5,x0,1
   (0x80000004#64, 0x00200313#32),   -- addi x6,x0,2
   (0x80000008#64, 0x00300393#32)]   -- addi x7,x0,3

end Vsa.Sim
