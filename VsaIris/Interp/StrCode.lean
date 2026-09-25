import VsaIris.Interp.StrRun
import VsaIris.Vsa.StrlenOwned
import Vsa.Sim.Code.Strcpy

/-!
# The string leaves' code (`strlen`, `strcpy`)

`strlen` (`0x80006cf0`, 212 bytes, H3's `strlenCode`) and `strcpy`
(`0x80006dc4`, 220 bytes) are contiguous in `.text`. `strCode` is both as one
read-only list; VSA's fetch predicates `Code.StrlenLoaded`/`StrcpyLoaded`
(what `chain_facts` consumes) follow from it. `SW` is `SR` at this code. The
step table over `SW` is `StrSteps.lean` (`scripts/gen_str_steps.py`).
-/

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst.Strlen

def strcpyCodeA : List (BitVec 8) :=
  [0xb3#8, 0x67#8, 0xb5#8, 0x00#8, 0x93#8, 0xf7#8, 0x77#8, 0x00#8, 0x63#8, 0x98#8, 0x07#8, 0x0a#8,
   0xb7#8, 0x87#8, 0x7f#8, 0x7f#8, 0x93#8, 0x87#8, 0xf7#8, 0xf7#8, 0x03#8, 0xb7#8, 0x05#8, 0x00#8,
   0x93#8, 0x96#8, 0x07#8, 0x02#8, 0xb3#8, 0x86#8, 0xf6#8, 0x00#8, 0x33#8, 0x78#8, 0xd7#8, 0x00#8,
   0x33#8, 0x08#8, 0xd8#8, 0x00#8, 0x33#8, 0x68#8, 0xe8#8, 0x00#8, 0x33#8, 0x68#8, 0xd8#8, 0x00#8,
   0x93#8, 0x07#8, 0xf0#8, 0xff#8, 0x13#8, 0x06#8, 0x05#8, 0x00#8]

def strcpyCodeB : List (BitVec 8) :=
  [0x63#8, 0x14#8, 0xf8#8, 0x02#8, 0x93#8, 0x85#8, 0x85#8, 0x00#8, 0x23#8, 0x30#8, 0xe6#8, 0x00#8,
   0x03#8, 0xb7#8, 0x05#8, 0x00#8, 0x13#8, 0x06#8, 0x86#8, 0x00#8, 0xb3#8, 0x77#8, 0xd7#8, 0x00#8,
   0xb3#8, 0x87#8, 0xd7#8, 0x00#8, 0xb3#8, 0xe7#8, 0xe7#8, 0x00#8, 0xb3#8, 0xe7#8, 0xd7#8, 0x00#8,
   0xe3#8, 0x80#8, 0x07#8, 0xff#8, 0x83#8, 0xc7#8, 0x05#8, 0x00#8, 0x03#8, 0xc7#8, 0x15#8, 0x00#8,
   0x83#8, 0xc6#8, 0x25#8, 0x00#8, 0x23#8, 0x00#8, 0xf6#8, 0x00#8]

def strcpyCodeC : List (BitVec 8) :=
  [0x63#8, 0x82#8, 0x07#8, 0x04#8, 0xa3#8, 0x00#8, 0xe6#8, 0x00#8, 0x63#8, 0x0e#8, 0x07#8, 0x02#8,
   0x83#8, 0xc7#8, 0x35#8, 0x00#8, 0x23#8, 0x01#8, 0xd6#8, 0x00#8, 0x63#8, 0x88#8, 0x06#8, 0x02#8,
   0x03#8, 0xc7#8, 0x45#8, 0x00#8, 0xa3#8, 0x01#8, 0xf6#8, 0x00#8, 0x63#8, 0x82#8, 0x07#8, 0x02#8,
   0x83#8, 0xc7#8, 0x55#8, 0x00#8, 0x23#8, 0x02#8, 0xe6#8, 0x00#8, 0x63#8, 0x0c#8, 0x07#8, 0x00#8,
   0x03#8, 0xc7#8, 0x65#8, 0x00#8, 0xa3#8, 0x02#8, 0xf6#8, 0x00#8]

def strcpyCodeD : List (BitVec 8) :=
  [0x63#8, 0x86#8, 0x07#8, 0x00#8, 0x23#8, 0x03#8, 0xe6#8, 0x00#8, 0x63#8, 0x12#8, 0x07#8, 0x02#8,
   0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x93#8, 0x07#8, 0x05#8, 0x00#8, 0x03#8, 0xc7#8, 0x05#8, 0x00#8,
   0x93#8, 0x87#8, 0x17#8, 0x00#8, 0x93#8, 0x85#8, 0x15#8, 0x00#8, 0xa3#8, 0x8f#8, 0xe7#8, 0xfe#8,
   0xe3#8, 0x18#8, 0x07#8, 0xfe#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0xa3#8, 0x03#8, 0x06#8, 0x00#8,
   0x67#8, 0x80#8, 0x00#8, 0x00#8]

/-- The 220 code bytes of `strcpy`, in four chunks (as `strlenCode`). -/
def strcpyCode : List (BitVec 8) :=
  strcpyCodeA ++ strcpyCodeB ++ strcpyCodeC ++ strcpyCodeD

abbrev cpyBase : Nat := 0x80006dc4

/-- The code of both string leaves as one read-only list. -/
def strCode : List (Nat × BitVec 8) :=
  codeText codeBase strlenCode ++ codeText cpyBase strcpyCode

/-- The string leaves' symbolic run: `SR` at their code. -/
abbrev SW (live : Nat → Prop) (D : List (Nat × BitVec 8)) (S : Nat → Prop)
    (Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop) :
    BitVec 64 → (Nat → BitVec 64) → Mem → Prop :=
  SR live strCode D S Q

theorem strcpyLoaded_of_code {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ q ∈ memFoot (codeText cpyBase strcpyCode), m[q.1]? = some q.2.2) :
    Code.StrcpyLoaded m := by
  have h' : ∀ a b, (a, b) ∈ codeText cpyBase strcpyCode → m[a]? = some b := by
    intro a b hab
    exact h (a, Iris.DFrac.discard, b)
      (List.mem_map_of_mem (f := fun q => (q.1, Iris.DFrac.discard, q.2)) hab)
  unfold Code.StrcpyLoaded Code.strcpyChunk0 Code.strcpyChunk1 Code.strcpyChunk2
    Code.strcpyChunk3
  repeat' apply And.intro
  all_goals (apply h'; decide)

theorem strlenLoaded_of_str {m : Mem} (h : TextLoaded strCode m) : Code.StrlenLoaded m :=
  strlenLoaded_of_code fun q hq => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact h p (List.mem_append_left _ hp)

theorem strcpyLoaded_of_str {m : Mem} (h : TextLoaded strCode m) : Code.StrcpyLoaded m :=
  strcpyLoaded_of_code fun q hq => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    exact h p (List.mem_append_right _ hp)

/-- `strcpy`'s code is the image's. -/
theorem strcpyCode_text : Newlib.TextAt cpyBase strcpyCode := by decide +kernel

/-- The `snez` of `strlen` (`0x80006d64`) lies in the code. -/
theorem str_code_80006d64 :
    ∀ p ∈ VsaIris.codeFoot 0x80006d64 [0x33#8, 0x35#8, 0xf0#8, 0x00#8], (p.1, p.2.2) ∈ strCode := by
  intro p hp
  simp only [VsaIris.codeFoot, List.zipIdx, List.zipIdx_cons, List.zipIdx_nil, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl <;>
    exact List.mem_append_left _ (by decide)

end VsaIris.Sym
