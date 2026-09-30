import VsaIris.Vsa.BinImg
import VsaIris.Vsa.JalSite
import Vsa.Sim.OutputAliasDecode

namespace VsaIris.Newlib.Sites

open VsaIris.Inst

abbrev exitCodeBase : Nat := 0x80004764
def exitCode : List (BitVec 8) :=
  [0x13#8, 0x01#8, 0x01#8, 0xff#8, 0x93#8, 0x05#8, 0x00#8, 0x00#8, 0x23#8, 0x30#8, 0x81#8, 0x00#8, 0x23#8, 0x34#8, 0x11#8, 0x00#8, 0x13#8, 0x04#8, 0x05#8, 0x00#8, 0xef#8, 0x20#8, 0x10#8, 0x13#8, 0x83#8, 0xb7#8, 0x01#8, 0x4a#8, 0x63#8, 0x84#8, 0x07#8, 0x00#8, 0xe7#8, 0x80#8, 0x07#8, 0x00#8, 0x13#8, 0x05#8, 0x04#8, 0x00#8, 0xef#8, 0xb0#8, 0x5f#8, 0x9f#8]

theorem exitCode_text : TextAt exitCodeBase exitCode := by decide +kernel

def exitCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 44 → m[exitCodeBase + k]? = some (exitCode.getD k 0)

abbrev exitCodeEBase : Nat := 0x80000180
def exitCodeE : List (BitVec 8) :=
  [0x13#8, 0x17#8, 0x05#8, 0x02#8, 0x93#8, 0x57#8, 0xf7#8, 0x01#8, 0x93#8, 0xe7#8, 0x17#8, 0x00#8, 0x17#8, 0xb7#8, 0x01#8, 0x00#8, 0x23#8, 0x3a#8, 0xf7#8, 0xb6#8, 0x6f#8, 0x00#8, 0x00#8, 0x00#8]

theorem exitCodeE_text : TextAt exitCodeEBase exitCodeE := by decide +kernel

def exitJalExitE : JalSite where
  pc := 0x8000478c
  b0 := 0xef#8
  b1 := 0xb0#8
  b2 := 0x5f#8
  b3 := 0x9f#8
  w := 0x9f5fb0ef#32
  imm := 0x1fb9f4#21
  tgt := 0x80000180#64

theorem exitJalExitE_cert : exitJalExitE.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_9f5fb0ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

end VsaIris.Newlib.Sites

namespace Vsa.Sim.DecodeTable

alias decode_72c0406f := Vsa.Sim.OutputAliasDecode.decode_72c0406f

end Vsa.Sim.DecodeTable

namespace VsaIris.Newlib.Sites

open VsaIris.Inst

abbrev mainErrCodeBase : Nat := 0x800045ec
def mainErrCode : List (BitVec 8) :=
  [0x63#8, 0x1a#8, 0x05#8, 0x00#8, 0x83#8, 0x30#8, 0x81#8, 0x2f#8, 0x03#8, 0x34#8, 0x01#8, 0x2f#8, 0x13#8, 0x01#8, 0x01#8, 0x30#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8, 0x83#8, 0x37#8, 0x04#8, 0x00#8, 0x13#8, 0x06#8, 0x01#8, 0x1f#8, 0x97#8, 0x55#8, 0x01#8, 0x00#8, 0x93#8, 0x85#8, 0x85#8, 0xfd#8, 0x03#8, 0xb5#8, 0x87#8, 0x01#8, 0xef#8, 0x10#8, 0xd0#8, 0x3a#8, 0x13#8, 0x05#8, 0x60#8, 0x04#8, 0x6f#8, 0xf0#8, 0x5f#8, 0xfd#8]

theorem mainErrCode_text : TextAt mainErrCodeBase mainErrCode := by decide +kernel

def mainErrCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 52 → m[mainErrCodeBase + k]? = some (mainErrCode.getD k 0)

theorem mainErrCode_len : mainErrCode.length = 52 := by decide +kernel

theorem mainErrCodeLoaded_of {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot mainErrCodeBase mainErrCode, m[p.1]? = some p.2.2) : mainErrCodeLoaded m :=
  fun k hk => loaded_of_foot h k (by rw [mainErrCode_len]; exact hk)

theorem mainErrCode_at_800045ec {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x800045ec : Nat)]? = some (0x63 : BitVec 8) ∧
    m[(0x800045ed : Nat)]? = some (0x1a : BitVec 8) ∧
    m[(0x800045ee : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x800045ef : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

theorem mainErrCode_at_800045f0 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x800045f0 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x800045f1 : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x800045f2 : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x800045f3 : Nat)]? = some (0x2f : BitVec 8) :=
  ⟨h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

theorem mainErrCode_at_800045f4 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x800045f4 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x800045f5 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x800045f6 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x800045f7 : Nat)]? = some (0x2f : BitVec 8) :=
  ⟨h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)⟩

theorem mainErrCode_at_800045f8 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x800045f8 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x800045f9 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x800045fa : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x800045fb : Nat)]? = some (0x30 : BitVec 8) :=
  ⟨h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)⟩

theorem mainErrCode_at_800045fc {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x800045fc : Nat)]? = some (0x67 : BitVec 8) ∧
    m[(0x800045fd : Nat)]? = some (0x80 : BitVec 8) ∧
    m[(0x800045fe : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x800045ff : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide)⟩

theorem mainErrCode_at_80004600 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x80004600 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80004601 : Nat)]? = some (0x37 : BitVec 8) ∧
    m[(0x80004602 : Nat)]? = some (0x04 : BitVec 8) ∧
    m[(0x80004603 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide)⟩

theorem mainErrCode_at_80004604 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x80004604 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80004605 : Nat)]? = some (0x06 : BitVec 8) ∧
    m[(0x80004606 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80004607 : Nat)]? = some (0x1f : BitVec 8) :=
  ⟨h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide)⟩

theorem mainErrCode_at_80004608 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x80004608 : Nat)]? = some (0x97 : BitVec 8) ∧
    m[(0x80004609 : Nat)]? = some (0x55 : BitVec 8) ∧
    m[(0x8000460a : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000460b : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide)⟩

theorem mainErrCode_at_8000460c {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x8000460c : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x8000460d : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x8000460e : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x8000460f : Nat)]? = some (0xfd : BitVec 8) :=
  ⟨h 32 (by decide), h 33 (by decide), h 34 (by decide), h 35 (by decide)⟩

theorem mainErrCode_at_80004610 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x80004610 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80004611 : Nat)]? = some (0xb5 : BitVec 8) ∧
    m[(0x80004612 : Nat)]? = some (0x87 : BitVec 8) ∧
    m[(0x80004613 : Nat)]? = some (0x01 : BitVec 8) :=
  ⟨h 36 (by decide), h 37 (by decide), h 38 (by decide), h 39 (by decide)⟩

theorem mainErrCode_at_80004618 {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x80004618 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80004619 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000461a : Nat)]? = some (0x60 : BitVec 8) ∧
    m[(0x8000461b : Nat)]? = some (0x04 : BitVec 8) :=
  ⟨h 44 (by decide), h 45 (by decide), h 46 (by decide), h 47 (by decide)⟩

theorem mainErrCode_at_8000461c {m : Std.ExtHashMap Nat (BitVec 8)} (h : mainErrCodeLoaded m) :
    m[(0x8000461c : Nat)]? = some (0x6f : BitVec 8) ∧
    m[(0x8000461d : Nat)]? = some (0xf0 : BitVec 8) ∧
    m[(0x8000461e : Nat)]? = some (0x5f : BitVec 8) ∧
    m[(0x8000461f : Nat)]? = some (0xfd : BitVec 8) :=
  ⟨h 48 (by decide), h 49 (by decide), h 50 (by decide), h 51 (by decide)⟩

abbrev crt0JCodeBase : Nat := 0x80000038
def crt0JCode : List (BitVec 8) :=
  [0x6f#8, 0x40#8, 0xc0#8, 0x72#8]

theorem crt0JCode_text : TextAt crt0JCodeBase crt0JCode := by decide +kernel

def crt0JCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 4 → m[crt0JCodeBase + k]? = some (crt0JCode.getD k 0)

theorem crt0JCode_len : crt0JCode.length = 4 := by decide +kernel

theorem crt0JCodeLoaded_of {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot crt0JCodeBase crt0JCode, m[p.1]? = some p.2.2) : crt0JCodeLoaded m :=
  fun k hk => loaded_of_foot h k (by rw [crt0JCode_len]; exact hk)

theorem crt0JCode_at_80000038 {m : Std.ExtHashMap Nat (BitVec 8)} (h : crt0JCodeLoaded m) :
    m[(0x80000038 : Nat)]? = some (0x6f : BitVec 8) ∧
    m[(0x80000039 : Nat)]? = some (0x40 : BitVec 8) ∧
    m[(0x8000003a : Nat)]? = some (0xc0 : BitVec 8) ∧
    m[(0x8000003b : Nat)]? = some (0x72 : BitVec 8) :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

abbrev interpLandCodeBase : Nat := 0x80004428
def interpLandCode : List (BitVec 8) :=
  [0x63#8, 0x10#8, 0x05#8, 0x0e#8, 0x83#8, 0x37#8, 0x01#8, 0x01#8, 0x93#8, 0x0a#8, 0x05#8, 0x00#8, 0x63#8, 0x50#8, 0xf0#8, 0x0e#8, 0x83#8, 0x37#8, 0x01#8, 0x01#8, 0x03#8, 0x34#8, 0x81#8, 0x01#8, 0x13#8, 0x8b#8, 0x01#8, 0x46#8, 0x13#8, 0x99#8, 0x37#8, 0x00#8, 0x33#8, 0x09#8, 0x24#8, 0x01#8, 0x93#8, 0x09#8, 0x30#8, 0x00#8, 0x13#8, 0x0a#8, 0x10#8, 0x00#8, 0x6f#8, 0x00#8, 0x80#8, 0x03#8, 0x13#8, 0x05#8, 0x81#8, 0x05#8, 0xef#8, 0xe0#8, 0x0f#8, 0xb9#8, 0x83#8, 0x37#8, 0x01#8, 0x00#8, 0x93#8, 0x06#8, 0x81#8, 0x05#8, 0x93#8, 0x85#8, 0x04#8, 0x00#8, 0x03#8, 0xb6#8, 0x07#8, 0x00#8, 0x13#8, 0x85#8, 0x07#8, 0x00#8, 0xef#8, 0xf0#8, 0xdf#8, 0xb6#8, 0x63#8, 0x04#8, 0x35#8, 0x0d#8, 0x1b#8, 0x05#8, 0xf5#8, 0xff#8, 0x63#8, 0x72#8, 0xaa#8, 0x0e#8, 0x13#8, 0x04#8, 0x84#8, 0x00#8, 0x63#8, 0x06#8, 0x24#8, 0x09#8, 0x83#8, 0x37#8, 0x81#8, 0x00#8, 0x83#8, 0x34#8, 0x04#8, 0x00#8, 0xe3#8, 0x82#8, 0x07#8, 0xfc#8, 0x83#8, 0xa7#8, 0x04#8, 0x00#8, 0xe3#8, 0x9e#8, 0x07#8, 0xfa#8, 0x83#8, 0x37#8, 0x01#8, 0x00#8, 0x03#8, 0xb6#8, 0x84#8, 0x00#8, 0x13#8, 0x05#8, 0x01#8, 0x04#8, 0x83#8, 0xb6#8, 0x07#8, 0x00#8, 0x93#8, 0x85#8, 0x07#8, 0x00#8, 0xef#8, 0xe0#8, 0x1f#8, 0xcb#8, 0x83#8, 0x27#8, 0x01#8, 0x04#8, 0x13#8, 0x05#8, 0x01#8, 0x02#8, 0x63#8, 0x8c#8, 0x07#8, 0x02#8, 0x83#8, 0x37#8, 0x0b#8, 0x00#8, 0x83#8, 0x36#8, 0x01#8, 0x04#8, 0x03#8, 0x37#8, 0x81#8, 0x04#8, 0x83#8, 0xb5#8, 0x07#8, 0x01#8, 0x83#8, 0x37#8, 0x01#8, 0x05#8, 0x23#8, 0x30#8, 0xd1#8, 0x02#8, 0x23#8, 0x34#8, 0xe1#8, 0x02#8, 0x23#8, 0x38#8, 0xf1#8, 0x02#8, 0xef#8, 0xe0#8, 0x8f#8, 0xc1#8, 0x83#8, 0x37#8, 0x0b#8, 0x00#8, 0x13#8, 0x05#8, 0xa0#8, 0x00#8, 0x83#8, 0xb5#8, 0x07#8, 0x01#8, 0xef#8, 0x10#8, 0xd0#8, 0x5e#8, 0x13#8, 0x04#8, 0x84#8, 0x00#8, 0x63#8, 0x0c#8, 0x24#8, 0x01#8, 0x83#8, 0x34#8, 0x04#8, 0x00#8, 0x6f#8, 0xf0#8, 0x5f#8, 0xf9#8, 0x83#8, 0x37#8, 0x01#8, 0x00#8, 0x93#8, 0x0a#8, 0x10#8, 0x00#8, 0x23#8, 0xa4#8, 0x07#8, 0x00#8, 0x83#8, 0x30#8, 0x81#8, 0x0a#8, 0x03#8, 0x34#8, 0x01#8, 0x0a#8, 0x83#8, 0x34#8, 0x81#8, 0x09#8, 0x03#8, 0x39#8, 0x01#8, 0x09#8, 0x83#8, 0x39#8, 0x81#8, 0x08#8, 0x03#8, 0x3a#8, 0x01#8, 0x08#8, 0x03#8, 0x3b#8, 0x01#8, 0x07#8, 0x13#8, 0x85#8, 0x0a#8, 0x00#8, 0x83#8, 0x3a#8, 0x81#8, 0x07#8, 0x13#8, 0x01#8, 0x01#8, 0x0b#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8]

theorem interpLandCode_text : TextAt interpLandCodeBase interpLandCode := by decide +kernel

def interpLandCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 280 → m[interpLandCodeBase + k]? = some (interpLandCode.getD k 0)

theorem interpLandCode_len : interpLandCode.length = 280 := by decide +kernel

theorem interpLandCodeLoaded_of {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot interpLandCodeBase interpLandCode, m[p.1]? = some p.2.2) : interpLandCodeLoaded m :=
  fun k hk => loaded_of_foot h k (by rw [interpLandCode_len]; exact hk)

theorem interpLandCode_at_80004428 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004428 : Nat)]? = some (0x63 : BitVec 8) ∧
    m[(0x80004429 : Nat)]? = some (0x10 : BitVec 8) ∧
    m[(0x8000442a : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000442b : Nat)]? = some (0x0e : BitVec 8) :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

theorem interpLandCode_at_80004508 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004508 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80004509 : Nat)]? = some (0x37 : BitVec 8) ∧
    m[(0x8000450a : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000450b : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 224 (by decide), h 225 (by decide), h 226 (by decide), h 227 (by decide)⟩

theorem interpLandCode_at_8000450c {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x8000450c : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x8000450d : Nat)]? = some (0x0a : BitVec 8) ∧
    m[(0x8000450e : Nat)]? = some (0x10 : BitVec 8) ∧
    m[(0x8000450f : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 228 (by decide), h 229 (by decide), h 230 (by decide), h 231 (by decide)⟩

theorem interpLandCode_at_80004510 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004510 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80004511 : Nat)]? = some (0xa4 : BitVec 8) ∧
    m[(0x80004512 : Nat)]? = some (0x07 : BitVec 8) ∧
    m[(0x80004513 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 232 (by decide), h 233 (by decide), h 234 (by decide), h 235 (by decide)⟩

theorem interpLandCode_at_80004514 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004514 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80004515 : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x80004516 : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x80004517 : Nat)]? = some (0x0a : BitVec 8) :=
  ⟨h 236 (by decide), h 237 (by decide), h 238 (by decide), h 239 (by decide)⟩

theorem interpLandCode_at_80004518 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004518 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80004519 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x8000451a : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000451b : Nat)]? = some (0x0a : BitVec 8) :=
  ⟨h 240 (by decide), h 241 (by decide), h 242 (by decide), h 243 (by decide)⟩

theorem interpLandCode_at_8000451c {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x8000451c : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x8000451d : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x8000451e : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x8000451f : Nat)]? = some (0x09 : BitVec 8) :=
  ⟨h 244 (by decide), h 245 (by decide), h 246 (by decide), h 247 (by decide)⟩

theorem interpLandCode_at_80004520 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004520 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80004521 : Nat)]? = some (0x39 : BitVec 8) ∧
    m[(0x80004522 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80004523 : Nat)]? = some (0x09 : BitVec 8) :=
  ⟨h 248 (by decide), h 249 (by decide), h 250 (by decide), h 251 (by decide)⟩

theorem interpLandCode_at_80004524 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004524 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80004525 : Nat)]? = some (0x39 : BitVec 8) ∧
    m[(0x80004526 : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x80004527 : Nat)]? = some (0x08 : BitVec 8) :=
  ⟨h 252 (by decide), h 253 (by decide), h 254 (by decide), h 255 (by decide)⟩

theorem interpLandCode_at_80004528 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004528 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80004529 : Nat)]? = some (0x3a : BitVec 8) ∧
    m[(0x8000452a : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000452b : Nat)]? = some (0x08 : BitVec 8) :=
  ⟨h 256 (by decide), h 257 (by decide), h 258 (by decide), h 259 (by decide)⟩

theorem interpLandCode_at_8000452c {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x8000452c : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x8000452d : Nat)]? = some (0x3b : BitVec 8) ∧
    m[(0x8000452e : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000452f : Nat)]? = some (0x07 : BitVec 8) :=
  ⟨h 260 (by decide), h 261 (by decide), h 262 (by decide), h 263 (by decide)⟩

theorem interpLandCode_at_80004530 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004530 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80004531 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80004532 : Nat)]? = some (0x0a : BitVec 8) ∧
    m[(0x80004533 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 264 (by decide), h 265 (by decide), h 266 (by decide), h 267 (by decide)⟩

theorem interpLandCode_at_80004534 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004534 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80004535 : Nat)]? = some (0x3a : BitVec 8) ∧
    m[(0x80004536 : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x80004537 : Nat)]? = some (0x07 : BitVec 8) :=
  ⟨h 268 (by decide), h 269 (by decide), h 270 (by decide), h 271 (by decide)⟩

theorem interpLandCode_at_80004538 {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x80004538 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80004539 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000453a : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x8000453b : Nat)]? = some (0x0b : BitVec 8) :=
  ⟨h 272 (by decide), h 273 (by decide), h 274 (by decide), h 275 (by decide)⟩

theorem interpLandCode_at_8000453c {m : Std.ExtHashMap Nat (BitVec 8)} (h : interpLandCodeLoaded m) :
    m[(0x8000453c : Nat)]? = some (0x67 : BitVec 8) ∧
    m[(0x8000453d : Nat)]? = some (0x80 : BitVec 8) ∧
    m[(0x8000453e : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x8000453f : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 276 (by decide), h 277 (by decide), h 278 (by decide), h 279 (by decide)⟩

def mainJalFprintf : JalSite where
  pc := 0x80004614
  b0 := 0xef#8
  b1 := 0x10#8
  b2 := 0xd0#8
  b3 := 0x3a#8
  w := 0x3ad010ef#32
  imm := 0x1bac#21
  tgt := 0x800061c0#64

theorem mainJalFprintf_cert : mainJalFprintf.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_3ad010ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

abbrev rtErrCodeBase : Nat := 0x80002da8
def rtErrCode : List (BitVec 8) :=
  [0x13#8, 0x01#8, 0x01#8, 0xf2#8, 0x23#8, 0x38#8, 0x81#8, 0x0c#8, 0x23#8, 0x34#8, 0x91#8, 0x0c#8, 0x13#8, 0x04#8, 0x05#8, 0x00#8, 0x93#8, 0x84#8, 0x05#8, 0x00#8, 0x13#8, 0x05#8, 0x01#8, 0x00#8, 0x93#8, 0x05#8, 0x00#8, 0x0c#8, 0x23#8, 0x3c#8, 0x11#8, 0x0c#8, 0xef#8, 0x20#8, 0xd0#8, 0x67#8, 0x93#8, 0x05#8, 0x00#8, 0x10#8, 0x13#8, 0x07#8, 0x01#8, 0x00#8, 0x93#8, 0x86#8, 0x04#8, 0x00#8, 0x13#8, 0x05#8, 0x04#8, 0x0e#8, 0x17#8, 0x66#8, 0x01#8, 0x00#8, 0x13#8, 0x06#8, 0xc6#8, 0x53#8, 0xef#8, 0x20#8, 0x10#8, 0x66#8, 0x13#8, 0x05#8, 0x04#8, 0x01#8, 0x93#8, 0x05#8, 0x10#8, 0x00#8, 0xef#8, 0x40#8, 0xc0#8, 0x24#8]

theorem rtErrCode_text : TextAt rtErrCodeBase rtErrCode := by decide +kernel

def rtErrCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 76 → m[rtErrCodeBase + k]? = some (rtErrCode.getD k 0)

theorem rtErrCode_len : rtErrCode.length = 76 := by decide +kernel

theorem rtErrCodeLoaded_of {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot rtErrCodeBase rtErrCode, m[p.1]? = some p.2.2) : rtErrCodeLoaded m :=
  fun k hk => loaded_of_foot h k (by rw [rtErrCode_len]; exact hk)

theorem rtErrCode_at_80002da8 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002da8 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002da9 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80002daa : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80002dab : Nat)]? = some (0xf2 : BitVec 8) :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

theorem rtErrCode_at_80002dac {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dac : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80002dad : Nat)]? = some (0x38 : BitVec 8) ∧
    m[(0x80002dae : Nat)]? = some (0x81 : BitVec 8) ∧
    m[(0x80002daf : Nat)]? = some (0x0c : BitVec 8) :=
  ⟨h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

theorem rtErrCode_at_80002db0 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002db0 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80002db1 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80002db2 : Nat)]? = some (0x91 : BitVec 8) ∧
    m[(0x80002db3 : Nat)]? = some (0x0c : BitVec 8) :=
  ⟨h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)⟩

theorem rtErrCode_at_80002db4 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002db4 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002db5 : Nat)]? = some (0x04 : BitVec 8) ∧
    m[(0x80002db6 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002db7 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)⟩

theorem rtErrCode_at_80002db8 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002db8 : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x80002db9 : Nat)]? = some (0x84 : BitVec 8) ∧
    m[(0x80002dba : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dbb : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide)⟩

theorem rtErrCode_at_80002dbc {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dbc : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002dbd : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dbe : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80002dbf : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide)⟩

theorem rtErrCode_at_80002dc0 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dc0 : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x80002dc1 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dc2 : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x80002dc3 : Nat)]? = some (0x0c : BitVec 8) :=
  ⟨h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide)⟩

theorem rtErrCode_at_80002dc4 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dc4 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80002dc5 : Nat)]? = some (0x3c : BitVec 8) ∧
    m[(0x80002dc6 : Nat)]? = some (0x11 : BitVec 8) ∧
    m[(0x80002dc7 : Nat)]? = some (0x0c : BitVec 8) :=
  ⟨h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide)⟩

theorem rtErrCode_at_80002dcc {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dcc : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x80002dcd : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dce : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x80002dcf : Nat)]? = some (0x10 : BitVec 8) :=
  ⟨h 36 (by decide), h 37 (by decide), h 38 (by decide), h 39 (by decide)⟩

theorem rtErrCode_at_80002dd0 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dd0 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002dd1 : Nat)]? = some (0x07 : BitVec 8) ∧
    m[(0x80002dd2 : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80002dd3 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 40 (by decide), h 41 (by decide), h 42 (by decide), h 43 (by decide)⟩

theorem rtErrCode_at_80002dd4 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dd4 : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x80002dd5 : Nat)]? = some (0x86 : BitVec 8) ∧
    m[(0x80002dd6 : Nat)]? = some (0x04 : BitVec 8) ∧
    m[(0x80002dd7 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 44 (by decide), h 45 (by decide), h 46 (by decide), h 47 (by decide)⟩

theorem rtErrCode_at_80002dd8 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dd8 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002dd9 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dda : Nat)]? = some (0x04 : BitVec 8) ∧
    m[(0x80002ddb : Nat)]? = some (0x0e : BitVec 8) :=
  ⟨h 48 (by decide), h 49 (by decide), h 50 (by decide), h 51 (by decide)⟩

theorem rtErrCode_at_80002ddc {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002ddc : Nat)]? = some (0x17 : BitVec 8) ∧
    m[(0x80002ddd : Nat)]? = some (0x66 : BitVec 8) ∧
    m[(0x80002dde : Nat)]? = some (0x01 : BitVec 8) ∧
    m[(0x80002ddf : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 52 (by decide), h 53 (by decide), h 54 (by decide), h 55 (by decide)⟩

theorem rtErrCode_at_80002de0 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002de0 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002de1 : Nat)]? = some (0x06 : BitVec 8) ∧
    m[(0x80002de2 : Nat)]? = some (0xc6 : BitVec 8) ∧
    m[(0x80002de3 : Nat)]? = some (0x53 : BitVec 8) :=
  ⟨h 56 (by decide), h 57 (by decide), h 58 (by decide), h 59 (by decide)⟩

theorem rtErrCode_at_80002de8 {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002de8 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80002de9 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dea : Nat)]? = some (0x04 : BitVec 8) ∧
    m[(0x80002deb : Nat)]? = some (0x01 : BitVec 8) :=
  ⟨h 64 (by decide), h 65 (by decide), h 66 (by decide), h 67 (by decide)⟩

theorem rtErrCode_at_80002dec {m : Std.ExtHashMap Nat (BitVec 8)} (h : rtErrCodeLoaded m) :
    m[(0x80002dec : Nat)]? = some (0x93 : BitVec 8) ∧
    m[(0x80002ded : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80002dee : Nat)]? = some (0x10 : BitVec 8) ∧
    m[(0x80002def : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 68 (by decide), h 69 (by decide), h 70 (by decide), h 71 (by decide)⟩

abbrev ljCodeBase : Nat := 0x8000703c
def ljCode : List (BitVec 8) :=
  [0x83#8, 0x30#8, 0x05#8, 0x00#8, 0x03#8, 0x34#8, 0x85#8, 0x00#8, 0x83#8, 0x34#8, 0x05#8, 0x01#8, 0x03#8, 0x39#8, 0x85#8, 0x01#8, 0x83#8, 0x39#8, 0x05#8, 0x02#8, 0x03#8, 0x3a#8, 0x85#8, 0x02#8, 0x83#8, 0x3a#8, 0x05#8, 0x03#8, 0x03#8, 0x3b#8, 0x85#8, 0x03#8, 0x83#8, 0x3b#8, 0x05#8, 0x04#8, 0x03#8, 0x3c#8, 0x85#8, 0x04#8, 0x83#8, 0x3c#8, 0x05#8, 0x05#8, 0x03#8, 0x3d#8, 0x85#8, 0x05#8, 0x83#8, 0x3d#8, 0x05#8, 0x06#8, 0x03#8, 0x31#8, 0x85#8, 0x06#8, 0x13#8, 0xb5#8, 0x15#8, 0x00#8, 0x33#8, 0x05#8, 0xb5#8, 0x00#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8]

theorem ljCode_text : TextAt ljCodeBase ljCode := by decide +kernel

def ljCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 68 → m[ljCodeBase + k]? = some (ljCode.getD k 0)

theorem ljCode_len : ljCode.length = 68 := by decide +kernel

theorem ljCodeLoaded_of {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot ljCodeBase ljCode, m[p.1]? = some p.2.2) : ljCodeLoaded m :=
  fun k hk => loaded_of_foot h k (by rw [ljCode_len]; exact hk)

theorem ljCode_at_8000703c {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x8000703c : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x8000703d : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x8000703e : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000703f : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

theorem ljCode_at_80007040 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007040 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007041 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80007042 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80007043 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

theorem ljCode_at_80007044 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007044 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80007045 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80007046 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80007047 : Nat)]? = some (0x01 : BitVec 8) :=
  ⟨h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)⟩

theorem ljCode_at_80007048 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007048 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007049 : Nat)]? = some (0x39 : BitVec 8) ∧
    m[(0x8000704a : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x8000704b : Nat)]? = some (0x01 : BitVec 8) :=
  ⟨h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)⟩

theorem ljCode_at_8000704c {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x8000704c : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x8000704d : Nat)]? = some (0x39 : BitVec 8) ∧
    m[(0x8000704e : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000704f : Nat)]? = some (0x02 : BitVec 8) :=
  ⟨h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide)⟩

theorem ljCode_at_80007050 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007050 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007051 : Nat)]? = some (0x3a : BitVec 8) ∧
    m[(0x80007052 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80007053 : Nat)]? = some (0x02 : BitVec 8) :=
  ⟨h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide)⟩

theorem ljCode_at_80007054 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007054 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80007055 : Nat)]? = some (0x3a : BitVec 8) ∧
    m[(0x80007056 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80007057 : Nat)]? = some (0x03 : BitVec 8) :=
  ⟨h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide)⟩

theorem ljCode_at_80007058 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007058 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007059 : Nat)]? = some (0x3b : BitVec 8) ∧
    m[(0x8000705a : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x8000705b : Nat)]? = some (0x03 : BitVec 8) :=
  ⟨h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide)⟩

theorem ljCode_at_8000705c {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x8000705c : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x8000705d : Nat)]? = some (0x3b : BitVec 8) ∧
    m[(0x8000705e : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000705f : Nat)]? = some (0x04 : BitVec 8) :=
  ⟨h 32 (by decide), h 33 (by decide), h 34 (by decide), h 35 (by decide)⟩

theorem ljCode_at_80007060 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007060 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007061 : Nat)]? = some (0x3c : BitVec 8) ∧
    m[(0x80007062 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80007063 : Nat)]? = some (0x04 : BitVec 8) :=
  ⟨h 36 (by decide), h 37 (by decide), h 38 (by decide), h 39 (by decide)⟩

theorem ljCode_at_80007064 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007064 : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x80007065 : Nat)]? = some (0x3c : BitVec 8) ∧
    m[(0x80007066 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80007067 : Nat)]? = some (0x05 : BitVec 8) :=
  ⟨h 40 (by decide), h 41 (by decide), h 42 (by decide), h 43 (by decide)⟩

theorem ljCode_at_80007068 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007068 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007069 : Nat)]? = some (0x3d : BitVec 8) ∧
    m[(0x8000706a : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x8000706b : Nat)]? = some (0x05 : BitVec 8) :=
  ⟨h 44 (by decide), h 45 (by decide), h 46 (by decide), h 47 (by decide)⟩

theorem ljCode_at_8000706c {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x8000706c : Nat)]? = some (0x83 : BitVec 8) ∧
    m[(0x8000706d : Nat)]? = some (0x3d : BitVec 8) ∧
    m[(0x8000706e : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000706f : Nat)]? = some (0x06 : BitVec 8) :=
  ⟨h 48 (by decide), h 49 (by decide), h 50 (by decide), h 51 (by decide)⟩

theorem ljCode_at_80007070 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007070 : Nat)]? = some (0x03 : BitVec 8) ∧
    m[(0x80007071 : Nat)]? = some (0x31 : BitVec 8) ∧
    m[(0x80007072 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80007073 : Nat)]? = some (0x06 : BitVec 8) :=
  ⟨h 52 (by decide), h 53 (by decide), h 54 (by decide), h 55 (by decide)⟩

theorem ljCode_at_80007074 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007074 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80007075 : Nat)]? = some (0xb5 : BitVec 8) ∧
    m[(0x80007076 : Nat)]? = some (0x15 : BitVec 8) ∧
    m[(0x80007077 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 56 (by decide), h 57 (by decide), h 58 (by decide), h 59 (by decide)⟩

theorem ljCode_at_80007078 {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x80007078 : Nat)]? = some (0x33 : BitVec 8) ∧
    m[(0x80007079 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x8000707a : Nat)]? = some (0xb5 : BitVec 8) ∧
    m[(0x8000707b : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 60 (by decide), h 61 (by decide), h 62 (by decide), h 63 (by decide)⟩

theorem ljCode_at_8000707c {m : Std.ExtHashMap Nat (BitVec 8)} (h : ljCodeLoaded m) :
    m[(0x8000707c : Nat)]? = some (0x67 : BitVec 8) ∧
    m[(0x8000707d : Nat)]? = some (0x80 : BitVec 8) ∧
    m[(0x8000707e : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x8000707f : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 64 (by decide), h 65 (by decide), h 66 (by decide), h 67 (by decide)⟩

def rtJalSnprintf1 : JalSite where
  pc := 0x80002dc8
  b0 := 0xef#8
  b1 := 0x20#8
  b2 := 0xd0#8
  b3 := 0x67#8
  w := 0x67d020ef#32
  imm := 0x2e7c#21
  tgt := 0x80005c44#64

theorem rtJalSnprintf1_cert : rtJalSnprintf1.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_67d020ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

def rtJalSnprintf2 : JalSite where
  pc := 0x80002de4
  b0 := 0xef#8
  b1 := 0x20#8
  b2 := 0x10#8
  b3 := 0x66#8
  w := 0x661020ef#32
  imm := 0x2e60#21
  tgt := 0x80005c44#64

theorem rtJalSnprintf2_cert : rtJalSnprintf2.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_661020ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

def rtJalLongjmp : JalSite where
  pc := 0x80002df0
  b0 := 0xef#8
  b1 := 0x40#8
  b2 := 0xc0#8
  b3 := 0x24#8
  w := 0x24c040ef#32
  imm := 0x424c#21
  tgt := 0x8000703c#64

theorem rtJalLongjmp_cert : rtJalLongjmp.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_24c040ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

abbrev setjmpCodeBase : Nat := 0x80006ffc
def setjmpCode : List (BitVec 8) :=
  [0x23#8, 0x30#8, 0x15#8, 0x00#8, 0x23#8, 0x34#8, 0x85#8, 0x00#8, 0x23#8, 0x38#8, 0x95#8, 0x00#8, 0x23#8, 0x3c#8, 0x25#8, 0x01#8, 0x23#8, 0x30#8, 0x35#8, 0x03#8, 0x23#8, 0x34#8, 0x45#8, 0x03#8, 0x23#8, 0x38#8, 0x55#8, 0x03#8, 0x23#8, 0x3c#8, 0x65#8, 0x03#8, 0x23#8, 0x30#8, 0x75#8, 0x05#8, 0x23#8, 0x34#8, 0x85#8, 0x05#8, 0x23#8, 0x38#8, 0x95#8, 0x05#8, 0x23#8, 0x3c#8, 0xa5#8, 0x05#8, 0x23#8, 0x30#8, 0xb5#8, 0x07#8, 0x23#8, 0x34#8, 0x25#8, 0x06#8, 0x13#8, 0x05#8, 0x00#8, 0x00#8, 0x67#8, 0x80#8, 0x00#8, 0x00#8]

theorem setjmpCode_text : TextAt setjmpCodeBase setjmpCode := by decide +kernel

def setjmpCodeLoaded (m : Std.ExtHashMap Nat (BitVec 8)) : Prop :=
  ∀ k, k < 64 → m[setjmpCodeBase + k]? = some (setjmpCode.getD k 0)

theorem setjmpCode_len : setjmpCode.length = 64 := by decide +kernel

theorem setjmpCodeLoaded_of {m : Std.ExtHashMap Nat (BitVec 8)}
    (h : ∀ p ∈ codeFoot setjmpCodeBase setjmpCode, m[p.1]? = some p.2.2) : setjmpCodeLoaded m :=
  fun k hk => loaded_of_foot h k (by rw [setjmpCode_len]; exact hk)

theorem setjmpCode_at_80006ffc {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80006ffc : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80006ffd : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x80006ffe : Nat)]? = some (0x15 : BitVec 8) ∧
    m[(0x80006fff : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide)⟩

theorem setjmpCode_at_80007000 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007000 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007001 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80007002 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80007003 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide)⟩

theorem setjmpCode_at_80007004 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007004 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007005 : Nat)]? = some (0x38 : BitVec 8) ∧
    m[(0x80007006 : Nat)]? = some (0x95 : BitVec 8) ∧
    m[(0x80007007 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 8 (by decide), h 9 (by decide), h 10 (by decide), h 11 (by decide)⟩

theorem setjmpCode_at_80007008 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007008 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007009 : Nat)]? = some (0x3c : BitVec 8) ∧
    m[(0x8000700a : Nat)]? = some (0x25 : BitVec 8) ∧
    m[(0x8000700b : Nat)]? = some (0x01 : BitVec 8) :=
  ⟨h 12 (by decide), h 13 (by decide), h 14 (by decide), h 15 (by decide)⟩

theorem setjmpCode_at_8000700c {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x8000700c : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x8000700d : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x8000700e : Nat)]? = some (0x35 : BitVec 8) ∧
    m[(0x8000700f : Nat)]? = some (0x03 : BitVec 8) :=
  ⟨h 16 (by decide), h 17 (by decide), h 18 (by decide), h 19 (by decide)⟩

theorem setjmpCode_at_80007010 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007010 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007011 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80007012 : Nat)]? = some (0x45 : BitVec 8) ∧
    m[(0x80007013 : Nat)]? = some (0x03 : BitVec 8) :=
  ⟨h 20 (by decide), h 21 (by decide), h 22 (by decide), h 23 (by decide)⟩

theorem setjmpCode_at_80007014 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007014 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007015 : Nat)]? = some (0x38 : BitVec 8) ∧
    m[(0x80007016 : Nat)]? = some (0x55 : BitVec 8) ∧
    m[(0x80007017 : Nat)]? = some (0x03 : BitVec 8) :=
  ⟨h 24 (by decide), h 25 (by decide), h 26 (by decide), h 27 (by decide)⟩

theorem setjmpCode_at_80007018 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007018 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007019 : Nat)]? = some (0x3c : BitVec 8) ∧
    m[(0x8000701a : Nat)]? = some (0x65 : BitVec 8) ∧
    m[(0x8000701b : Nat)]? = some (0x03 : BitVec 8) :=
  ⟨h 28 (by decide), h 29 (by decide), h 30 (by decide), h 31 (by decide)⟩

theorem setjmpCode_at_8000701c {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x8000701c : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x8000701d : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x8000701e : Nat)]? = some (0x75 : BitVec 8) ∧
    m[(0x8000701f : Nat)]? = some (0x05 : BitVec 8) :=
  ⟨h 32 (by decide), h 33 (by decide), h 34 (by decide), h 35 (by decide)⟩

theorem setjmpCode_at_80007020 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007020 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007021 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80007022 : Nat)]? = some (0x85 : BitVec 8) ∧
    m[(0x80007023 : Nat)]? = some (0x05 : BitVec 8) :=
  ⟨h 36 (by decide), h 37 (by decide), h 38 (by decide), h 39 (by decide)⟩

theorem setjmpCode_at_80007024 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007024 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007025 : Nat)]? = some (0x38 : BitVec 8) ∧
    m[(0x80007026 : Nat)]? = some (0x95 : BitVec 8) ∧
    m[(0x80007027 : Nat)]? = some (0x05 : BitVec 8) :=
  ⟨h 40 (by decide), h 41 (by decide), h 42 (by decide), h 43 (by decide)⟩

theorem setjmpCode_at_80007028 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007028 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007029 : Nat)]? = some (0x3c : BitVec 8) ∧
    m[(0x8000702a : Nat)]? = some (0xa5 : BitVec 8) ∧
    m[(0x8000702b : Nat)]? = some (0x05 : BitVec 8) :=
  ⟨h 44 (by decide), h 45 (by decide), h 46 (by decide), h 47 (by decide)⟩

theorem setjmpCode_at_8000702c {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x8000702c : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x8000702d : Nat)]? = some (0x30 : BitVec 8) ∧
    m[(0x8000702e : Nat)]? = some (0xb5 : BitVec 8) ∧
    m[(0x8000702f : Nat)]? = some (0x07 : BitVec 8) :=
  ⟨h 48 (by decide), h 49 (by decide), h 50 (by decide), h 51 (by decide)⟩

theorem setjmpCode_at_80007030 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007030 : Nat)]? = some (0x23 : BitVec 8) ∧
    m[(0x80007031 : Nat)]? = some (0x34 : BitVec 8) ∧
    m[(0x80007032 : Nat)]? = some (0x25 : BitVec 8) ∧
    m[(0x80007033 : Nat)]? = some (0x06 : BitVec 8) :=
  ⟨h 52 (by decide), h 53 (by decide), h 54 (by decide), h 55 (by decide)⟩

theorem setjmpCode_at_80007034 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007034 : Nat)]? = some (0x13 : BitVec 8) ∧
    m[(0x80007035 : Nat)]? = some (0x05 : BitVec 8) ∧
    m[(0x80007036 : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x80007037 : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 56 (by decide), h 57 (by decide), h 58 (by decide), h 59 (by decide)⟩

theorem setjmpCode_at_80007038 {m : Std.ExtHashMap Nat (BitVec 8)} (h : setjmpCodeLoaded m) :
    m[(0x80007038 : Nat)]? = some (0x67 : BitVec 8) ∧
    m[(0x80007039 : Nat)]? = some (0x80 : BitVec 8) ∧
    m[(0x8000703a : Nat)]? = some (0x00 : BitVec 8) ∧
    m[(0x8000703b : Nat)]? = some (0x00 : BitVec 8) :=
  ⟨h 60 (by decide), h 61 (by decide), h 62 (by decide), h 63 (by decide)⟩

def topJalRet : JalSite where
  pc := 0x80004558
  b0 := 0xef#8
  b1 := 0x10#8
  b2 := 0xc0#8
  b3 := 0x6e#8
  w := 0x6ec010ef#32
  imm := 0x16ec#21
  tgt := 0x80005c44#64

theorem topJalRet_cert : topJalRet.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_6ec010ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

def topJalBrk : JalSite where
  pc := 0x8000457c
  b0 := 0xef#8
  b1 := 0x10#8
  b2 := 0x80#8
  b3 := 0x6c#8
  w := 0x6c8010ef#32
  imm := 0x16c8#21
  tgt := 0x80005c44#64

theorem topJalBrk_cert : topJalBrk.Cert where
  word := by decide
  notrvc := by decide
  dec := fun σ h1 h2 h3 => Vsa.Sim.DecodeTable.decode_6c8010ef σ h1 h2 h3
  tgt := by decide
  tgt_align := by decide
  lo := by decide
  hi := by decide
  align := by decide

end VsaIris.Newlib.Sites
