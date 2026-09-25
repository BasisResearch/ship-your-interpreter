import VsaIris.Interp.ProofEnvNew
import VsaIris.Interp.ProofEnvGet
import VsaIris.Interp.ProofEnvSet
import VsaIris.Interp.ProofEnvDefine
import VsaIris.Interp.ProofStrcmp
import VsaIris.Interp.ProofMemcpy
import VsaIris.Interp.ProofStrcpyH
import VsaIris.Interp.ProofStringify
import VsaIris.Interp.ProofValueCons
import VsaIris.Interp.ProofValueTruthy
import VsaIris.Interp.ProofValueEqual
import VsaIris.Interp.ProofValueKindName
import VsaIris.Interp.ProofNativePrintln
import VsaIris.Interp.ProofNativeAssert
import VsaIris.Interp.SupplyBoot
import VsaIris.Interp.StuckSim
import VsaIris.Interp.TopRun
import VsaIris.Interp.TopBoundary
import VsaIris.Interp.Holes
import VsaIris.Vsa.ExitH.Iris
import VsaIris.Vsa.Stderr.FprintfSpec

/-!
# The helper specs as closed statements (lane A, F4)

INTERP_DESIGN.md "STATEMENT CHANGE (lane A): helper specs carry their code
context". Every helper spec the case lemmas take (`TermSupply`,
`StuckSupply`) carries the persistent code context its proof runs from in its
precondition: `codeX` (the binary's image and `_impure_ptr`) and `gp` for the
`env_*` helpers, `binImg` for `strcmp`, `strlen`/`strcpy` of heap strings and
`memcpy` of an owned source, and `stringify` already takes `binImg` and
`stdioOwn`. So each spec is a closed statement: `*_closed` below proves it
from the helper's proof, whose code-context premise it reads off the
precondition (the generic `fnSpecW_close`/`fnSpecAbort_close`/
`helperSpec_close`).

`termSupply`/`stuckSupply` assemble the records from these and the boundary's
facts. Premises on `live`: the interpreter's text (`interpText`), the binary's
`.text` (`CodeLive`), `env.c`'s and the allocator's code lists (`envText`,
`AllocLive`: both include `_impure_ptr`'s bytes) and the stack segment
(`StackLive`: `stringify`'s `strlen` of its stack buffer, H3).
-/

namespace VsaIris.Interp

open Iris Iris.BI Iris.Std Iris.ProgramLogic Iris.ProofMode
open VsaIris VsaIris.Inst VsaIris.VsaHeap VsaIris.MallocFast VsaIris.Sym VsaIris.Newlib VsaIris.Stdio
open Vsa.While Vsa.MemRepr Vsa.RuntimeRepr

/-! ## Closing a spec over a persistent context in its precondition -/

section Close

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] {M : MachineModel}

/-- **A spec proved under a persistent context `C` that its precondition
carries is closed.** -/
theorem fnSpecW_close (Wp : MachWP (GF := GF) M) {entry : BitVec 64} {C : IProp GF}
    [Persistent C] {P Q : BitVec 64 → IProp GF} (h : C ⊢ fnSpecW Wp entry P Q)
    (hP : ∀ r, P r ⊢ C ∗ P r) : ⊢ fnSpecW Wp entry P Q := by
  unfold fnSpecW at h ⊢
  imodintro
  iintro %r %Φ Hpc Hra HP Hk
  ihave ⟨#HC, HP⟩ := hP r $$ HP
  ihave #H := h $$ HC
  iapply H $$ %r %Φ Hpc Hra HP Hk

/-- `fnSpecW_close` for a function that returns or aborts. -/
theorem fnSpecAbort_close (Wp : MachWP (GF := GF) M) {entry : BitVec 64} {C : IProp GF}
    [Persistent C] {P Q : BitVec 64 → IProp GF} {A : IProp GF} (h : C ⊢ fnSpecAbort Wp entry P Q A)
    (hP : ∀ r, P r ⊢ C ∗ P r) : ⊢ fnSpecAbort Wp entry P Q A := by
  unfold fnSpecAbort at h ⊢
  imodintro
  iintro %r %Φ Hpc Hra HP Hk
  ihave ⟨#HC, HP⟩ := hP r $$ HP
  ihave #H := h $$ HC
  iapply H $$ %r %Φ Hpc Hra HP Hk

/-- `fnSpecW_close` for a runtime helper in register-file form. -/
theorem helperSpec_close (Wp : MachWP (GF := GF) M) {entry : BitVec 64} {clob : List Nat}
    {pins : (Nat → BitVec 64) → Prop} {Pre : IProp GF} {Post : (Nat → BitVec 64) → IProp GF}
    {C : IProp GF} [Persistent C] (h : C ⊢ helperSpec M Wp entry clob pins Pre Post)
    (hP : Pre ⊢ C ∗ Pre) : ⊢ helperSpec M Wp entry clob pins Pre Post := by
  unfold helperSpec at h ⊢
  iintro %rv
  iapply fnSpecW_close Wp (C := C) (h.trans (forall_elim rv))
  intro r
  iintro ⟨%hal, Hregs, %hp, #Hcode, HPre⟩
  ihave ⟨#HC, HPre⟩ := hP $$ HPre
  iframe HC Hregs Hcode HPre
  ipureintro; exact ⟨hal, hp⟩

end Close

/-! ## The closed helper specs -/

section Closed

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]
variable {live : Nat → Prop}

local notation "Mv" live => vsaModel live

/-- The stack segment is live (`stringify`'s `strlen` reads its stack buffer
through the run's read-only text, H3). -/
abbrev StackLive (live : Nat → Prop) : Prop := ∀ a, 0x87800000 ≤ a → a < 0x88000000 → live a

theorem strcmpV_closed (hcl : CodeLive live) (Wp : MachWP (GF := GF) (Mv live)) :
    ⊢ strcmpSpecV (GF := GF) (Mv live) Wp :=
  strcmp_spec_v live hcl Wp

omit I in
theorem strcmpOrd_closed (hcl : CodeLive live) (Wp : MachWP (GF := GF) (Mv live)) :
    ⊢ strcmpOrdSpec (GF := GF) (Mv live) Wp :=
  strcmp_spec_ord live hcl Wp

/-- **`env_new`**, closed. -/
theorem envNew_closed (henv : ∀ p ∈ envText, live p.1) (A : AllocSpecs live)
    (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) : ⊢ envNewSpec (GF := GF) Wp N := by
  have h := envNew_spec Wp henv A N
  unfold envNewSpec at h ⊢
  imodintro
  iintro %ρ %st %po %par %s %saved %hsv
  iapply fnSpecAbort_close Wp (C := iprop(codeX ∗ gp ↦ᵣ□ MallocFast.gpV)) ?_ ?_
  · iintro ⟨#Hx, #Hg⟩
    ihave #Ht := codeX_envText $$ Hx
    ihave #Ha := codeX_allocText $$ Hx
    ihave #H := h $$ [Ht Ha Hg]
    · iframe Ht Ha Hg
    iapply H $$ %ρ %st %po %par %s %saved %hsv
  · intro r
    iintro ⟨%hp, H10, Hsp, #Hg, #Hx, Hrest⟩
    iframe Hx Hg H10 Hsp Hrest
    ipureintro; exact hp

/-- **`env_define`**, closed. -/
theorem envDefine_closed (hcl : CodeLive live) (henv : ∀ p ∈ envText, live p.1)
    (halloc : AllocLive live) (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) :
    ⊢ envDefineSpec (GF := GF) Wp N := by
  have h := envDefine_spec Wp henv halloc N
  unfold envDefineSpec at h ⊢
  imodintro
  iintro %ρ %st %fa %x %v %e %pn %pv %s %saved %hsv
  iapply fnSpecAbort_close Wp (C := iprop(codeX ∗ gp ↦ᵣ□ MallocFast.gpV)) ?_ ?_
  · iintro ⟨#Hx, #Hg⟩
    ihave #Hb := codeX_binImg $$ Hx
    ihave #Ht := codeX_envText $$ Hx
    ihave #Ha := codeX_allocText $$ Hx
    ihave #Hcmp := strcmp_spec_env live hcl Wp $$ Hb
    ihave #Hsl := StrLeaf.strlen_spec_env live hcl Wp $$ Hb
    ihave #Hmc := memcpy_spec_env live hcl Wp $$ Hb
    ihave #H := h $$ [Ht Ha Hg Hcmp Hsl Hmc]
    · iframe Ht Ha Hg Hcmp Hsl Hmc
    iapply H $$ %ρ %st %fa %x %v %e %pn %pv %s %saved %hsv
  · intro r
    iintro ⟨%hp, H10, H11, H12, Hsp, #Hg, #Hx, Hrest⟩
    iframe Hx Hg H10 H11 H12 Hsp Hrest
    ipureintro; exact hp

/-- **`env_get`**, closed. -/
theorem envGet_closed (hcl : CodeLive live) (henv : ∀ p ∈ envText, live p.1)
    (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) : ⊢ envGetSpec (GF := GF) Wp N := by
  have h := envGet_spec Wp henv N
  unfold envGetSpec at h ⊢
  imodintro
  iintro %st %B %fa %x %e %pn %out %s %saved %hsv
  iapply fnSpecW_close Wp (C := iprop(codeX ∗ gp ↦ᵣ□ MallocFast.gpV)) ?_ ?_
  · iintro ⟨#Hx, #Hg⟩
    ihave #Ht := codeX_envText $$ Hx
    ihave #Hcmp := strcmp_spec_env live hcl Wp $$ [Hx]
    · iapply codeX_binImg $$ Hx
    ihave #H := h $$ [Ht Hg Hcmp]
    · iframe Ht Hg Hcmp
    iapply H $$ %st %B %fa %x %e %pn %out %s %saved %hsv
  · intro r
    iintro ⟨%hp, H10, H11, H12, Hsp, Hcl, Hsv, Hstk, #Hfa, #Hs, Hout, Hst, #Hg, #Hx⟩
    iframe Hx Hg H10 H11 H12 Hsp Hcl Hsv Hstk Hfa Hs Hout Hst
    ipureintro; exact hp

/-- **`env_set`**, closed. -/
theorem envSet_closed (hcl : CodeLive live) (henv : ∀ p ∈ envText, live p.1)
    (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) : ⊢ envSetSpec (GF := GF) Wp N := by
  have h := envSet_spec Wp henv N
  unfold envSetSpec at h ⊢
  imodintro
  iintro %st %B %fa %x %v %e %pn %pv %s %saved %hsv
  iapply fnSpecW_close Wp (C := iprop(codeX ∗ gp ↦ᵣ□ MallocFast.gpV)) ?_ ?_
  · iintro ⟨#Hx, #Hg⟩
    ihave #Ht := codeX_envText $$ Hx
    ihave #Hcmp := strcmp_spec_env live hcl Wp $$ [Hx]
    · iapply codeX_binImg $$ Hx
    ihave #H := h $$ [Ht Hg Hcmp]
    · iframe Ht Hg Hcmp
    iapply H $$ %st %B %fa %x %v %e %pn %pv %s %saved %hsv
  · intro r
    iintro ⟨%hp, H10, H11, H12, Hsp, Hcl, Hsv, Hstk, #Hfa, #Hs, Hval, Hst, #Hg, #Hx⟩
    iframe Hx Hg H10 H11 H12 Hsp Hcl Hsv Hstk Hfa Hs Hval Hst
    ipureintro; exact hp

/-- **`strlen` of an owned heap string**, closed. -/
theorem strlenHeap_closed (hcl : CodeLive live) (Wp : MachWP (GF := GF) (Mv live)) :
    ⊢ ∀ q x ρ H, strlenHeapSpec (GF := GF) (Mv live) Wp q x ρ H := by
  iintro %q %x %ρ %H
  unfold strlenHeapSpec
  iapply helperSpec_close Wp (C := binImg) (StrLeaf.strlen_heap_spec live hcl Wp q x ρ H)
  iintro ⟨#Hb, Hrest⟩
  iframe Hb Hrest

/-- **`strcpy` of an owned heap string**, closed. -/
theorem strcpyHeap_closed (hcl : CodeLive live) (Wp : MachWP (GF := GF) (Mv live)) :
    ⊢ ∀ d q y ρ H, strcpyHeapSpec (GF := GF) (Mv live) Wp d q y ρ H := by
  iintro %d %q %y %ρ %H
  unfold strcpyHeapSpec
  iapply helperSpec_close Wp (C := binImg) (StrLeaf.strcpy_heap_spec live hcl Wp d q y ρ H)
  iintro ⟨#Hb, Hrest⟩
  iframe Hb Hrest

omit I in
/-- **`memcpy` from an owned source**, closed. -/
theorem memcpyOwned_closed (hcl : CodeLive live) (Wp : MachWP (GF := GF) (Mv live)) :
    ⊢ memcpySpecOwned (GF := GF) (Mv live) Wp := by
  have h := memcpy_spec_owned live hcl Wp
  unfold memcpySpecOwned at h ⊢
  imodintro
  iintro %dst %src %n %img
  iapply fnSpecW_close Wp (C := binImg) ?_ ?_
  · iintro #Hb
    ihave #H := h $$ Hb
    iapply H $$ %dst %src %n %img
  · intro r
    iintro ⟨%hp, H10, H11, H12, Hcl, Hd, Hs, #Hb⟩
    iframe Hb H10 H11 H12 Hcl Hd Hs
    ipureintro; exact hp

/-- `stringify`'s own callee specs, from the image. -/
theorem stringify_spec_img (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live)
    (hstk : StackLive live) (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles)
    (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) (inp : Nat) (p s : BitVec 64) (v : Value)
    (st : Store) (ρ : Regime) (H : List (Nat × Nat)) (c : Nat) (o : String) :
    textOwn allocText ⊢ stringifySpec (Mv live) N Wp inp p s v st ρ H c o :=
  stringify_spec hlive hcl hstk A HN Hout Wp (memcpyOwned_closed hcl Wp) (memcpy_spec_env live hcl Wp)
    (StrLeaf.strlen_spec_env live hcl Wp) (StrLeaf.strcpy_spec live hcl Wp) N inp p s v st ρ H c o

/-- **`stringify` in the counted regime**, closed: its precondition carries
`binImg` and `stdioOwn` (whose `_impure_ptr` gives the allocator's text), and
the counted regime refutes its out-of-memory abort. -/
theorem stringifyT_closed (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live)
    (hstk : StackLive live) (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles)
    (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) :
    ⊢ ∀ p s v st k H c o, stringifySpecT (GF := GF) (Mv live) N Wp p s v st k H c o := by
  iintro %p %s %v %st %k %H %c %o
  unfold stringifySpecT helperSpec fnSpecW
  dsimp only
  iintro %rv
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Hregs, %hp, #Hcode, HPre⟩ Hk
  unfold stringifyPre
  icases HPre with ⟨Hv, %hg, #Hd, #Hb, Hh, Hstd, Hcon, Hst⟩
  ihave ⟨Hstd, #Hat⟩ := stdioAt_codeX _ $$ [Hstd]
  · iframe Hstd Hb
  ihave #Hat := codeX_allocText $$ Hat
  have hS := stringify_spec_img hlive hcl hstk A HN Hout Wp N 0 p s v st (.counted k) H c o
  unfold stringifySpec fnSpecAbort at hS
  dsimp only at hS
  ihave #HS := hS $$ Hat
  ihave #HS := HS $$ %rv
  ihave HS := HS $$ %r %Φ Hpc Hra [Hregs Hv Hh Hstd Hcon Hst]
  · iframe Hregs Hcode Hv Hd Hb Hh Hstd Hcon Hst
    ipureintro; exact ⟨hal, hp, hg⟩
  iapply HS
  isplit
  · iintro Hpc Hra ⟨%rv', %q, Hregs, %hk, %hq, Hv, Hs, %hf, Hh, Hstd, Hcon, Hst⟩
    iapply Hk $$ Hpc Hra
    iexists rv'
    iframe Hregs
    isplitr
    · ipureintro; exact hk
    unfold stringifyPost
    rw [hq]
    iframe Hv Hs Hh Hstd Hcon Hst
    ipureintro; exact hf
  · iintro ⟨%hρ, -⟩
    cases hρ

/-- **`stringify` that may abort**, closed. -/
theorem stringifyP_closed (hlive : ∀ q ∈ interpText, live q.1) (hcl : CodeLive live)
    (hstk : StackLive live) (A : AllocSpecs live) (HN : NewlibHoles) (Hout : OutHoles)
    (Wp : MachWP (GF := GF) (Mv live)) (N : NativeAddrs) (inp : Nat) :
    ⊢ ∀ p s v st ρ H c o, stringifySpecP (GF := GF) (Mv live) N Wp inp p s v st ρ H c o := by
  iintro %p %s %v %st %ρ %H %c %o
  unfold stringifySpecP helperSpecA fnSpecAbort
  dsimp only
  iintro %rv
  imodintro
  iintro %r %Φ Hpc Hra ⟨%hal, Hregs, %hp, #Hcode, HPre⟩ Hk
  unfold stringifyPre
  icases HPre with ⟨Hv, %hg, #Hd, #Hb, Hh, Hstd, Hcon, Hst⟩
  ihave ⟨Hstd, #Hat⟩ := stdioAt_codeX _ $$ [Hstd]
  · iframe Hstd Hb
  ihave #Hat := codeX_allocText $$ Hat
  have hS := stringify_spec_img hlive hcl hstk A HN Hout Wp N inp p s v st ρ H c o
  unfold stringifySpec fnSpecAbort at hS
  dsimp only at hS
  ihave #HS := hS $$ Hat
  ihave #HS := HS $$ %rv
  ihave HS := HS $$ %r %Φ Hpc Hra [Hregs Hv Hh Hstd Hcon Hst]
  · iframe Hregs Hcode Hv Hd Hb Hh Hstd Hcon Hst
    ipureintro; exact ⟨hal, hp, hg⟩
  iapply HS
  isplit
  · iintro Hpc Hra ⟨%rv', %q, Hregs, %hk, %hq, Hv, Hs, %hf, Hh, Hstd, Hcon, Hst⟩
    ihave Hk := and_elim_l $$ Hk
    iapply Hk $$ Hpc Hra
    iexists rv'
    iframe Hregs
    isplitr
    · ipureintro; exact hk
    unfold stringifyPost
    rw [hq]
    iframe Hv Hs Hh Hstd Hcon Hst
    ipureintro; exact hf
  · iintro ⟨-, HA⟩
    ihave Hk := and_elim_r $$ Hk
    iapply Hk $$ HA

end Closed

/-! ## The records -/

section Records

variable {hlc : HasLC} {GF : BundledGFunctors} [G : MachGS hlc GF] [I : InterpGS GF]

local notation "Mv" live => vsaModel live
local notation "Lp" => vsaLayoutP
local notation "Rp" => vsaRoomB

/-- The premises on `live` the helper proofs share. -/
structure SupplyLive (live : Nat → Prop) : Prop where
  interp : ∀ p ∈ interpText, live p.1
  code : CodeLive live
  env : ∀ p ∈ envText, live p.1
  alloc : AllocLive live
  stack : StackLive live

/-- **`term_sim`'s supply** from the helper proofs and the boundary's facts. -/
theorem termSupply {live : Nat → Prop} (L : SupplyLive live) (HN : NewlibHoles) (Hout : OutHoles)
    {N : NativeAddrs} {inp : Nat} (hent : NativeEntries N) (hclo : CloSupply (GF := GF) N)
    (hgeo : RtErr.InpGeom (BitVec.ofNat 64 inp)) (hlt : inp < 2 ^ 64) (hal : inp % 8 = 0) :
    TermSupply (GF := GF) live N inp where
  hlive := L.interp
  vint := by iintro %p %n; iapply valueInt_spec L.interp _ N p n
  vbool := by iintro %p %b; iapply valueBool_spec L.interp _ N p b
  vnull := by iintro %p; iapply valueNull_spec L.interp _ N p
  vstr := by iintro %p %q %x; iapply valueStr_spec L.interp _ N p q x
  vtruthy := by iintro %p %v; iapply valueTruthy_spec L.interp _ N p v
  vequal := by
    iintro %pa %pb %s %a %b %st %B; iapply valueEqual_spec L.interp _ N pa pb s a b st B
  strcmpV := strcmpV_closed L.code _
  strcmpOrd := strcmpOrd_closed L.code _
  envGet := envGet_closed L.code L.env _ N
  envSet := envSet_closed L.code L.env _ N
  envNew := envNew_closed L.env (allocSpecs live L.alloc) _ N
  envDefine := envDefine_closed L.code L.env L.alloc _ N
  nativeInj := nativeInj_of hent
  nativeEntries := hent
  cloSupply := hclo
  inpGeom := hgeo
  inpLt := hlt
  inpAl := hal
  nPrint := fun sret args s vs st o => nativePrint_spec L.interp L.code Hout _ N sret args s vs st o
  nPrintln := fun sret args s vs st o => nativePrintln_spec L.interp L.code Hout _ N sret args s vs st o
  nAssert := fun sret inp args s line vs ρ st d jb =>
    nativeAssert_spec L.interp L.code HN _ N Lp Rp sret inp args s line vs ρ st d jb
  alloc := allocSpecs live L.alloc
  stringifyT := stringifyT_closed L.interp L.code L.stack (allocSpecs live L.alloc) HN Hout _ N
  strlenHeap := strlenHeap_closed L.code _
  memcpyOwned := memcpyOwned_closed L.code _
  strcpyHeap := strcpyHeap_closed L.code _

/-- **`stuck_sim`'s supply** from the helper proofs and the boundary's facts. -/
theorem stuckSupply {live : Nat → Prop} (L : SupplyLive live) (HN : NewlibHoles) (Hout : OutHoles)
    {N : NativeAddrs} {inp : Nat} (hE : ErrEnv (GF := GF) N Lp Rp inp live (evalCore N Lp Rp inp))
    (hent : NativeEntries N) (hclo : CloSupply (GF := GF) N) (hal : inp % 8 = 0) :
    StuckSupply (GF := GF) live N inp where
  hlive := L.interp
  errEnv := hE
  vint := by iintro %p %n; iapply valueInt_spec L.interp _ N p n
  vbool := by iintro %p %b; iapply valueBool_spec L.interp _ N p b
  vnull := by iintro %p; iapply valueNull_spec L.interp _ N p
  vstr := by iintro %p %q %x; iapply valueStr_spec L.interp _ N p q x
  vtruthy := by iintro %p %v; iapply valueTruthy_spec L.interp _ N p v
  vequal := by
    iintro %pa %pb %s %a %b %st %B; iapply valueEqual_spec L.interp _ N pa pb s a b st B
  vkind := by iintro %p %Mt %v; iapply valueKindName_spec L.interp _ N p Mt v
  strcmpV := strcmpV_closed L.code _
  strcmpOrd := strcmpOrd_closed L.code _
  envGet := envGet_closed L.code L.env _ N
  envSet := envSet_closed L.code L.env _ N
  envNew := envNew_closed L.env (allocSpecs live L.alloc) _ N
  envDefine := envDefine_closed L.code L.env L.alloc _ N
  nativeInj := nativeInj_of hent
  nativeEntries := hent
  cloSupply := hclo
  inpAl := hal
  nPrint := fun sret args s vs st o => nativePrint_spec L.interp L.code Hout _ N sret args s vs st o
  nPrintln := fun sret args s vs st o => nativePrintln_spec L.interp L.code Hout _ N sret args s vs st o
  nAssert := fun sret inp args s line vs ρ st d jb =>
    nativeAssert_spec L.interp L.code HN _ N Lp Rp sret inp args s line vs ρ st d jb
  alloc := allocSpecs live L.alloc
  stringifyP := stringifyP_closed L.interp L.code L.stack (allocSpecs live L.alloc) HN Hout _ N inp
  strlenHeap := strlenHeap_closed L.code _
  memcpyOwned := memcpyOwned_closed L.code _
  strcpyHeap := strcpyHeap_closed L.code _

/-! ## At the boundary's live set -/

theorem textOrImpure_topLive {p : Nat × BitVec 8} (h : TextOrImpure p) : topLive p.1 := by
  rcases h with ⟨hd, -⟩ | ⟨hd, -⟩
  · unfold textDom at hd; exact .inl ⟨hd.1, by omega⟩
  · unfold impureW at hd; exact .inr (.inl hd)

/-- `topLive` holds every code list the helpers run from. -/
theorem supplyLive_top : SupplyLive topLive where
  interp := topLive_interp
  code := topLive_code
  env := fun p hp => textOrImpure_topLive (envText_ok p hp)
  alloc := fun p hp => textOrImpure_topLive (allocText_ok p hp)
  stack := fun _ h1 h2 => .inr (.inr ⟨h1, h2⟩)

end Records

open Vsa.Sim.LayoutInstance in
/-- The helper specs of the total and partial cases, for every Iris
instance, from the holes. -/
structure Supplies : Prop where
  term : ∀ {GF : BundledGFunctors} [G : MachGS .hasLC GF] [I : InterpGS GF] (N : NativeAddrs),
    NativeEntries N → TermSupply (GF := GF) topLive N inpTop
  stuck : ∀ {GF : BundledGFunctors} [G : MachGS .hasLC GF] [I : InterpGS GF] (N : NativeAddrs),
    NativeEntries N → StuckSupply (GF := GF) topLive N inpTop

/-- **Every helper spec the recursions take, from the holes.** -/
theorem supplies_of (h : IrisHoles) : Supplies where
  term N hent := termSupply supplyLive_top (h.newlib.full VsaIris.Newlib.fprintf_ok) h.out hent cloSupply inpGeom_top inpLt_top
    inpAl_top
  stuck N hent := stuckSupply supplyLive_top (h.newlib.full VsaIris.Newlib.fprintf_ok) h.out
    ⟨h.newlib.full VsaIris.Newlib.fprintf_ok, topLive_code, inpGeom_top, inpLt_top, coreOK_top N vsaLayoutP vsaRoomB inpTop⟩
    hent
    cloSupply inpAl_top

end VsaIris.Interp

#print axioms VsaIris.Interp.termSupply
#print axioms VsaIris.Interp.stuckSupply
#print axioms VsaIris.Interp.supplies_of
