
#ix_seg {ARM}_run2 {live : Nat → Prop} (hlive : ∀ p ∈ interpText, live p.1)
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {m Mt : Mem} {R : Nat → BitVec 64}
    {s : BitVec 64} :
    IW live m [] (InExt (s.toNat - 176, 176)) Q 0x{J1N}#64 R Mt
  by ix_run hlive at 0x8000409c
