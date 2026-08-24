import Vsa.Elf

/-! Discovery only (not proof): #eval the post-`setupElf` values of the
GoodState priority registers, to pin them as literals in Vsa/Sim/InitValues. -/

open LeanRV64DExecutable Sail ConcurrencyInterfaceV1 Vsa
open Register

def postInit : Except String (SequentialState RegisterType trivialChoiceSource) :=
  match Vsa.whileElf? with
  | .error e => .error e
  | .ok elf =>
    match (Vsa.setupElf elf).run (Vsa.initState elf) with
    | .ok _ σ => .ok σ
    | .error e _ => .error e.print

def showReg (name : String) (f : SequentialState RegisterType trivialChoiceSource → String) : IO Unit := do
  match postInit with
  | .error e => IO.println s!"ERROR: {e}"
  | .ok σ => IO.println s!"{name} = {f σ}"

#eval showReg "misa" (fun σ => toString <| (σ.regs.get? Register.misa).map repr)
#eval showReg "mstatus" (fun σ => toString <| (σ.regs.get? Register.mstatus).map repr)
#eval showReg "mseccfg" (fun σ => toString <| (σ.regs.get? Register.mseccfg).map repr)
#eval showReg "mie" (fun σ => toString <| (σ.regs.get? Register.mie).map repr)
#eval showReg "mip" (fun σ => toString <| (σ.regs.get? Register.mip).map repr)
#eval showReg "mideleg" (fun σ => toString <| (σ.regs.get? Register.mideleg).map repr)
#eval showReg "medeleg" (fun σ => toString <| (σ.regs.get? Register.medeleg).map repr)
#eval showReg "satp" (fun σ => toString <| (σ.regs.get? Register.satp).map repr)
#eval showReg "cur_privilege" (fun σ => toString <| (σ.regs.get? Register.cur_privilege).map (fun v => match (v : Privilege) with | .Machine => "Machine" | .Supervisor => "Supervisor" | .User => "User" | _ => "other"))
#eval showReg "htif_done" (fun σ => toString <| (σ.regs.get? Register.htif_done).map (fun v => toString (v : Bool)))
#eval showReg "htif_tohost" (fun σ => toString <| (σ.regs.get? Register.htif_tohost).map repr)
#eval showReg "PC" (fun σ => toString <| (σ.regs.get? Register.PC).map repr)
#eval showReg "nextPC" (fun σ => toString <| (σ.regs.get? Register.nextPC).map repr)
#eval showReg "mtvec" (fun σ => toString <| (σ.regs.get? Register.mtvec).map repr)
#eval showReg "mcountinhibit" (fun σ => toString <| (σ.regs.get? Register.mcountinhibit).map repr)
#eval showReg "minstretcfg" (fun σ => toString <| (σ.regs.get? Register.minstretcfg).map repr)
#eval showReg "mcyclecfg" (fun σ => toString <| (σ.regs.get? Register.mcyclecfg).map repr)
#eval showReg "minstret_increment" (fun σ => toString <| (σ.regs.get? Register.minstret_increment).map (fun v => toString (v : Bool)))
#eval showReg "elp" (fun σ => toString <| (σ.regs.get? Register.elp).map repr)
#eval showReg "pmpcfg0" (fun σ => toString <| (σ.regs.get? Register.pmpcfg_n).map (fun v => toString <| ((v : Vector (BitVec 8) 64).toList.map (fun e => e.toNat))))
#eval showReg "pmpaddr_all_zero" (fun σ => toString <| (σ.regs.get? Register.pmpaddr_n).map (fun v => toString <| ((v : Vector (BitVec 64) 64).toList.all (fun e => e == 0))))
#eval showReg "sig_meip" (fun σ => toString <| (σ.regs.get? Register.sig_meip).map repr)
#eval showReg "sig_seip" (fun σ => toString <| (σ.regs.get? Register.sig_seip).map repr)
#eval showReg "menvcfg" (fun σ => toString <| (σ.regs.get? Register.menvcfg).map repr)
#eval showReg "stimecmp" (fun σ => toString <| (σ.regs.get? Register.stimecmp).map repr)
#eval showReg "senvcfg" (fun σ => toString <| (σ.regs.get? Register.senvcfg).map repr)
