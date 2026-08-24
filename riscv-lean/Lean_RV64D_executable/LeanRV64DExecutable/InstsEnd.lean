import LeanRV64DExecutable.LeanRV64DExecutable
import LeanRV64DExecutable.Flow
import LeanRV64DExecutable.Arith
import LeanRV64DExecutable.Prelude
import LeanRV64DExecutable.Errors
import LeanRV64DExecutable.Xlen
import LeanRV64DExecutable.PlatformConfig
import LeanRV64DExecutable.Types
import LeanRV64DExecutable.Callbacks
import LeanRV64DExecutable.Regs
import LeanRV64DExecutable.PcAccess
import LeanRV64DExecutable.SysRegs
import LeanRV64DExecutable.SysExceptions
import LeanRV64DExecutable.ZicfilpRegs
import LeanRV64DExecutable.SysControl
import LeanRV64DExecutable.Mem
import LeanRV64DExecutable.VmemTlb
import LeanRV64DExecutable.Vmem
import LeanRV64DExecutable.InstsBegin
import LeanRV64DExecutable.VmemUtils
import LeanRV64DExecutable.ZicfilpInsts
import LeanRV64DExecutable.BaseInsts
import LeanRV64DExecutable.ZicsrInsts
import LeanRV64DExecutable.ZicbomInsts

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace LeanRV64DExecutable

open ConcurrencyInterfaceV1

namespace Functions

open xRET_type
open wxfunct6
open wvxfunct6
open wvvfunct6
open wvfunct6
open write_kind
open wmvxfunct6
open wmvvfunct6
open vxsgfunct6
open vxmsfunct6
open vxmfunct6
open vxmcfunct6
open vxfunct6
open vxcmpfunct6
open vvmsfunct6
open vvmfunct6
open vvmcfunct6
open vvfunct6
open vvcmpfunct6
open vstart_class
open vregno
open vregidx
open vmlsop
open vlewidth
open visgfunct6
open virtaddr
open vimsfunct6
open vimfunct6
open vimcfunct6
open vifunct6
open vicmpfunct6
open vfwunary0
open vfunary1
open vfunary0
open vfnunary0
open vextfunct6
open vector_support
open uop
open stateen_bit
open sopw
open sop
open seed_opst
open rounding_mode
open ropw
open rop
open rmvvfunct6
open rivvfunct6
open rfwvvfunct6
open rfvvfunct6
open regno
open regidx
open read_kind
open pte_check_failure
open pmpAddrMatch
open physaddr
open page_based_mem_type
open option
open nxsfunct6
open nxfunct6
open nvsfunct6
open nvfunct6
open nisfunct6
open nifunct6
open mvxmafunct6
open mvxfunct6
open mvvmafunct6
open mvvfunct6
open mmfunct6
open misaligned_exception
open mem_payload
open maskfunct3
open landing_pad_expectation
open iop
open instruction
open indexed_mop
open fwvvmafunct6
open fwvvfunct6
open fwvfunct6
open fwvfmafunct6
open fwvffunct6
open fwffunct6
open fvvmfunct6
open fvvmafunct6
open fvvfunct6
open fvfmfunct6
open fvfmafunct6
open fvffunct6
open fregno
open fregidx
open float_class
open f_un_x_op_H
open f_un_x_op_D
open f_un_rm_xf_op_S
open f_un_rm_xf_op_H
open f_un_rm_xf_op_D
open f_un_rm_fx_op_S
open f_un_rm_fx_op_H
open f_un_rm_fx_op_D
open f_un_rm_ff_op_S
open f_un_rm_ff_op_H
open f_un_rm_ff_op_D
open f_un_op_x_S
open f_un_op_f_S
open f_un_f_op_H
open f_un_f_op_D
open f_madd_op_S
open f_madd_op_H
open f_madd_op_D
open f_bin_x_op_H
open f_bin_x_op_D
open f_bin_rm_op_S
open f_bin_rm_op_H
open f_bin_rm_op_D
open f_bin_op_x_S
open f_bin_op_f_S
open f_bin_f_op_H
open f_bin_f_op_D
open extension
open exception
open csrop
open cregidx
open checked_cbop
open cfregidx
open cbop_zicbop
open cbop_zicbom
open cbie
open cacheop
open breakpoint_cause
open bop
open barrier_kind
open amoop
open agtype
open XtvecModeReservedBehavior
open XipReadType
open XenvcfgCbieReservedBehavior
open WaitReason
open VectorHalf
open TrapVectorMode
open TrapCause
open Step
open Splittability
open Software_Check_Code
open Signedness
open SWCheckCodes
open SATPMode
open Reservability
open Register
open RV32ZdinxOddRegisterReservedBehavior
open Privileged_ISA_Version
open Privilege
open PointerMaskingMode
open PmpWriteOnlyReservedBehavior
open PmpAddrMatchType
open PTW_Error
open PTE_Check
open PM_Ext
open OOBVstartReservedBehavior
open MemoryRegionType
open MemoryAccessType
open InterruptType
open IllegalVtypeReservedBehavior
open ISA_Format
open HartState
open FflagsDirtyPolicy
open FetchResult
open FetchBytes_Result
open FeatureEnabledResult
open FcsrRmReservedBehavior
open Ext_DataAddr_Check
open ExtStatus
open ExtContextPolicy
open ExecutionResult
open ExceptionType
open CSRCheckResult
open CSRAccessType
open AtomicSupport
open Architecture
open AmocasOddRegisterReservedBehavior

def encdec_backwards (arg_ : (BitVec 32)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__178 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__178 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then
      (let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__178 31 12)
      let lpl : (BitVec 20) := (Sail.BitVec.extractLsb v__178 31 12)
      (pure (some (LPAD lpl))))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__178 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__178 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__178 31 12)
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__178 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__178 11 7)
            let imm : (BitVec 20) := (Sail.BitVec.extractLsb v__178 31 12)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some (UTYPE (imm, rd, op)))))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__176 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__176 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__176 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__176 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__176 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__176 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__176 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__176 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__176 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  (JAL ((imm +++ 0#1), rd))))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__173 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__173 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__173 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__173 31 20)
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__173 19 15)
                let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__173 31 20)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some (JALR (imm, rs1, rd)))))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__171 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__171 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__171 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__171 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__171 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__171 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__171 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__171 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__171 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__171 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__171 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__171 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__171 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          (BTYPE ((imm +++ 0#1), rs2, rs1, op))))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__169 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__169 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__169 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__169 31 20)
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__169 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__169 11 7)
                        let imm : (BitVec 12) := (Sail.BitVec.extractLsb v__169 31 20)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some (ITYPE (imm, rs1, rd, op)))))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__165 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__165 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__165 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__165 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__165 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__165 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__165 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__165 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__165 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some (SHIFTIOP (shamt, rs1, rd, SLLI))))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__161 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__161 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__161 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__161 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__161 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__161 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__161 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__161 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__161 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some (SHIFTIOP (shamt, rs1, rd, SRLI))))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__157 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__157 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__157 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__157 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__157 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__157 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__157 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__157 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__157 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some (SHIFTIOP (shamt, rs1, rd, SRAI))))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__153 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__153 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__153 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__153 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__153 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__153 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__153 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__153 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__153 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__153 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) =>
                                          (pure (some (RTYPE (rs2, rs1, rd, ADD)))))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__149 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__149 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__149 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__149 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__149 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__149 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__149 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__149 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__149 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__149 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) =>
                                              (pure (some (RTYPE (rs2, rs1, rd, SLT)))))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__145 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__145 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__145 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__145 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__145 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__145 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__145 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__145 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__145 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__145 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) =>
                                                  (pure (some (RTYPE (rs2, rs1, rd, SLTU)))))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__141 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__141 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__141 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__141 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__141 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__141 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__141 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__141 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__141 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__141 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) =>
                                                      (pure (some (RTYPE (rs2, rs1, rd, AND)))))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__137 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__137 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__137 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__137 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__137 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__137 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__137 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__137 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__137 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__137 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) =>
                                                          (pure (some (RTYPE (rs2, rs1, rd, OR)))))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__133 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__133 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__133 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__133 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__133 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__133 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__133 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__133 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__133 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__133 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) =>
                                                              (pure (some
                                                                  (RTYPE (rs2, rs1, rd, XOR)))))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__129 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__129 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__129 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__129 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__129 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__129 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__129 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__129 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__129 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__129 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some
                                                                      (RTYPE (rs2, rs1, rd, SLL)))))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__125 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__125 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__125 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__125 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__125 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__125 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__125 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__125
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__125
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__125
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some
                                                                          (RTYPE (rs2, rs1, rd, SRL)))))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__121 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__121 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__121 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__121 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__121 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__121 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__121 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__121 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__121 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__121 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some
                                                                              (RTYPE
                                                                                (rs2, rs1, rd, SUB)))))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__117 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__117 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__117 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__117 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__117 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__117 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__117 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__117 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__117 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__117 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some
                                                                                  (RTYPE
                                                                                    (rs2, rs1, rd, SRA)))))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__115 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__115 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__115 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__115 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__115 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__115 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__115 31 20)
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__115 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__115 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__115 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__115 19 15)
                                                                                let imm : (BitVec 12) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__115 31 20)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some
                                                                                        (LOAD
                                                                                          (imm, rs1, rd, is_unsigned, width))))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__112 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__112 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__112 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__112 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__112 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__112 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__112 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__112 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__112 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__112 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__112 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__112 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            (STORE
                                                                                              (imm, rs2, rs1, width)))))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__109 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__109
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__109
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__109
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__109
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__109
                                                                                            31 20)
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__109
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__109
                                                                                            19 15)
                                                                                        let imm : (BitVec 12) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__109
                                                                                            31 20)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                (ADDIW
                                                                                                  (imm, rs1, rd))))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__105 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__105
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__105
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__105
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__105
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__105
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__105
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__105
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__105
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__105
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    (RTYPEW
                                                                                                      (rs2, rs1, rd, ADDW))))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__101 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__101
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__101
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__101
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__101
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__101
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__101
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__101
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__101
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__101
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        (RTYPEW
                                                                                                          (rs2, rs1, rd, SUBW))))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__97 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__97
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__97
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__97
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__97
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__97
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__97
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__97
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__97
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__97
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            (RTYPEW
                                                                                                              (rs2, rs1, rd, SLLW))))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__93 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__93
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__93
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__93
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__93
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__93
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__93
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__93
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__93
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__93
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                (RTYPEW
                                                                                                                  (rs2, rs1, rd, SRLW))))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__89 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__89
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__89
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__89
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__89
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__89
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__89
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__89
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__89
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__89
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    (RTYPEW
                                                                                                                      (rs2, rs1, rd, SRAW))))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__85 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__85
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__85
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__85
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__85
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__85
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let shamt : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__85
                                                                                                                    24
                                                                                                                    20)
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__85
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__85
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        (SHIFTIWOP
                                                                                                                          (shamt, rs1, rd, SLLIW))))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__81 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__81
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__81
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__81
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__81
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__81
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let shamt : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__81
                                                                                                                        24
                                                                                                                        20)
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__81
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__81
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            (SHIFTIWOP
                                                                                                                              (shamt, rs1, rd, SRLIW))))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__77 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__77
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__77
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__77
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__77
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__77
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let shamt : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__77
                                                                                                                            24
                                                                                                                            20)
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__77
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__77
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                (SHIFTIWOP
                                                                                                                                  (shamt, rs1, rd, SRAIW))))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__66 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__66 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (FENCE_TSO
                                                                                                                                ())))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__66
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__66
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__66
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__66
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__66
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                let succ : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__66
                                                                                                                                    23
                                                                                                                                    20)
                                                                                                                                let pred : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__66
                                                                                                                                    27
                                                                                                                                    24)
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__66
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__66
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                let fm : (BitVec 4) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__66
                                                                                                                                    31
                                                                                                                                    28)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      (FENCE
                                                                                                                                        (fm, pred, succ, rs, rd)))))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__29 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__29 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  (ECALL
                                                                                                                                    ())))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__29 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (MRET
                                                                                                                                        ())))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__29 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          (SRET
                                                                                                                                            ())))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__29 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (EBREAK
                                                                                                                                                ())))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__29 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (WFI
                                                                                                                                                    ())))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__29
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__29
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__29
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__29
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__29
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__29
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              (SFENCE_VMA
                                                                                                                                                                (rs1, rs2))))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__26 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping83_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__26
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping82_ : (BitVec 2) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__26
                                                                                                                                         13
                                                                                                                                         12)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__26
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_csrop_backwards_matches
                                                                                                                                           mapping82_) && (encdec_reg_backwards_matches
                                                                                                                                           mapping83_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__26
                                                                                                                                           14
                                                                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__26
                                                                                                                                           6
                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__26
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    let mapping83_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__26
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping82_ : (BitVec 2) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__26
                                                                                                                                        13
                                                                                                                                        12)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__26
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    let csr : (BitVec 12) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__26
                                                                                                                                        31
                                                                                                                                        20)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_csrop_backwards
                                                                                                                                        mapping82_)), (← (encdec_reg_backwards
                                                                                                                                        mapping83_))) with
                                                                                                                                    | (rs1, op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              (CSRReg
                                                                                                                                                (csr, rs1, rd, op))))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__23 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__23
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping84_ : (BitVec 2) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__23
                                                                                                                                             13
                                                                                                                                             12)
                                                                                                                                         ((encdec_csrop_backwards_matches
                                                                                                                                             mapping84_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping85_))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__23
                                                                                                                                               14
                                                                                                                                               14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                               v__23
                                                                                                                                               6
                                                                                                                                               0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let csr : (BitVec 12) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__23
                                                                                                                                            31
                                                                                                                                            20)
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__23
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping84_ : (BitVec 2) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__23
                                                                                                                                            13
                                                                                                                                            12)
                                                                                                                                        let imm : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__23
                                                                                                                                            19
                                                                                                                                            15)
                                                                                                                                        let csr : (BitVec 12) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__23
                                                                                                                                            31
                                                                                                                                            20)
                                                                                                                                        match ((← (encdec_csrop_backwards
                                                                                                                                            mapping84_)), (← (encdec_reg_backwards
                                                                                                                                            mapping85_))) with
                                                                                                                                        | (op, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_Zicsr)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  (CSRImm
                                                                                                                                                    (csr, imm, rd, op))))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__19 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping86_ : (BitVec 12) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__19
                                                                                                                                                 31
                                                                                                                                                 20)
                                                                                                                                             let mapping87_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__19
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping86_ : (BitVec 12) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__19
                                                                                                                                                 31
                                                                                                                                                 20)
                                                                                                                                             ((encdec_cbop_backwards_matches
                                                                                                                                                 mapping86_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping87_))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__19
                                                                                                                                                 14
                                                                                                                                                 0) == (0b010000000001111#15 : (BitVec 15)))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping86_ : (BitVec 12) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__19
                                                                                                                                                31
                                                                                                                                                20)
                                                                                                                                            let mapping87_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__19
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping86_ : (BitVec 12) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__19
                                                                                                                                                31
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_cbop_backwards
                                                                                                                                                mapping86_)), (← (encdec_reg_backwards
                                                                                                                                                mapping87_))) with
                                                                                                                                            | (cbop, rs1) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_Zicbom)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (ZICBOM
                                                                                                                                                        (cbop, rs1))))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__14 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__14
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 (encdec_reg_backwards_matches
                                                                                                                                                   mapping88_)) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__14
                                                                                                                                                       31
                                                                                                                                                       20) == (0x004#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb
                                                                                                                                                       v__14
                                                                                                                                                       14
                                                                                                                                                       0) == (0b010000000001111#15 : (BitVec 15))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping88_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__14
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let rs1 ← do
                                                                                                                                                  (encdec_reg_backwards
                                                                                                                                                    mapping88_)
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_Zicboz)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      (ZICBOZ
                                                                                                                                                        rs1)))
                                                                                                                                                else
                                                                                                                                                  (pure none))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (match head_exp_ with
                                                                                                                                            | s =>
                                                                                                                                              (pure (ILLEGAL
                                                                                                                                                  s)))))))))))))))))))))))))))))))))))))

def encdec_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .LPAD lpl =>
    (do
      if ((← (currentlyEnabled Ext_Zicfilp)) : Bool)
      then (pure true)
      else (pure false))
  | .UTYPE (imm, rd, op) => (pure true)
  | .JAL (v__182, rd) =>
    (if (((Sail.BitVec.extractLsb v__182 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .JALR (imm, rs1, rd) => (pure true)
  | .BTYPE (v__184, rs2, rs1, op) =>
    (if (((Sail.BitVec.extractLsb v__184 0 0) == (0#1 : (BitVec 1))) : Bool)
    then (pure true)
    else (pure false))
  | .ITYPE (imm, rs1, rd, op) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SLLI) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SRLI) => (pure true)
  | .SHIFTIOP (shamt, rs1, rd, .SRAI) => (pure true)
  | .RTYPE (rs2, rs1, rd, .ADD) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLT) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLTU) => (pure true)
  | .RTYPE (rs2, rs1, rd, .AND) => (pure true)
  | .RTYPE (rs2, rs1, rd, .OR) => (pure true)
  | .RTYPE (rs2, rs1, rd, .XOR) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SLL) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SRL) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SUB) => (pure true)
  | .RTYPE (rs2, rs1, rd, .SRA) => (pure true)
  | .LOAD (imm, rs1, rd, is_unsigned, width) =>
    (if ((valid_load_encdec width is_unsigned) : Bool)
    then (pure true)
    else (pure false))
  | .STORE (imm, rs2, rs1, width) => (pure true)
  | .ADDIW (imm, rs1, rd) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .ADDW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SUBW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SLLW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SRLW) => (pure true)
  | .RTYPEW (rs2, rs1, rd, .SRAW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SLLIW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SRLIW) => (pure true)
  | .SHIFTIWOP (shamt, rs1, rd, .SRAIW) => (pure true)
  | .FENCE_TSO () => (pure true)
  | .FENCE (fm, pred, succ, rs, rd) => (pure true)
  | .ECALL () => (pure true)
  | .MRET () => (pure true)
  | .SRET () => (pure true)
  | .EBREAK () => (pure true)
  | .WFI () => (pure true)
  | .SFENCE_VMA (rs1, rs2) =>
    (do
      if (((← (virtual_memory_supported ())) || (not (true : Bool))) : Bool)
      then (pure true)
      else (pure false))
  | .CSRReg (csr, rs1, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .CSRImm (csr, imm, rd, op) =>
    (do
      if ((← (currentlyEnabled Ext_Zicsr)) : Bool)
      then (pure true)
      else (pure false))
  | .ZICBOM (cbop, rs1) =>
    (do
      if ((← (currentlyEnabled Ext_Zicbom)) : Bool)
      then (pure true)
      else (pure false))
  | .ZICBOZ rs1 =>
    (do
      if ((← (currentlyEnabled Ext_Zicboz)) : Bool)
      then (pure true)
      else (pure false))
  | .ILLEGAL s => (pure true)
  | _ => (pure false)

def encdec_backwards_matches (arg_ : (BitVec 32)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__350 := head_exp_
    if (((← (currentlyEnabled Ext_Zicfilp)) && ((Sail.BitVec.extractLsb v__350 11 0) == (0x017#12 : (BitVec 12)))) : Bool)
    then (pure (some true))
    else
      (do
        if ((let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__350 6 0)
           let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__350 11 7)
           ((encdec_reg_backwards_matches mapping0_) && (encdec_uop_backwards_matches mapping1_))) : Bool)
        then
          (do
            let mapping1_ : (BitVec 7) := (Sail.BitVec.extractLsb v__350 6 0)
            let mapping0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__350 11 7)
            match ((← (encdec_reg_backwards mapping0_)), (← (encdec_uop_backwards mapping1_))) with
            | (rd, op) => (pure (some true)))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__348 := head_exp_
        if (((let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__348 11 7)
             (encdec_reg_backwards_matches mapping2_)) && ((Sail.BitVec.extractLsb v__348 6 0) == (0b1101111#7 : (BitVec 7)))) : Bool)
        then
          (do
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__348 31 31)
            let mapping2_ : (BitVec 5) := (Sail.BitVec.extractLsb v__348 11 7)
            let imm_9_0_ : (BitVec 10) := (Sail.BitVec.extractLsb v__348 30 21)
            let imm_19_19_ : (BitVec 1) := (Sail.BitVec.extractLsb v__348 31 31)
            let imm_18_11_ : (BitVec 8) := (Sail.BitVec.extractLsb v__348 19 12)
            let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__348 20 20)
            match (← (encdec_reg_backwards mapping2_)) with
            | rd =>
              (pure (some
                  (let imm := (((imm_19_19_ +++ imm_18_11_) +++ imm_10_10_) +++ imm_9_0_)
                  true))))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__345 := head_exp_
            if (((let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 11 7)
                 let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 19 15)
                 ((encdec_reg_backwards_matches mapping3_) && (encdec_reg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__345 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__345 6 0) == (0b1100111#7 : (BitVec 7))))) : Bool)
            then
              (do
                let mapping4_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 11 7)
                let mapping3_ : (BitVec 5) := (Sail.BitVec.extractLsb v__345 19 15)
                match ((← (encdec_reg_backwards mapping3_)), (← (encdec_reg_backwards mapping4_))) with
                | (rs1, rd) => (pure (some true)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__343 := head_exp_
                if (((let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__343 14 12)
                     let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__343 19 15)
                     let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__343 24 20)
                     ((encdec_reg_backwards_matches mapping5_) && ((encdec_reg_backwards_matches
                           mapping6_) && (encdec_bop_backwards_matches mapping7_)))) && ((Sail.BitVec.extractLsb
                         v__343 6 0) == (0b1100011#7 : (BitVec 7)))) : Bool)
                then
                  (do
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__343 31 31)
                    let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__343 14 12)
                    let mapping6_ : (BitVec 5) := (Sail.BitVec.extractLsb v__343 19 15)
                    let mapping5_ : (BitVec 5) := (Sail.BitVec.extractLsb v__343 24 20)
                    let imm_9_4_ : (BitVec 6) := (Sail.BitVec.extractLsb v__343 30 25)
                    let imm_3_0_ : (BitVec 4) := (Sail.BitVec.extractLsb v__343 11 8)
                    let imm_11_11_ : (BitVec 1) := (Sail.BitVec.extractLsb v__343 31 31)
                    let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__343 7 7)
                    match ((← (encdec_reg_backwards mapping5_)), (← (encdec_reg_backwards
                        mapping6_)), (← (encdec_bop_backwards mapping7_))) with
                    | (rs2, rs1, op) =>
                      (pure (some
                          (let imm := (((imm_11_11_ +++ imm_10_10_) +++ imm_9_4_) +++ imm_3_0_)
                          true))))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__341 := head_exp_
                    if (((let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__341 14 12)
                         let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 19 15)
                         let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 11 7)
                         ((encdec_reg_backwards_matches mapping8_) && ((encdec_iop_backwards_matches
                               mapping9_) && (encdec_reg_backwards_matches mapping10_)))) && ((Sail.BitVec.extractLsb
                             v__341 6 0) == (0b0010011#7 : (BitVec 7)))) : Bool)
                    then
                      (do
                        let mapping9_ : (BitVec 3) := (Sail.BitVec.extractLsb v__341 14 12)
                        let mapping8_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 19 15)
                        let mapping10_ : (BitVec 5) := (Sail.BitVec.extractLsb v__341 11 7)
                        match ((← (encdec_reg_backwards mapping8_)), (← (encdec_iop_backwards
                            mapping9_)), (← (encdec_reg_backwards mapping10_))) with
                        | (rs1, op, rd) => (pure (some true)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__337 := head_exp_
                        if (((let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 11 7)
                             let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 19 15)
                             ((encdec_reg_backwards_matches mapping11_) && (encdec_reg_backwards_matches
                                 mapping12_))) && (((Sail.BitVec.extractLsb v__337 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                     v__337 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                     v__337 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                        then
                          (do
                            let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__337 25 20)
                            let mapping12_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 11 7)
                            let mapping11_ : (BitVec 5) := (Sail.BitVec.extractLsb v__337 19 15)
                            match ((← (encdec_reg_backwards mapping11_)), (← (encdec_reg_backwards
                                mapping12_))) with
                            | (rs1, rd) =>
                              (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                              then (pure (some true))
                              else (pure none)))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__333 := head_exp_
                            if (((let mapping14_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__333 11 7)
                                 let mapping13_ : (BitVec 5) :=
                                   (Sail.BitVec.extractLsb v__333 19 15)
                                 ((encdec_reg_backwards_matches mapping13_) && (encdec_reg_backwards_matches
                                     mapping14_))) && (((Sail.BitVec.extractLsb v__333 31 26) == (0b000000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                         v__333 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                         v__333 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                            then
                              (do
                                let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__333 25 20)
                                let mapping14_ : (BitVec 5) := (Sail.BitVec.extractLsb v__333 11 7)
                                let mapping13_ : (BitVec 5) := (Sail.BitVec.extractLsb v__333 19 15)
                                match ((← (encdec_reg_backwards mapping13_)), (← (encdec_reg_backwards
                                    mapping14_))) with
                                | (rs1, rd) =>
                                  (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                  then (pure (some true))
                                  else (pure none)))
                            else (pure none)) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__329 := head_exp_
                                if (((let mapping16_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__329 11 7)
                                     let mapping15_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__329 19 15)
                                     ((encdec_reg_backwards_matches mapping15_) && (encdec_reg_backwards_matches
                                         mapping16_))) && (((Sail.BitVec.extractLsb v__329 31 26) == (0b010000#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                             v__329 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                             v__329 6 0) == (0b0010011#7 : (BitVec 7)))))) : Bool)
                                then
                                  (do
                                    let shamt : (BitVec 6) := (Sail.BitVec.extractLsb v__329 25 20)
                                    let mapping16_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__329 11 7)
                                    let mapping15_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__329 19 15)
                                    match ((← (encdec_reg_backwards mapping15_)), (← (encdec_reg_backwards
                                        mapping16_))) with
                                    | (rs1, rd) =>
                                      (if (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) : Bool)
                                      then (pure (some true))
                                      else (pure none)))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__325 := head_exp_
                                    if (((let mapping19_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__325 11 7)
                                         let mapping18_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__325 19 15)
                                         let mapping17_ : (BitVec 5) :=
                                           (Sail.BitVec.extractLsb v__325 24 20)
                                         ((encdec_reg_backwards_matches mapping17_) && ((encdec_reg_backwards_matches
                                               mapping18_) && (encdec_reg_backwards_matches
                                               mapping19_)))) && (((Sail.BitVec.extractLsb v__325 31
                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                 v__325 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                 v__325 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                    then
                                      (do
                                        let mapping19_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__325 11 7)
                                        let mapping18_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__325 19 15)
                                        let mapping17_ : (BitVec 5) :=
                                          (Sail.BitVec.extractLsb v__325 24 20)
                                        match ((← (encdec_reg_backwards mapping17_)), (← (encdec_reg_backwards
                                            mapping18_)), (← (encdec_reg_backwards mapping19_))) with
                                        | (rs2, rs1, rd) => (pure (some true)))
                                    else (pure none)) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__321 := head_exp_
                                        if (((let mapping22_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__321 11 7)
                                             let mapping21_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__321 19 15)
                                             let mapping20_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__321 24 20)
                                             ((encdec_reg_backwards_matches mapping20_) && ((encdec_reg_backwards_matches
                                                   mapping21_) && (encdec_reg_backwards_matches
                                                   mapping22_)))) && (((Sail.BitVec.extractLsb
                                                   v__321 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                     v__321 14 12) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                     v__321 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                        then
                                          (do
                                            let mapping22_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__321 11 7)
                                            let mapping21_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__321 19 15)
                                            let mapping20_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__321 24 20)
                                            match ((← (encdec_reg_backwards mapping20_)), (← (encdec_reg_backwards
                                                mapping21_)), (← (encdec_reg_backwards mapping22_))) with
                                            | (rs2, rs1, rd) => (pure (some true)))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__317 := head_exp_
                                            if (((let mapping25_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__317 11 7)
                                                 let mapping24_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__317 19 15)
                                                 let mapping23_ : (BitVec 5) :=
                                                   (Sail.BitVec.extractLsb v__317 24 20)
                                                 ((encdec_reg_backwards_matches mapping23_) && ((encdec_reg_backwards_matches
                                                       mapping24_) && (encdec_reg_backwards_matches
                                                       mapping25_)))) && (((Sail.BitVec.extractLsb
                                                       v__317 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                         v__317 14 12) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                         v__317 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                            then
                                              (do
                                                let mapping25_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__317 11 7)
                                                let mapping24_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__317 19 15)
                                                let mapping23_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__317 24 20)
                                                match ((← (encdec_reg_backwards mapping23_)), (← (encdec_reg_backwards
                                                    mapping24_)), (← (encdec_reg_backwards
                                                    mapping25_))) with
                                                | (rs2, rs1, rd) => (pure (some true)))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__313 := head_exp_
                                                if (((let mapping28_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__313 11 7)
                                                     let mapping27_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__313 19 15)
                                                     let mapping26_ : (BitVec 5) :=
                                                       (Sail.BitVec.extractLsb v__313 24 20)
                                                     ((encdec_reg_backwards_matches mapping26_) && ((encdec_reg_backwards_matches
                                                           mapping27_) && (encdec_reg_backwards_matches
                                                           mapping28_)))) && (((Sail.BitVec.extractLsb
                                                           v__313 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                             v__313 14 12) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                             v__313 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping28_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__313 11 7)
                                                    let mapping27_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__313 19 15)
                                                    let mapping26_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__313 24 20)
                                                    match ((← (encdec_reg_backwards mapping26_)), (← (encdec_reg_backwards
                                                        mapping27_)), (← (encdec_reg_backwards
                                                        mapping28_))) with
                                                    | (rs2, rs1, rd) => (pure (some true)))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__309 := head_exp_
                                                    if (((let mapping31_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__309 11 7)
                                                         let mapping30_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__309 19 15)
                                                         let mapping29_ : (BitVec 5) :=
                                                           (Sail.BitVec.extractLsb v__309 24 20)
                                                         ((encdec_reg_backwards_matches mapping29_) && ((encdec_reg_backwards_matches
                                                               mapping30_) && (encdec_reg_backwards_matches
                                                               mapping31_)))) && (((Sail.BitVec.extractLsb
                                                               v__309 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                 v__309 14 12) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                 v__309 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping31_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__309 11 7)
                                                        let mapping30_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__309 19 15)
                                                        let mapping29_ : (BitVec 5) :=
                                                          (Sail.BitVec.extractLsb v__309 24 20)
                                                        match ((← (encdec_reg_backwards mapping29_)), (← (encdec_reg_backwards
                                                            mapping30_)), (← (encdec_reg_backwards
                                                            mapping31_))) with
                                                        | (rs2, rs1, rd) => (pure (some true)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__305 := head_exp_
                                                        if (((let mapping34_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__305 11 7)
                                                             let mapping33_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__305 19 15)
                                                             let mapping32_ : (BitVec 5) :=
                                                               (Sail.BitVec.extractLsb v__305 24 20)
                                                             ((encdec_reg_backwards_matches
                                                                 mapping32_) && ((encdec_reg_backwards_matches
                                                                   mapping33_) && (encdec_reg_backwards_matches
                                                                   mapping34_)))) && (((Sail.BitVec.extractLsb
                                                                   v__305 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                     v__305 14 12) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                     v__305 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping34_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__305 11 7)
                                                            let mapping33_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__305 19 15)
                                                            let mapping32_ : (BitVec 5) :=
                                                              (Sail.BitVec.extractLsb v__305 24 20)
                                                            match ((← (encdec_reg_backwards
                                                                mapping32_)), (← (encdec_reg_backwards
                                                                mapping33_)), (← (encdec_reg_backwards
                                                                mapping34_))) with
                                                            | (rs2, rs1, rd) => (pure (some true)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__301 := head_exp_
                                                            if (((let mapping37_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__301 11
                                                                     7)
                                                                 let mapping36_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__301 19
                                                                     15)
                                                                 let mapping35_ : (BitVec 5) :=
                                                                   (Sail.BitVec.extractLsb v__301 24
                                                                     20)
                                                                 ((encdec_reg_backwards_matches
                                                                     mapping35_) && ((encdec_reg_backwards_matches
                                                                       mapping36_) && (encdec_reg_backwards_matches
                                                                       mapping37_)))) && (((Sail.BitVec.extractLsb
                                                                       v__301 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                         v__301 14 12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                         v__301 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping37_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__301 11
                                                                    7)
                                                                let mapping36_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__301 19
                                                                    15)
                                                                let mapping35_ : (BitVec 5) :=
                                                                  (Sail.BitVec.extractLsb v__301 24
                                                                    20)
                                                                match ((← (encdec_reg_backwards
                                                                    mapping35_)), (← (encdec_reg_backwards
                                                                    mapping36_)), (← (encdec_reg_backwards
                                                                    mapping37_))) with
                                                                | (rs2, rs1, rd) =>
                                                                  (pure (some true)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__297 := head_exp_
                                                                if (((let mapping40_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__297 11 7)
                                                                     let mapping39_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__297 19 15)
                                                                     let mapping38_ : (BitVec 5) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__297 24 20)
                                                                     ((encdec_reg_backwards_matches
                                                                         mapping38_) && ((encdec_reg_backwards_matches
                                                                           mapping39_) && (encdec_reg_backwards_matches
                                                                           mapping40_)))) && (((Sail.BitVec.extractLsb
                                                                           v__297 31 25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                             v__297 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                             v__297 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping40_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__297
                                                                        11 7)
                                                                    let mapping39_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__297
                                                                        19 15)
                                                                    let mapping38_ : (BitVec 5) :=
                                                                      (Sail.BitVec.extractLsb v__297
                                                                        24 20)
                                                                    match ((← (encdec_reg_backwards
                                                                        mapping38_)), (← (encdec_reg_backwards
                                                                        mapping39_)), (← (encdec_reg_backwards
                                                                        mapping40_))) with
                                                                    | (rs2, rs1, rd) =>
                                                                      (pure (some true)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__293 := head_exp_
                                                                    if (((let mapping43_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__293 11 7)
                                                                         let mapping42_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__293 19 15)
                                                                         let mapping41_ : (BitVec 5) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__293 24 20)
                                                                         ((encdec_reg_backwards_matches
                                                                             mapping41_) && ((encdec_reg_backwards_matches
                                                                               mapping42_) && (encdec_reg_backwards_matches
                                                                               mapping43_)))) && (((Sail.BitVec.extractLsb
                                                                               v__293 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                 v__293 14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                 v__293 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping43_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__293 11 7)
                                                                        let mapping42_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__293 19 15)
                                                                        let mapping41_ : (BitVec 5) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__293 24 20)
                                                                        match ((← (encdec_reg_backwards
                                                                            mapping41_)), (← (encdec_reg_backwards
                                                                            mapping42_)), (← (encdec_reg_backwards
                                                                            mapping43_))) with
                                                                        | (rs2, rs1, rd) =>
                                                                          (pure (some true)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__289 := head_exp_
                                                                        if (((let mapping46_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__289 11 7)
                                                                             let mapping45_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__289 19 15)
                                                                             let mapping44_ : (BitVec 5) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__289 24 20)
                                                                             ((encdec_reg_backwards_matches
                                                                                 mapping44_) && ((encdec_reg_backwards_matches
                                                                                   mapping45_) && (encdec_reg_backwards_matches
                                                                                   mapping46_)))) && (((Sail.BitVec.extractLsb
                                                                                   v__289 31 25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                     v__289 14 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                     v__289 6 0) == (0b0110011#7 : (BitVec 7)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping46_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__289 11 7)
                                                                            let mapping45_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__289 19 15)
                                                                            let mapping44_ : (BitVec 5) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__289 24 20)
                                                                            match ((← (encdec_reg_backwards
                                                                                mapping44_)), (← (encdec_reg_backwards
                                                                                mapping45_)), (← (encdec_reg_backwards
                                                                                mapping46_))) with
                                                                            | (rs2, rs1, rd) =>
                                                                              (pure (some true)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__287 := head_exp_
                                                                            if (((let mapping50_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__287 11 7)
                                                                                 let mapping49_ : (BitVec 2) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__287 13 12)
                                                                                 let mapping48_ : (BitVec 1) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__287 14 14)
                                                                                 let mapping47_ : (BitVec 5) :=
                                                                                   (Sail.BitVec.extractLsb
                                                                                     v__287 19 15)
                                                                                 ((encdec_reg_backwards_matches
                                                                                     mapping47_) && ((bool_bit_backwards_matches
                                                                                       mapping48_) && ((width_enc_backwards_matches
                                                                                         mapping49_) && (encdec_reg_backwards_matches
                                                                                         mapping50_))))) && ((Sail.BitVec.extractLsb
                                                                                     v__287 6 0) == (0b0000011#7 : (BitVec 7)))) : Bool)
                                                                            then
                                                                              (do
                                                                                let mapping50_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__287 11 7)
                                                                                let mapping49_ : (BitVec 2) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__287 13 12)
                                                                                let mapping48_ : (BitVec 1) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__287 14 14)
                                                                                let mapping47_ : (BitVec 5) :=
                                                                                  (Sail.BitVec.extractLsb
                                                                                    v__287 19 15)
                                                                                match ((← (encdec_reg_backwards
                                                                                    mapping47_)), (bool_bit_backwards
                                                                                  mapping48_), (width_enc_backwards
                                                                                  mapping49_), (← (encdec_reg_backwards
                                                                                    mapping50_))) with
                                                                                | (rs1, is_unsigned, width, rd) =>
                                                                                  (if ((valid_load_encdec
                                                                                       width
                                                                                       is_unsigned) : Bool)
                                                                                  then
                                                                                    (pure (some true))
                                                                                  else (pure none)))
                                                                            else (pure none)) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__284 :=
                                                                                  head_exp_
                                                                                if (((let mapping53_ : (BitVec 2) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__284 13
                                                                                         12)
                                                                                     let mapping52_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__284 19
                                                                                         15)
                                                                                     let mapping51_ : (BitVec 5) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__284 24
                                                                                         20)
                                                                                     ((encdec_reg_backwards_matches
                                                                                         mapping51_) && ((encdec_reg_backwards_matches
                                                                                           mapping52_) && (width_enc_backwards_matches
                                                                                           mapping53_)))) && (((Sail.BitVec.extractLsb
                                                                                           v__284 14
                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                           v__284 6
                                                                                           0) == (0b0100011#7 : (BitVec 7))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__284 31 25)
                                                                                    let mapping53_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__284 13 12)
                                                                                    let mapping52_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__284 19 15)
                                                                                    let mapping51_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__284 24 20)
                                                                                    let imm_4_0_ : (BitVec 5) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__284 11 7)
                                                                                    let imm_11_5_ : (BitVec 7) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__284 31 25)
                                                                                    match ((← (encdec_reg_backwards
                                                                                        mapping51_)), (← (encdec_reg_backwards
                                                                                        mapping52_)), (width_enc_backwards
                                                                                      mapping53_)) with
                                                                                    | (rs2, rs1, width) =>
                                                                                      (if ((let imm :=
                                                                                           (imm_11_5_ +++ imm_4_0_)
                                                                                         (width ≤b xlen_bytes)) : Bool)
                                                                                      then
                                                                                        (pure (some
                                                                                            (let imm :=
                                                                                              (imm_11_5_ +++ imm_4_0_)
                                                                                            true)))
                                                                                      else
                                                                                        (pure none)))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__281 :=
                                                                                      head_exp_
                                                                                    if (((let mapping55_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__281
                                                                                             11 7)
                                                                                         let mapping54_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__281
                                                                                             19 15)
                                                                                         ((encdec_reg_backwards_matches
                                                                                             mapping54_) && (encdec_reg_backwards_matches
                                                                                             mapping55_))) && (((Sail.BitVec.extractLsb
                                                                                               v__281
                                                                                               14 12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__281
                                                                                               6 0) == (0b0011011#7 : (BitVec 7))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let mapping55_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__281
                                                                                            11 7)
                                                                                        let mapping54_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__281
                                                                                            19 15)
                                                                                        match ((← (encdec_reg_backwards
                                                                                            mapping54_)), (← (encdec_reg_backwards
                                                                                            mapping55_))) with
                                                                                        | (rs1, rd) =>
                                                                                          (if ((xlen == 64) : Bool)
                                                                                          then
                                                                                            (pure (some
                                                                                                true))
                                                                                          else
                                                                                            (pure none)))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__277 :=
                                                                                          head_exp_
                                                                                        if (((let mapping58_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__277
                                                                                                 11
                                                                                                 7)
                                                                                             let mapping57_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__277
                                                                                                 19
                                                                                                 15)
                                                                                             let mapping56_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__277
                                                                                                 24
                                                                                                 20)
                                                                                             ((encdec_reg_backwards_matches
                                                                                                 mapping56_) && ((encdec_reg_backwards_matches
                                                                                                   mapping57_) && (encdec_reg_backwards_matches
                                                                                                   mapping58_)))) && (((Sail.BitVec.extractLsb
                                                                                                   v__277
                                                                                                   31
                                                                                                   25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                     v__277
                                                                                                     14
                                                                                                     12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                     v__277
                                                                                                     6
                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let mapping58_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__277
                                                                                                11 7)
                                                                                            let mapping57_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__277
                                                                                                19
                                                                                                15)
                                                                                            let mapping56_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__277
                                                                                                24
                                                                                                20)
                                                                                            match ((← (encdec_reg_backwards
                                                                                                mapping56_)), (← (encdec_reg_backwards
                                                                                                mapping57_)), (← (encdec_reg_backwards
                                                                                                mapping58_))) with
                                                                                            | (rs2, rs1, rd) =>
                                                                                              (if ((xlen == 64) : Bool)
                                                                                              then
                                                                                                (pure (some
                                                                                                    true))
                                                                                              else
                                                                                                (pure none)))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__273 :=
                                                                                              head_exp_
                                                                                            if (((let mapping61_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__273
                                                                                                     11
                                                                                                     7)
                                                                                                 let mapping60_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__273
                                                                                                     19
                                                                                                     15)
                                                                                                 let mapping59_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__273
                                                                                                     24
                                                                                                     20)
                                                                                                 ((encdec_reg_backwards_matches
                                                                                                     mapping59_) && ((encdec_reg_backwards_matches
                                                                                                       mapping60_) && (encdec_reg_backwards_matches
                                                                                                       mapping61_)))) && (((Sail.BitVec.extractLsb
                                                                                                       v__273
                                                                                                       31
                                                                                                       25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                         v__273
                                                                                                         14
                                                                                                         12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                         v__273
                                                                                                         6
                                                                                                         0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let mapping61_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__273
                                                                                                    11
                                                                                                    7)
                                                                                                let mapping60_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__273
                                                                                                    19
                                                                                                    15)
                                                                                                let mapping59_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__273
                                                                                                    24
                                                                                                    20)
                                                                                                match ((← (encdec_reg_backwards
                                                                                                    mapping59_)), (← (encdec_reg_backwards
                                                                                                    mapping60_)), (← (encdec_reg_backwards
                                                                                                    mapping61_))) with
                                                                                                | (rs2, rs1, rd) =>
                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                  then
                                                                                                    (pure (some
                                                                                                        true))
                                                                                                  else
                                                                                                    (pure none)))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__269 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping64_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__269
                                                                                                         11
                                                                                                         7)
                                                                                                     let mapping63_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__269
                                                                                                         19
                                                                                                         15)
                                                                                                     let mapping62_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__269
                                                                                                         24
                                                                                                         20)
                                                                                                     ((encdec_reg_backwards_matches
                                                                                                         mapping62_) && ((encdec_reg_backwards_matches
                                                                                                           mapping63_) && (encdec_reg_backwards_matches
                                                                                                           mapping64_)))) && (((Sail.BitVec.extractLsb
                                                                                                           v__269
                                                                                                           31
                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                             v__269
                                                                                                             14
                                                                                                             12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                             v__269
                                                                                                             6
                                                                                                             0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let mapping64_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__269
                                                                                                        11
                                                                                                        7)
                                                                                                    let mapping63_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__269
                                                                                                        19
                                                                                                        15)
                                                                                                    let mapping62_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__269
                                                                                                        24
                                                                                                        20)
                                                                                                    match ((← (encdec_reg_backwards
                                                                                                        mapping62_)), (← (encdec_reg_backwards
                                                                                                        mapping63_)), (← (encdec_reg_backwards
                                                                                                        mapping64_))) with
                                                                                                    | (rs2, rs1, rd) =>
                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                      then
                                                                                                        (pure (some
                                                                                                            true))
                                                                                                      else
                                                                                                        (pure none)))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__265 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping67_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__265
                                                                                                             11
                                                                                                             7)
                                                                                                         let mapping66_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__265
                                                                                                             19
                                                                                                             15)
                                                                                                         let mapping65_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__265
                                                                                                             24
                                                                                                             20)
                                                                                                         ((encdec_reg_backwards_matches
                                                                                                             mapping65_) && ((encdec_reg_backwards_matches
                                                                                                               mapping66_) && (encdec_reg_backwards_matches
                                                                                                               mapping67_)))) && (((Sail.BitVec.extractLsb
                                                                                                               v__265
                                                                                                               31
                                                                                                               25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                 v__265
                                                                                                                 14
                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                 v__265
                                                                                                                 6
                                                                                                                 0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let mapping67_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__265
                                                                                                            11
                                                                                                            7)
                                                                                                        let mapping66_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__265
                                                                                                            19
                                                                                                            15)
                                                                                                        let mapping65_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__265
                                                                                                            24
                                                                                                            20)
                                                                                                        match ((← (encdec_reg_backwards
                                                                                                            mapping65_)), (← (encdec_reg_backwards
                                                                                                            mapping66_)), (← (encdec_reg_backwards
                                                                                                            mapping67_))) with
                                                                                                        | (rs2, rs1, rd) =>
                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                          then
                                                                                                            (pure (some
                                                                                                                true))
                                                                                                          else
                                                                                                            (pure none)))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__261 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping70_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__261
                                                                                                                 11
                                                                                                                 7)
                                                                                                             let mapping69_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__261
                                                                                                                 19
                                                                                                                 15)
                                                                                                             let mapping68_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__261
                                                                                                                 24
                                                                                                                 20)
                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                 mapping68_) && ((encdec_reg_backwards_matches
                                                                                                                   mapping69_) && (encdec_reg_backwards_matches
                                                                                                                   mapping70_)))) && (((Sail.BitVec.extractLsb
                                                                                                                   v__261
                                                                                                                   31
                                                                                                                   25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                     v__261
                                                                                                                     14
                                                                                                                     12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                     v__261
                                                                                                                     6
                                                                                                                     0) == (0b0111011#7 : (BitVec 7)))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping70_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__261
                                                                                                                11
                                                                                                                7)
                                                                                                            let mapping69_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__261
                                                                                                                19
                                                                                                                15)
                                                                                                            let mapping68_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__261
                                                                                                                24
                                                                                                                20)
                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                mapping68_)), (← (encdec_reg_backwards
                                                                                                                mapping69_)), (← (encdec_reg_backwards
                                                                                                                mapping70_))) with
                                                                                                            | (rs2, rs1, rd) =>
                                                                                                              (if ((xlen == 64) : Bool)
                                                                                                              then
                                                                                                                (pure (some
                                                                                                                    true))
                                                                                                              else
                                                                                                                (pure none)))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__257 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping72_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__257
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 let mapping71_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__257
                                                                                                                     19
                                                                                                                     15)
                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                     mapping71_) && (encdec_reg_backwards_matches
                                                                                                                     mapping72_))) && (((Sail.BitVec.extractLsb
                                                                                                                       v__257
                                                                                                                       31
                                                                                                                       25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                         v__257
                                                                                                                         14
                                                                                                                         12) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                         v__257
                                                                                                                         6
                                                                                                                         0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping72_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__257
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let mapping71_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__257
                                                                                                                    19
                                                                                                                    15)
                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                    mapping71_)), (← (encdec_reg_backwards
                                                                                                                    mapping72_))) with
                                                                                                                | (rs1, rd) =>
                                                                                                                  (if ((xlen == 64) : Bool)
                                                                                                                  then
                                                                                                                    (pure (some
                                                                                                                        true))
                                                                                                                  else
                                                                                                                    (pure none)))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__253 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping74_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__253
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     let mapping73_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__253
                                                                                                                         19
                                                                                                                         15)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping73_) && (encdec_reg_backwards_matches
                                                                                                                         mapping74_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__253
                                                                                                                           31
                                                                                                                           25) == (0b0000000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                             v__253
                                                                                                                             14
                                                                                                                             12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                             v__253
                                                                                                                             6
                                                                                                                             0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping74_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__253
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    let mapping73_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__253
                                                                                                                        19
                                                                                                                        15)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping73_)), (← (encdec_reg_backwards
                                                                                                                        mapping74_))) with
                                                                                                                    | (rs1, rd) =>
                                                                                                                      (if ((xlen == 64) : Bool)
                                                                                                                      then
                                                                                                                        (pure (some
                                                                                                                            true))
                                                                                                                      else
                                                                                                                        (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__249 :=
                                                                                                                      head_exp_
                                                                                                                    if (((let mapping76_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__249
                                                                                                                             11
                                                                                                                             7)
                                                                                                                         let mapping75_ : (BitVec 5) :=
                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                             v__249
                                                                                                                             19
                                                                                                                             15)
                                                                                                                         ((encdec_reg_backwards_matches
                                                                                                                             mapping75_) && (encdec_reg_backwards_matches
                                                                                                                             mapping76_))) && (((Sail.BitVec.extractLsb
                                                                                                                               v__249
                                                                                                                               31
                                                                                                                               25) == (0b0100000#7 : (BitVec 7))) && (((Sail.BitVec.extractLsb
                                                                                                                                 v__249
                                                                                                                                 14
                                                                                                                                 12) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                 v__249
                                                                                                                                 6
                                                                                                                                 0) == (0b0011011#7 : (BitVec 7)))))) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let mapping76_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__249
                                                                                                                            11
                                                                                                                            7)
                                                                                                                        let mapping75_ : (BitVec 5) :=
                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                            v__249
                                                                                                                            19
                                                                                                                            15)
                                                                                                                        match ((← (encdec_reg_backwards
                                                                                                                            mapping75_)), (← (encdec_reg_backwards
                                                                                                                            mapping76_))) with
                                                                                                                        | (rs1, rd) =>
                                                                                                                          (if ((xlen == 64) : Bool)
                                                                                                                          then
                                                                                                                            (pure (some
                                                                                                                                true))
                                                                                                                          else
                                                                                                                            (pure none)))
                                                                                                                    else
                                                                                                                      (pure none)) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (do
                                                                                                                      match (← do
                                                                                                                        let v__238 :=
                                                                                                                          head_exp_
                                                                                                                        if ((v__238 == (0x8330000F#32 : (BitVec 32))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (do
                                                                                                                            if (((let mapping78_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__238
                                                                                                                                     11
                                                                                                                                     7)
                                                                                                                                 let mapping77_ : (BitVec 5) :=
                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                     v__238
                                                                                                                                     19
                                                                                                                                     15)
                                                                                                                                 ((encdec_reg_backwards_matches
                                                                                                                                     mapping77_) && (encdec_reg_backwards_matches
                                                                                                                                     mapping78_))) && (((Sail.BitVec.extractLsb
                                                                                                                                       v__238
                                                                                                                                       14
                                                                                                                                       12) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                                                       v__238
                                                                                                                                       6
                                                                                                                                       0) == (0b0001111#7 : (BitVec 7))))) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let mapping78_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__238
                                                                                                                                    11
                                                                                                                                    7)
                                                                                                                                let mapping77_ : (BitVec 5) :=
                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                    v__238
                                                                                                                                    19
                                                                                                                                    15)
                                                                                                                                match ((← (encdec_reg_backwards
                                                                                                                                    mapping77_)), (← (encdec_reg_backwards
                                                                                                                                    mapping78_))) with
                                                                                                                                | (rs, rd) =>
                                                                                                                                  (pure (some
                                                                                                                                      true)))
                                                                                                                            else
                                                                                                                              (pure none))) with
                                                                                                                      | .some result =>
                                                                                                                        (pure result)
                                                                                                                      | none =>
                                                                                                                        (do
                                                                                                                          match (← do
                                                                                                                            let v__201 :=
                                                                                                                              head_exp_
                                                                                                                            if ((v__201 == (0x00000073#32 : (BitVec 32))) : Bool)
                                                                                                                            then
                                                                                                                              (pure (some
                                                                                                                                  true))
                                                                                                                            else
                                                                                                                              (do
                                                                                                                                if ((v__201 == (0x30200073#32 : (BitVec 32))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (do
                                                                                                                                    if ((v__201 == (0x10200073#32 : (BitVec 32))) : Bool)
                                                                                                                                    then
                                                                                                                                      (pure (some
                                                                                                                                          true))
                                                                                                                                    else
                                                                                                                                      (do
                                                                                                                                        if ((v__201 == (0x00100073#32 : (BitVec 32))) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (do
                                                                                                                                            if ((v__201 == (0x10500073#32 : (BitVec 32))) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (do
                                                                                                                                                if (((let mapping80_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__201
                                                                                                                                                         19
                                                                                                                                                         15)
                                                                                                                                                     let mapping79_ : (BitVec 5) :=
                                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                                         v__201
                                                                                                                                                         24
                                                                                                                                                         20)
                                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                                         mapping79_) && (encdec_reg_backwards_matches
                                                                                                                                                         mapping80_))) && (((Sail.BitVec.extractLsb
                                                                                                                                                           v__201
                                                                                                                                                           31
                                                                                                                                                           25) == (0b0001001#7 : (BitVec 7))) && ((Sail.BitVec.extractLsb
                                                                                                                                                           v__201
                                                                                                                                                           14
                                                                                                                                                           0) == (0b000000001110011#15 : (BitVec 15))))) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let mapping80_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__201
                                                                                                                                                        19
                                                                                                                                                        15)
                                                                                                                                                    let mapping79_ : (BitVec 5) :=
                                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                                        v__201
                                                                                                                                                        24
                                                                                                                                                        20)
                                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                                        mapping79_)), (← (encdec_reg_backwards
                                                                                                                                                        mapping80_))) with
                                                                                                                                                    | (rs2, rs1) =>
                                                                                                                                                      (do
                                                                                                                                                        if (((← (virtual_memory_supported
                                                                                                                                                                 ())) || (not
                                                                                                                                                               (true : Bool))) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (pure (some
                                                                                                                                                              true))
                                                                                                                                                        else
                                                                                                                                                          (pure none)))
                                                                                                                                                else
                                                                                                                                                  (pure none))))))) with
                                                                                                                          | .some result =>
                                                                                                                            (pure result)
                                                                                                                          | none =>
                                                                                                                            (do
                                                                                                                              match (← do
                                                                                                                                let v__198 :=
                                                                                                                                  head_exp_
                                                                                                                                if (((let mapping83_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__198
                                                                                                                                         11
                                                                                                                                         7)
                                                                                                                                     let mapping82_ : (BitVec 2) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__198
                                                                                                                                         13
                                                                                                                                         12)
                                                                                                                                     let mapping81_ : (BitVec 5) :=
                                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                                         v__198
                                                                                                                                         19
                                                                                                                                         15)
                                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                                         mapping81_) && ((encdec_csrop_backwards_matches
                                                                                                                                           mapping82_) && (encdec_reg_backwards_matches
                                                                                                                                           mapping83_)))) && (((Sail.BitVec.extractLsb
                                                                                                                                           v__198
                                                                                                                                           14
                                                                                                                                           14) == (0#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                           v__198
                                                                                                                                           6
                                                                                                                                           0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let mapping83_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__198
                                                                                                                                        11
                                                                                                                                        7)
                                                                                                                                    let mapping82_ : (BitVec 2) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__198
                                                                                                                                        13
                                                                                                                                        12)
                                                                                                                                    let mapping81_ : (BitVec 5) :=
                                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                                        v__198
                                                                                                                                        19
                                                                                                                                        15)
                                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                                        mapping81_)), (← (encdec_csrop_backwards
                                                                                                                                        mapping82_)), (← (encdec_reg_backwards
                                                                                                                                        mapping83_))) with
                                                                                                                                    | (rs1, op, rd) =>
                                                                                                                                      (do
                                                                                                                                        if ((← (currentlyEnabled
                                                                                                                                               Ext_Zicsr)) : Bool)
                                                                                                                                        then
                                                                                                                                          (pure (some
                                                                                                                                              true))
                                                                                                                                        else
                                                                                                                                          (pure none)))
                                                                                                                                else
                                                                                                                                  (pure none)) with
                                                                                                                              | .some result =>
                                                                                                                                (pure result)
                                                                                                                              | none =>
                                                                                                                                (do
                                                                                                                                  match (← do
                                                                                                                                    let v__195 :=
                                                                                                                                      head_exp_
                                                                                                                                    if (((let mapping85_ : (BitVec 5) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__195
                                                                                                                                             11
                                                                                                                                             7)
                                                                                                                                         let mapping84_ : (BitVec 2) :=
                                                                                                                                           (Sail.BitVec.extractLsb
                                                                                                                                             v__195
                                                                                                                                             13
                                                                                                                                             12)
                                                                                                                                         ((encdec_csrop_backwards_matches
                                                                                                                                             mapping84_) && (encdec_reg_backwards_matches
                                                                                                                                             mapping85_))) && (((Sail.BitVec.extractLsb
                                                                                                                                               v__195
                                                                                                                                               14
                                                                                                                                               14) == (1#1 : (BitVec 1))) && ((Sail.BitVec.extractLsb
                                                                                                                                               v__195
                                                                                                                                               6
                                                                                                                                               0) == (0b1110011#7 : (BitVec 7))))) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let mapping85_ : (BitVec 5) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__195
                                                                                                                                            11
                                                                                                                                            7)
                                                                                                                                        let mapping84_ : (BitVec 2) :=
                                                                                                                                          (Sail.BitVec.extractLsb
                                                                                                                                            v__195
                                                                                                                                            13
                                                                                                                                            12)
                                                                                                                                        match ((← (encdec_csrop_backwards
                                                                                                                                            mapping84_)), (← (encdec_reg_backwards
                                                                                                                                            mapping85_))) with
                                                                                                                                        | (op, rd) =>
                                                                                                                                          (do
                                                                                                                                            if ((← (currentlyEnabled
                                                                                                                                                   Ext_Zicsr)) : Bool)
                                                                                                                                            then
                                                                                                                                              (pure (some
                                                                                                                                                  true))
                                                                                                                                            else
                                                                                                                                              (pure none)))
                                                                                                                                    else
                                                                                                                                      (pure none)) with
                                                                                                                                  | .some result =>
                                                                                                                                    (pure result)
                                                                                                                                  | none =>
                                                                                                                                    (do
                                                                                                                                      match (← do
                                                                                                                                        let v__191 :=
                                                                                                                                          head_exp_
                                                                                                                                        if (((let mapping86_ : (BitVec 12) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__191
                                                                                                                                                 31
                                                                                                                                                 20)
                                                                                                                                             let mapping87_ : (BitVec 5) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__191
                                                                                                                                                 19
                                                                                                                                                 15)
                                                                                                                                             let mapping86_ : (BitVec 12) :=
                                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                                 v__191
                                                                                                                                                 31
                                                                                                                                                 20)
                                                                                                                                             ((encdec_cbop_backwards_matches
                                                                                                                                                 mapping86_) && (encdec_reg_backwards_matches
                                                                                                                                                 mapping87_))) && ((Sail.BitVec.extractLsb
                                                                                                                                                 v__191
                                                                                                                                                 14
                                                                                                                                                 0) == (0b010000000001111#15 : (BitVec 15)))) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let mapping86_ : (BitVec 12) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__191
                                                                                                                                                31
                                                                                                                                                20)
                                                                                                                                            let mapping87_ : (BitVec 5) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__191
                                                                                                                                                19
                                                                                                                                                15)
                                                                                                                                            let mapping86_ : (BitVec 12) :=
                                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                                v__191
                                                                                                                                                31
                                                                                                                                                20)
                                                                                                                                            match ((← (encdec_cbop_backwards
                                                                                                                                                mapping86_)), (← (encdec_reg_backwards
                                                                                                                                                mapping87_))) with
                                                                                                                                            | (cbop, rs1) =>
                                                                                                                                              (do
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_Zicbom)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      true))
                                                                                                                                                else
                                                                                                                                                  (pure none)))
                                                                                                                                        else
                                                                                                                                          (pure none)) with
                                                                                                                                      | .some result =>
                                                                                                                                        (pure result)
                                                                                                                                      | none =>
                                                                                                                                        (do
                                                                                                                                          match (← do
                                                                                                                                            let v__186 :=
                                                                                                                                              head_exp_
                                                                                                                                            if (((let mapping88_ : (BitVec 5) :=
                                                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                                                     v__186
                                                                                                                                                     19
                                                                                                                                                     15)
                                                                                                                                                 (encdec_reg_backwards_matches
                                                                                                                                                   mapping88_)) && (((Sail.BitVec.extractLsb
                                                                                                                                                       v__186
                                                                                                                                                       31
                                                                                                                                                       20) == (0x004#12 : (BitVec 12))) && ((Sail.BitVec.extractLsb
                                                                                                                                                       v__186
                                                                                                                                                       14
                                                                                                                                                       0) == (0b010000000001111#15 : (BitVec 15))))) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let mapping88_ : (BitVec 5) :=
                                                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                                                    v__186
                                                                                                                                                    19
                                                                                                                                                    15)
                                                                                                                                                let rs1 ← do
                                                                                                                                                  (encdec_reg_backwards
                                                                                                                                                    mapping88_)
                                                                                                                                                if ((← (currentlyEnabled
                                                                                                                                                       Ext_Zicboz)) : Bool)
                                                                                                                                                then
                                                                                                                                                  (pure (some
                                                                                                                                                      true))
                                                                                                                                                else
                                                                                                                                                  (pure none))
                                                                                                                                            else
                                                                                                                                              (pure none)) with
                                                                                                                                          | .some result =>
                                                                                                                                            (pure result)
                                                                                                                                          | none =>
                                                                                                                                            (match head_exp_ with
                                                                                                                                            | s =>
                                                                                                                                              (pure true))))))))))))))))))))))))))))))))))))

def encdec_compressed_forwards (arg_ : instruction) : SailM (BitVec 16) := do
  match arg_ with
  | .C_NOP imm =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b000#3 +++ ((Sail.BitVec.extractLsb imm 5 5) +++ (0b00000#5 +++ ((Sail.BitVec.extractLsb
                    imm 4 0) +++ 0b01#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI4SPN (rd, nzimm) =>
    (do
      if (((nzimm != 0b00000000#8) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b000#3 +++ ((Sail.BitVec.extractLsb nzimm 3 2) +++ ((Sail.BitVec.extractLsb nzimm 7
                  4) +++ ((Sail.BitVec.extractLsb nzimm 0 0) +++ ((Sail.BitVec.extractLsb nzimm 1 1) +++ ((encdec_creg_forwards
                        rd) +++ 0b00#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LW (uimm, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b010#3 +++ ((Sail.BitVec.extractLsb uimm 3 1) +++ ((encdec_creg_forwards rs1) +++ ((Sail.BitVec.extractLsb
                    uimm 0 0) +++ ((Sail.BitVec.extractLsb uimm 4 4) +++ ((encdec_creg_forwards rd) +++ 0b00#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LD (uimm, rs1, rd) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b011#3 +++ ((Sail.BitVec.extractLsb uimm 2 0) +++ ((encdec_creg_forwards rs1) +++ ((Sail.BitVec.extractLsb
                    uimm 4 3) +++ ((encdec_creg_forwards rd) +++ 0b00#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SW (uimm, rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b110#3 +++ ((Sail.BitVec.extractLsb uimm 3 1) +++ ((encdec_creg_forwards rs1) +++ ((Sail.BitVec.extractLsb
                    uimm 0 0) +++ ((Sail.BitVec.extractLsb uimm 4 4) +++ ((encdec_creg_forwards rs2) +++ 0b00#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SD (uimm, rs1, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b111#3 +++ ((Sail.BitVec.extractLsb uimm 2 0) +++ ((encdec_creg_forwards rs1) +++ ((Sail.BitVec.extractLsb
                    uimm 4 3) +++ ((encdec_creg_forwards rs2) +++ 0b00#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI (imm, rsd) =>
    (do
      if (((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b000#3 +++ ((Sail.BitVec.extractLsb imm 5 5) +++ ((encdec_reg_forwards rsd) +++ ((Sail.BitVec.extractLsb
                    imm 4 0) +++ 0b01#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JAL imm =>
    (do
      if (((xlen == 32) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b001#3 +++ ((Sail.BitVec.extractLsb imm 10 10) +++ ((Sail.BitVec.extractLsb imm 3 3) +++ ((Sail.BitVec.extractLsb
                    imm 8 7) +++ ((Sail.BitVec.extractLsb imm 9 9) +++ ((Sail.BitVec.extractLsb imm
                        5 5) +++ ((Sail.BitVec.extractLsb imm 6 6) +++ ((Sail.BitVec.extractLsb imm
                            2 0) +++ ((Sail.BitVec.extractLsb imm 4 4) +++ 0b01#2))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDIW (imm, rsd) =>
    (do
      if (((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then
        (pure (0b001#3 +++ ((Sail.BitVec.extractLsb imm 5 5) +++ ((encdec_reg_forwards rsd) +++ ((Sail.BitVec.extractLsb
                    imm 4 0) +++ 0b01#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LI (imm, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b010#3 +++ ((Sail.BitVec.extractLsb imm 5 5) +++ ((encdec_reg_forwards rd) +++ ((Sail.BitVec.extractLsb
                    imm 4 0) +++ 0b01#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDI16SP nzimm =>
    (do
      if (((nzimm != 0b000000#6) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b011#3 +++ ((Sail.BitVec.extractLsb nzimm 5 5) +++ (0b00010#5 +++ ((Sail.BitVec.extractLsb
                    nzimm 0 0) +++ ((Sail.BitVec.extractLsb nzimm 2 2) +++ ((Sail.BitVec.extractLsb
                        nzimm 4 3) +++ ((Sail.BitVec.extractLsb nzimm 1 1) +++ 0b01#2))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LUI (imm, rd) =>
    (do
      if (((bne rd sp) && ((imm != 0b000000#6) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then
        (pure (0b011#3 +++ ((Sail.BitVec.extractLsb imm 5 5) +++ ((encdec_reg_forwards rd) +++ ((Sail.BitVec.extractLsb
                    imm 4 0) +++ 0b01#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRLI (shamt, rsd) =>
    (do
      if ((((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 +++ ((Sail.BitVec.extractLsb shamt 5 5) +++ (0b00#2 +++ ((encdec_creg_forwards
                    rsd) +++ ((Sail.BitVec.extractLsb shamt 4 0) +++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SRAI (shamt, rsd) =>
    (do
      if ((((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 +++ ((Sail.BitVec.extractLsb shamt 5 5) +++ (0b01#2 +++ ((encdec_creg_forwards
                    rsd) +++ ((Sail.BitVec.extractLsb shamt 4 0) +++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ANDI (imm, rsd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 +++ ((Sail.BitVec.extractLsb imm 5 5) +++ (0b10#2 +++ ((encdec_creg_forwards
                    rsd) +++ ((Sail.BitVec.extractLsb imm 4 0) +++ 0b01#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SUB (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 +++ (0#1 +++ (0b11#2 +++ ((encdec_creg_forwards rsd) +++ (0b00#2 +++ ((encdec_creg_forwards
                        rs2) +++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_XOR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 +++ (0#1 +++ (0b11#2 +++ ((encdec_creg_forwards rsd) +++ (0b01#2 +++ ((encdec_creg_forwards
                        rs2) +++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_OR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 +++ (0#1 +++ (0b11#2 +++ ((encdec_creg_forwards rsd) +++ (0b10#2 +++ ((encdec_creg_forwards
                        rs2) +++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_AND (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b100#3 +++ (0#1 +++ (0b11#2 +++ ((encdec_creg_forwards rsd) +++ (0b11#2 +++ ((encdec_creg_forwards
                        rs2) +++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SUBW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 +++ (1#1 +++ (0b11#2 +++ ((encdec_creg_forwards rsd) +++ (0b00#2 +++ ((encdec_creg_forwards
                        rs2) +++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADDW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 +++ (1#1 +++ (0b11#2 +++ ((encdec_creg_forwards rsd) +++ (0b01#2 +++ ((encdec_creg_forwards
                        rs2) +++ 0b01#2)))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_J imm =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b101#3 +++ ((Sail.BitVec.extractLsb imm 10 10) +++ ((Sail.BitVec.extractLsb imm 3 3) +++ ((Sail.BitVec.extractLsb
                    imm 8 7) +++ ((Sail.BitVec.extractLsb imm 9 9) +++ ((Sail.BitVec.extractLsb imm
                        5 5) +++ ((Sail.BitVec.extractLsb imm 6 6) +++ ((Sail.BitVec.extractLsb imm
                            2 0) +++ ((Sail.BitVec.extractLsb imm 4 4) +++ 0b01#2))))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_BEQZ (imm, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b110#3 +++ ((Sail.BitVec.extractLsb imm 7 7) +++ ((Sail.BitVec.extractLsb imm 3 2) +++ ((encdec_creg_forwards
                    rs) +++ ((Sail.BitVec.extractLsb imm 6 5) +++ ((Sail.BitVec.extractLsb imm 1 0) +++ ((Sail.BitVec.extractLsb
                          imm 4 4) +++ 0b01#2))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_BNEZ (imm, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b111#3 +++ ((Sail.BitVec.extractLsb imm 7 7) +++ ((Sail.BitVec.extractLsb imm 3 2) +++ ((encdec_creg_forwards
                    rs) +++ ((Sail.BitVec.extractLsb imm 6 5) +++ ((Sail.BitVec.extractLsb imm 1 0) +++ ((Sail.BitVec.extractLsb
                          imm 4 4) +++ 0b01#2))))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SLLI (shamt, rsd) =>
    (do
      if ((((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b000#3 +++ ((Sail.BitVec.extractLsb shamt 5 5) +++ ((encdec_reg_forwards rsd) +++ ((Sail.BitVec.extractLsb
                    shamt 4 0) +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LWSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b010#3 +++ ((Sail.BitVec.extractLsb uimm 3 3) +++ ((encdec_reg_forwards rd) +++ ((Sail.BitVec.extractLsb
                    uimm 2 0) +++ ((Sail.BitVec.extractLsb uimm 5 4) +++ 0b10#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_LDSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then
        (pure (0b011#3 +++ ((Sail.BitVec.extractLsb uimm 2 2) +++ ((encdec_reg_forwards rd) +++ ((Sail.BitVec.extractLsb
                    uimm 1 0) +++ ((Sail.BitVec.extractLsb uimm 5 3) +++ 0b10#2))))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SWSP (uimm, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then
        (pure (0b110#3 +++ ((Sail.BitVec.extractLsb uimm 3 0) +++ ((Sail.BitVec.extractLsb uimm 5 4) +++ ((encdec_reg_forwards
                    rs2) +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_SDSP (uimm, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b111#3 +++ ((Sail.BitVec.extractLsb uimm 2 0) +++ ((Sail.BitVec.extractLsb uimm 5 3) +++ ((encdec_reg_forwards
                    rs2) +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure (0b100#3 +++ (0#1 +++ ((encdec_reg_forwards rs1) +++ (0b00000#5 +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_JALR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure (0b100#3 +++ (1#1 +++ ((encdec_reg_forwards rs1) +++ (0b00000#5 +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_MV (rd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 +++ (0#1 +++ ((encdec_reg_forwards rd) +++ ((encdec_reg_forwards rs2) +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_EBREAK () =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure (0b1001#4 +++ (0b0000000000#10 +++ 0b10#2)))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ADD (rsd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then
        (pure (0b100#3 +++ (1#1 +++ ((encdec_reg_forwards rsd) +++ ((encdec_reg_forwards rs2) +++ 0b10#2)))))
      else
        (do
          assert false "Pattern match failure at unknown location"
          throw Error.Exit))
  | .C_ILLEGAL s => (pure s)
  | _ =>
    (do
      assert false "Pattern match failure at unknown location"
      throw Error.Exit)

def encdec_compressed_backwards (arg_ : (BitVec 16)) : SailM instruction := do
  let head_exp_ := arg_
  match (← do
    let v__479 := head_exp_
    if (((← do
           let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__479 12 12)
           let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__479 6 2)
           let imm := (imm_5_5_ +++ imm_4_0_)
           (currentlyEnabled Ext_Zca)) && (((Sail.BitVec.extractLsb v__479 15 13) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                 v__479 11 7) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb v__479 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
    then
      (let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__479 12 12)
      let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__479 6 2)
      (pure (some
          (let imm := (imm_5_5_ +++ imm_4_0_)
          (C_NOP imm)))))
    else
      (do
        if (((let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__479 4 2)
             (encdec_creg_backwards_matches mapping0_)) && (((Sail.BitVec.extractLsb v__479 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                   v__479 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let nzimm_7_4_ : (BitVec 4) := (Sail.BitVec.extractLsb v__479 10 7)
            let nzimm_3_2_ : (BitVec 2) := (Sail.BitVec.extractLsb v__479 12 11)
            let nzimm_1_1_ : (BitVec 1) := (Sail.BitVec.extractLsb v__479 5 5)
            let nzimm_0_0_ : (BitVec 1) := (Sail.BitVec.extractLsb v__479 6 6)
            let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__479 4 2)
            let rd := (encdec_creg_backwards mapping0_)
            if ((← do
                 let nzimm := (((nzimm_7_4_ +++ nzimm_3_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                 (pure ((nzimm != 0b00000000#8) && (← (currentlyEnabled Ext_Zca))))) : Bool)
            then
              (pure (some
                  (let nzimm := (((nzimm_7_4_ +++ nzimm_3_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                  (C_ADDI4SPN (rd, nzimm)))))
            else (pure none))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__476 := head_exp_
        if (((let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__476 4 2)
             let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__476 9 7)
             ((encdec_creg_backwards_matches mapping1_) && (encdec_creg_backwards_matches mapping2_))) && (((Sail.BitVec.extractLsb
                   v__476 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__476 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let uimm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__476 5 5)
            let uimm_3_1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__476 12 10)
            let uimm_0_0_ : (BitVec 1) := (Sail.BitVec.extractLsb v__476 6 6)
            let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__476 4 2)
            let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__476 9 7)
            match ((encdec_creg_backwards mapping1_), (encdec_creg_backwards mapping2_)) with
            | (rs1, rd) =>
              (do
                if ((← do
                     let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                     (currentlyEnabled Ext_Zca)) : Bool)
                then
                  (pure (some
                      (let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                      (C_LW (uimm, rs1, rd)))))
                else (pure none)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__473 := head_exp_
            if (((let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__473 4 2)
                 let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__473 9 7)
                 ((encdec_creg_backwards_matches mapping3_) && (encdec_creg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__473 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__473 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
            then
              (do
                let uimm_4_3_ : (BitVec 2) := (Sail.BitVec.extractLsb v__473 6 5)
                let uimm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__473 12 10)
                let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__473 4 2)
                let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__473 9 7)
                match ((encdec_creg_backwards mapping3_), (encdec_creg_backwards mapping4_)) with
                | (rs1, rd) =>
                  (do
                    if ((← do
                         let uimm := (uimm_4_3_ +++ uimm_2_0_)
                         (pure ((xlen == 64) && (← (currentlyEnabled Ext_Zca))))) : Bool)
                    then
                      (pure (some
                          (let uimm := (uimm_4_3_ +++ uimm_2_0_)
                          (C_LD (uimm, rs1, rd)))))
                    else (pure none)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__470 := head_exp_
                if (((let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__470 4 2)
                     let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__470 9 7)
                     ((encdec_creg_backwards_matches mapping5_) && (encdec_creg_backwards_matches
                         mapping6_))) && (((Sail.BitVec.extractLsb v__470 15 13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                           v__470 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                then
                  (do
                    let uimm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__470 5 5)
                    let uimm_3_1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__470 12 10)
                    let uimm_0_0_ : (BitVec 1) := (Sail.BitVec.extractLsb v__470 6 6)
                    let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__470 4 2)
                    let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__470 9 7)
                    match ((encdec_creg_backwards mapping5_), (encdec_creg_backwards mapping6_)) with
                    | (rs1, rs2) =>
                      (do
                        if ((← do
                             let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                             (currentlyEnabled Ext_Zca)) : Bool)
                        then
                          (pure (some
                              (let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                              (C_SW (uimm, rs1, rs2)))))
                        else (pure none)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__467 := head_exp_
                    if (((let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__467 4 2)
                         let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__467 9 7)
                         ((encdec_creg_backwards_matches mapping7_) && (encdec_creg_backwards_matches
                             mapping8_))) && (((Sail.BitVec.extractLsb v__467 15 13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                               v__467 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                    then
                      (do
                        let uimm_4_3_ : (BitVec 2) := (Sail.BitVec.extractLsb v__467 6 5)
                        let uimm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__467 12 10)
                        let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__467 4 2)
                        let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__467 9 7)
                        match ((encdec_creg_backwards mapping7_), (encdec_creg_backwards mapping8_)) with
                        | (rs1, rs2) =>
                          (do
                            if ((← do
                                 let uimm := (uimm_4_3_ +++ uimm_2_0_)
                                 (pure ((xlen == 64) && (← (currentlyEnabled Ext_Zca))))) : Bool)
                            then
                              (pure (some
                                  (let uimm := (uimm_4_3_ +++ uimm_2_0_)
                                  (C_SD (uimm, rs1, rs2)))))
                            else (pure none)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__464 := head_exp_
                        if (((let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__464 11 7)
                             (encdec_reg_backwards_matches mapping9_)) && (((Sail.BitVec.extractLsb
                                   v__464 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__464 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                        then
                          (do
                            let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__464 11 7)
                            let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__464 12 12)
                            let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__464 6 2)
                            let rsd ← do (encdec_reg_backwards mapping9_)
                            if ((← do
                                 let imm := (imm_5_5_ +++ imm_4_0_)
                                 (pure ((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))))) : Bool)
                            then
                              (pure (some
                                  (let imm := (imm_5_5_ +++ imm_4_0_)
                                  (C_ADDI (imm, rsd)))))
                            else (pure none))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__458 := head_exp_
                            if (((← do
                                   let imm_9_9_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 8 8)
                                   let imm_8_7_ : (BitVec 2) := (Sail.BitVec.extractLsb v__458 10 9)
                                   let imm_6_6_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 6 6)
                                   let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 7 7)
                                   let imm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 2 2)
                                   let imm_3_3_ : (BitVec 1) :=
                                     (Sail.BitVec.extractLsb v__458 11 11)
                                   let imm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__458 5 3)
                                   let imm_10_10_ : (BitVec 1) :=
                                     (Sail.BitVec.extractLsb v__458 12 12)
                                   let imm :=
                                     (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                   (pure ((xlen == 32) && (← (currentlyEnabled Ext_Zca))))) && (((Sail.BitVec.extractLsb
                                       v__458 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__458 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                            then
                              (let imm_9_9_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 8 8)
                              let imm_8_7_ : (BitVec 2) := (Sail.BitVec.extractLsb v__458 10 9)
                              let imm_6_6_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 6 6)
                              let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 7 7)
                              let imm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 2 2)
                              let imm_3_3_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 11 11)
                              let imm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__458 5 3)
                              let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__458 12 12)
                              (pure (some
                                  (let imm :=
                                    (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                  (C_JAL imm)))))
                            else
                              (do
                                if (((let mapping10_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__458 11 7)
                                     (encdec_reg_backwards_matches mapping10_)) && (((Sail.BitVec.extractLsb
                                           v__458 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__458 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping10_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__458 11 7)
                                    let imm_5_5_ : (BitVec 1) :=
                                      (Sail.BitVec.extractLsb v__458 12 12)
                                    let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__458 6 2)
                                    let rsd ← do (encdec_reg_backwards mapping10_)
                                    if ((← do
                                         let imm := (imm_5_5_ +++ imm_4_0_)
                                         (pure ((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled
                                                   Ext_Zca)))))) : Bool)
                                    then
                                      (pure (some
                                          (let imm := (imm_5_5_ +++ imm_4_0_)
                                          (C_ADDIW (imm, rsd)))))
                                    else (pure none))
                                else (pure none))) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__455 := head_exp_
                                if (((let mapping11_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__455 11 7)
                                     (encdec_reg_backwards_matches mapping11_)) && (((Sail.BitVec.extractLsb
                                           v__455 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__455 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping11_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__455 11 7)
                                    let imm_5_5_ : (BitVec 1) :=
                                      (Sail.BitVec.extractLsb v__455 12 12)
                                    let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__455 6 2)
                                    let rd ← do (encdec_reg_backwards mapping11_)
                                    if ((← do
                                         let imm := (imm_5_5_ +++ imm_4_0_)
                                         (currentlyEnabled Ext_Zca)) : Bool)
                                    then
                                      (pure (some
                                          (let imm := (imm_5_5_ +++ imm_4_0_)
                                          (C_LI (imm, rd)))))
                                    else (pure none))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__448 := head_exp_
                                    if (((← do
                                           let nzimm_5_5_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__448 12 12)
                                           let nzimm_4_3_ : (BitVec 2) :=
                                             (Sail.BitVec.extractLsb v__448 4 3)
                                           let nzimm_2_2_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__448 5 5)
                                           let nzimm_1_1_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__448 2 2)
                                           let nzimm_0_0_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__448 6 6)
                                           let nzimm :=
                                             ((((nzimm_5_5_ +++ nzimm_4_3_) +++ nzimm_2_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                                           (pure ((nzimm != 0b000000#6) && (← (currentlyEnabled
                                                   Ext_Zca))))) && (((Sail.BitVec.extractLsb v__448
                                               15 13) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                 v__448 11 7) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb
                                                 v__448 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                    then
                                      (let nzimm_5_5_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__448 12 12)
                                      let nzimm_4_3_ : (BitVec 2) :=
                                        (Sail.BitVec.extractLsb v__448 4 3)
                                      let nzimm_2_2_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__448 5 5)
                                      let nzimm_1_1_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__448 2 2)
                                      let nzimm_0_0_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__448 6 6)
                                      (pure (some
                                          (let nzimm :=
                                            ((((nzimm_5_5_ +++ nzimm_4_3_) +++ nzimm_2_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                                          (C_ADDI16SP nzimm)))))
                                    else
                                      (do
                                        if (((let mapping12_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__448 11 7)
                                             (encdec_reg_backwards_matches mapping12_)) && (((Sail.BitVec.extractLsb
                                                   v__448 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__448 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                        then
                                          (do
                                            let mapping12_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__448 11 7)
                                            let imm_5_5_ : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__448 12 12)
                                            let imm_4_0_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__448 6 2)
                                            let rd ← do (encdec_reg_backwards mapping12_)
                                            if ((← do
                                                 let imm := (imm_5_5_ +++ imm_4_0_)
                                                 (pure ((bne rd sp) && ((imm != 0b000000#6) && (← (currentlyEnabled
                                                           Ext_Zca)))))) : Bool)
                                            then
                                              (pure (some
                                                  (let imm := (imm_5_5_ +++ imm_4_0_)
                                                  (C_LUI (imm, rd)))))
                                            else (pure none))
                                        else (pure none))) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__444 := head_exp_
                                        if (((let mapping13_ : (BitVec 3) :=
                                               (Sail.BitVec.extractLsb v__444 9 7)
                                             (encdec_creg_backwards_matches mapping13_)) && (((Sail.BitVec.extractLsb
                                                   v__444 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                     v__444 11 10) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                     v__444 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                        then
                                          (do
                                            let shamt_5_5_ : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__444 12 12)
                                            let shamt_4_0_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__444 6 2)
                                            let mapping13_ : (BitVec 3) :=
                                              (Sail.BitVec.extractLsb v__444 9 7)
                                            let rsd := (encdec_creg_backwards mapping13_)
                                            if ((← do
                                                 let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                 (pure (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled
                                                         Ext_Zca))))) : Bool)
                                            then
                                              (pure (some
                                                  (let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                  (C_SRLI (shamt, rsd)))))
                                            else (pure none))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__440 := head_exp_
                                            if (((let mapping14_ : (BitVec 3) :=
                                                   (Sail.BitVec.extractLsb v__440 9 7)
                                                 (encdec_creg_backwards_matches mapping14_)) && (((Sail.BitVec.extractLsb
                                                       v__440 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                         v__440 11 10) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                         v__440 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                            then
                                              (do
                                                let shamt_5_5_ : (BitVec 1) :=
                                                  (Sail.BitVec.extractLsb v__440 12 12)
                                                let shamt_4_0_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__440 6 2)
                                                let mapping14_ : (BitVec 3) :=
                                                  (Sail.BitVec.extractLsb v__440 9 7)
                                                let rsd := (encdec_creg_backwards mapping14_)
                                                if ((← do
                                                     let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                     (pure (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled
                                                             Ext_Zca))))) : Bool)
                                                then
                                                  (pure (some
                                                      (let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                      (C_SRAI (shamt, rsd)))))
                                                else (pure none))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__436 := head_exp_
                                                if (((let mapping15_ : (BitVec 3) :=
                                                       (Sail.BitVec.extractLsb v__436 9 7)
                                                     (encdec_creg_backwards_matches mapping15_)) && (((Sail.BitVec.extractLsb
                                                           v__436 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                             v__436 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                             v__436 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping15_ : (BitVec 3) :=
                                                      (Sail.BitVec.extractLsb v__436 9 7)
                                                    let imm_5_5_ : (BitVec 1) :=
                                                      (Sail.BitVec.extractLsb v__436 12 12)
                                                    let imm_4_0_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__436 6 2)
                                                    let rsd := (encdec_creg_backwards mapping15_)
                                                    if ((← do
                                                         let imm := (imm_5_5_ +++ imm_4_0_)
                                                         (currentlyEnabled Ext_Zca)) : Bool)
                                                    then
                                                      (pure (some
                                                          (let imm := (imm_5_5_ +++ imm_4_0_)
                                                          (C_ANDI (imm, rsd)))))
                                                    else (pure none))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__430 := head_exp_
                                                    if (((let mapping17_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__430 4 2)
                                                         let mapping16_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__430 9 7)
                                                         ((encdec_creg_backwards_matches mapping16_) && (encdec_creg_backwards_matches
                                                             mapping17_))) && (((Sail.BitVec.extractLsb
                                                               v__430 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                 v__430 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                 v__430 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping17_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__430 4 2)
                                                        let mapping16_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__430 9 7)
                                                        match ((encdec_creg_backwards mapping16_), (encdec_creg_backwards
                                                          mapping17_)) with
                                                        | (rsd, rs2) =>
                                                          (do
                                                            if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                            then (pure (some (C_SUB (rsd, rs2))))
                                                            else (pure none)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__424 := head_exp_
                                                        if (((let mapping19_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__424 4 2)
                                                             let mapping18_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__424 9 7)
                                                             ((encdec_creg_backwards_matches
                                                                 mapping18_) && (encdec_creg_backwards_matches
                                                                 mapping19_))) && (((Sail.BitVec.extractLsb
                                                                   v__424 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                     v__424 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                     v__424 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping19_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__424 4 2)
                                                            let mapping18_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__424 9 7)
                                                            match ((encdec_creg_backwards mapping18_), (encdec_creg_backwards
                                                              mapping19_)) with
                                                            | (rsd, rs2) =>
                                                              (do
                                                                if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                                then
                                                                  (pure (some (C_XOR (rsd, rs2))))
                                                                else (pure none)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__418 := head_exp_
                                                            if (((let mapping21_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__418 4
                                                                     2)
                                                                 let mapping20_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__418 9
                                                                     7)
                                                                 ((encdec_creg_backwards_matches
                                                                     mapping20_) && (encdec_creg_backwards_matches
                                                                     mapping21_))) && (((Sail.BitVec.extractLsb
                                                                       v__418 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                         v__418 6 5) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                         v__418 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping21_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__418 4 2)
                                                                let mapping20_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__418 9 7)
                                                                match ((encdec_creg_backwards
                                                                  mapping20_), (encdec_creg_backwards
                                                                  mapping21_)) with
                                                                | (rsd, rs2) =>
                                                                  (do
                                                                    if ((← (currentlyEnabled
                                                                           Ext_Zca)) : Bool)
                                                                    then
                                                                      (pure (some (C_OR (rsd, rs2))))
                                                                    else (pure none)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__412 := head_exp_
                                                                if (((let mapping23_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__412 4 2)
                                                                     let mapping22_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__412 9 7)
                                                                     ((encdec_creg_backwards_matches
                                                                         mapping22_) && (encdec_creg_backwards_matches
                                                                         mapping23_))) && (((Sail.BitVec.extractLsb
                                                                           v__412 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                             v__412 6 5) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                             v__412 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping23_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__412
                                                                        4 2)
                                                                    let mapping22_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__412
                                                                        9 7)
                                                                    match ((encdec_creg_backwards
                                                                      mapping22_), (encdec_creg_backwards
                                                                      mapping23_)) with
                                                                    | (rsd, rs2) =>
                                                                      (do
                                                                        if ((← (currentlyEnabled
                                                                               Ext_Zca)) : Bool)
                                                                        then
                                                                          (pure (some
                                                                              (C_AND (rsd, rs2))))
                                                                        else (pure none)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__406 := head_exp_
                                                                    if (((let mapping25_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__406 4 2)
                                                                         let mapping24_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__406 9 7)
                                                                         ((encdec_creg_backwards_matches
                                                                             mapping24_) && (encdec_creg_backwards_matches
                                                                             mapping25_))) && (((Sail.BitVec.extractLsb
                                                                               v__406 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                 v__406 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                 v__406 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping25_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__406 4 2)
                                                                        let mapping24_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__406 9 7)
                                                                        match ((encdec_creg_backwards
                                                                          mapping24_), (encdec_creg_backwards
                                                                          mapping25_)) with
                                                                        | (rsd, rs2) =>
                                                                          (do
                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                     Ext_Zca))) : Bool)
                                                                            then
                                                                              (pure (some
                                                                                  (C_SUBW (rsd, rs2))))
                                                                            else (pure none)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__400 := head_exp_
                                                                        if (((let mapping27_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__400 4 2)
                                                                             let mapping26_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__400 9 7)
                                                                             ((encdec_creg_backwards_matches
                                                                                 mapping26_) && (encdec_creg_backwards_matches
                                                                                 mapping27_))) && (((Sail.BitVec.extractLsb
                                                                                   v__400 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                     v__400 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                     v__400 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping27_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__400 4 2)
                                                                            let mapping26_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__400 9 7)
                                                                            match ((encdec_creg_backwards
                                                                              mapping26_), (encdec_creg_backwards
                                                                              mapping27_)) with
                                                                            | (rsd, rs2) =>
                                                                              (do
                                                                                if (((xlen == 64) && (← (currentlyEnabled
                                                                                         Ext_Zca))) : Bool)
                                                                                then
                                                                                  (pure (some
                                                                                      (C_ADDW
                                                                                        (rsd, rs2))))
                                                                                else (pure none)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__394 := head_exp_
                                                                            if (((← do
                                                                                   let imm_9_9_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 8 8)
                                                                                   let imm_8_7_ : (BitVec 2) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 10 9)
                                                                                   let imm_6_6_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 6 6)
                                                                                   let imm_5_5_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 7 7)
                                                                                   let imm_4_4_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 2 2)
                                                                                   let imm_3_3_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 11 11)
                                                                                   let imm_2_0_ : (BitVec 3) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 5 3)
                                                                                   let imm_10_10_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__394 12 12)
                                                                                   let imm :=
                                                                                     (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                                                                   (currentlyEnabled
                                                                                     Ext_Zca)) && (((Sail.BitVec.extractLsb
                                                                                       v__394 15 13) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                       v__394 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                            then
                                                                              (let imm_9_9_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 8 8)
                                                                              let imm_8_7_ : (BitVec 2) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 10 9)
                                                                              let imm_6_6_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 6 6)
                                                                              let imm_5_5_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 7 7)
                                                                              let imm_4_4_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 2 2)
                                                                              let imm_3_3_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 11 11)
                                                                              let imm_2_0_ : (BitVec 3) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 5 3)
                                                                              let imm_10_10_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__394 12 12)
                                                                              (pure (some
                                                                                  (let imm :=
                                                                                    (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                                                                  (C_J imm)))))
                                                                            else
                                                                              (do
                                                                                if (((let mapping28_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__394 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping28_)) && (((Sail.BitVec.extractLsb
                                                                                           v__394 15
                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__394 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping28_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__394 9 7)
                                                                                    let imm_7_7_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__394 12 12)
                                                                                    let imm_6_5_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__394 6 5)
                                                                                    let imm_4_4_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__394 2 2)
                                                                                    let imm_3_2_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__394 11 10)
                                                                                    let imm_1_0_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__394 4 3)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping28_)
                                                                                    if ((← do
                                                                                         let imm :=
                                                                                           ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                         (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          (let imm :=
                                                                                            ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                          (C_BEQZ
                                                                                            (imm, rs)))))
                                                                                    else (pure none))
                                                                                else (pure none))) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__391 :=
                                                                                  head_exp_
                                                                                if (((let mapping29_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__391 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping29_)) && (((Sail.BitVec.extractLsb
                                                                                           v__391 15
                                                                                           13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__391 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping29_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__391 9 7)
                                                                                    let imm_7_7_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__391 12 12)
                                                                                    let imm_6_5_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__391 6 5)
                                                                                    let imm_4_4_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__391 2 2)
                                                                                    let imm_3_2_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__391 11 10)
                                                                                    let imm_1_0_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__391 4 3)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping29_)
                                                                                    if ((← do
                                                                                         let imm :=
                                                                                           ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                         (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          (let imm :=
                                                                                            ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                          (C_BNEZ
                                                                                            (imm, rs)))))
                                                                                    else (pure none))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__388 :=
                                                                                      head_exp_
                                                                                    if (((let mapping30_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__388
                                                                                             11 7)
                                                                                         (encdec_reg_backwards_matches
                                                                                           mapping30_)) && (((Sail.BitVec.extractLsb
                                                                                               v__388
                                                                                               15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__388
                                                                                               1 0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let shamt_5_5_ : (BitVec 1) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__388
                                                                                            12 12)
                                                                                        let shamt_4_0_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__388 6
                                                                                            2)
                                                                                        let mapping30_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__388
                                                                                            11 7)
                                                                                        let rsd ← do
                                                                                          (encdec_reg_backwards
                                                                                            mapping30_)
                                                                                        if ((← do
                                                                                             let shamt :=
                                                                                               (shamt_5_5_ +++ shamt_4_0_)
                                                                                             (pure (((xlen == 64) || ((BitVec.access
                                                                                                       shamt
                                                                                                       5) == 0#1)) && (← (currentlyEnabled
                                                                                                     Ext_Zca))))) : Bool)
                                                                                        then
                                                                                          (pure (some
                                                                                              (let shamt :=
                                                                                                (shamt_5_5_ +++ shamt_4_0_)
                                                                                              (C_SLLI
                                                                                                (shamt, rsd)))))
                                                                                        else
                                                                                          (pure none))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__385 :=
                                                                                          head_exp_
                                                                                        if (((let mapping31_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__385
                                                                                                 11
                                                                                                 7)
                                                                                             (encdec_reg_backwards_matches
                                                                                               mapping31_)) && (((Sail.BitVec.extractLsb
                                                                                                   v__385
                                                                                                   15
                                                                                                   13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                   v__385
                                                                                                   1
                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let uimm_5_4_ : (BitVec 2) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__385
                                                                                                3 2)
                                                                                            let uimm_3_3_ : (BitVec 1) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__385
                                                                                                12
                                                                                                12)
                                                                                            let uimm_2_0_ : (BitVec 3) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__385
                                                                                                6 4)
                                                                                            let mapping31_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__385
                                                                                                11 7)
                                                                                            let rd ← do
                                                                                              (encdec_reg_backwards
                                                                                                mapping31_)
                                                                                            if ((← do
                                                                                                 let uimm :=
                                                                                                   ((uimm_5_4_ +++ uimm_3_3_) +++ uimm_2_0_)
                                                                                                 (pure ((bne
                                                                                                       rd
                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                         Ext_Zca))))) : Bool)
                                                                                            then
                                                                                              (pure (some
                                                                                                  (let uimm :=
                                                                                                    ((uimm_5_4_ +++ uimm_3_3_) +++ uimm_2_0_)
                                                                                                  (C_LWSP
                                                                                                    (uimm, rd)))))
                                                                                            else
                                                                                              (pure none))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__382 :=
                                                                                              head_exp_
                                                                                            if (((let mapping32_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__382
                                                                                                     11
                                                                                                     7)
                                                                                                 (encdec_reg_backwards_matches
                                                                                                   mapping32_)) && (((Sail.BitVec.extractLsb
                                                                                                       v__382
                                                                                                       15
                                                                                                       13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                       v__382
                                                                                                       1
                                                                                                       0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let uimm_5_3_ : (BitVec 3) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__382
                                                                                                    4
                                                                                                    2)
                                                                                                let uimm_2_2_ : (BitVec 1) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__382
                                                                                                    12
                                                                                                    12)
                                                                                                let uimm_1_0_ : (BitVec 2) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__382
                                                                                                    6
                                                                                                    5)
                                                                                                let mapping32_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__382
                                                                                                    11
                                                                                                    7)
                                                                                                let rd ← do
                                                                                                  (encdec_reg_backwards
                                                                                                    mapping32_)
                                                                                                if ((← do
                                                                                                     let uimm :=
                                                                                                       ((uimm_5_3_ +++ uimm_2_2_) +++ uimm_1_0_)
                                                                                                     (pure ((bne
                                                                                                           rd
                                                                                                           zreg) && ((xlen == 64) && (← (currentlyEnabled
                                                                                                               Ext_Zca)))))) : Bool)
                                                                                                then
                                                                                                  (pure (some
                                                                                                      (let uimm :=
                                                                                                        ((uimm_5_3_ +++ uimm_2_2_) +++ uimm_1_0_)
                                                                                                      (C_LDSP
                                                                                                        (uimm, rd)))))
                                                                                                else
                                                                                                  (pure none))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__379 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping33_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__379
                                                                                                         6
                                                                                                         2)
                                                                                                     (encdec_reg_backwards_matches
                                                                                                       mapping33_)) && (((Sail.BitVec.extractLsb
                                                                                                           v__379
                                                                                                           15
                                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                           v__379
                                                                                                           1
                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let uimm_5_4_ : (BitVec 2) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__379
                                                                                                        8
                                                                                                        7)
                                                                                                    let uimm_3_0_ : (BitVec 4) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__379
                                                                                                        12
                                                                                                        9)
                                                                                                    let mapping33_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__379
                                                                                                        6
                                                                                                        2)
                                                                                                    let rs2 ← do
                                                                                                      (encdec_reg_backwards
                                                                                                        mapping33_)
                                                                                                    if ((← do
                                                                                                         let uimm :=
                                                                                                           (uimm_5_4_ +++ uimm_3_0_)
                                                                                                         (currentlyEnabled
                                                                                                           Ext_Zca)) : Bool)
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          (let uimm :=
                                                                                                            (uimm_5_4_ +++ uimm_3_0_)
                                                                                                          (C_SWSP
                                                                                                            (uimm, rs2)))))
                                                                                                    else
                                                                                                      (pure none))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__376 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping34_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__376
                                                                                                             6
                                                                                                             2)
                                                                                                         (encdec_reg_backwards_matches
                                                                                                           mapping34_)) && (((Sail.BitVec.extractLsb
                                                                                                               v__376
                                                                                                               15
                                                                                                               13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                               v__376
                                                                                                               1
                                                                                                               0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let uimm_5_3_ : (BitVec 3) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__376
                                                                                                            9
                                                                                                            7)
                                                                                                        let uimm_2_0_ : (BitVec 3) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__376
                                                                                                            12
                                                                                                            10)
                                                                                                        let mapping34_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__376
                                                                                                            6
                                                                                                            2)
                                                                                                        let rs2 ← do
                                                                                                          (encdec_reg_backwards
                                                                                                            mapping34_)
                                                                                                        if ((← do
                                                                                                             let uimm :=
                                                                                                               (uimm_5_3_ +++ uimm_2_0_)
                                                                                                             (pure ((xlen == 64) && (← (currentlyEnabled
                                                                                                                     Ext_Zca))))) : Bool)
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              (let uimm :=
                                                                                                                (uimm_5_3_ +++ uimm_2_0_)
                                                                                                              (C_SDSP
                                                                                                                (uimm, rs2)))))
                                                                                                        else
                                                                                                          (pure none))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__371 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping35_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__371
                                                                                                                 11
                                                                                                                 7)
                                                                                                             (encdec_reg_backwards_matches
                                                                                                               mapping35_)) && (((Sail.BitVec.extractLsb
                                                                                                                   v__371
                                                                                                                   15
                                                                                                                   12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                   v__371
                                                                                                                   6
                                                                                                                   0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping35_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__371
                                                                                                                11
                                                                                                                7)
                                                                                                            let rs1 ← do
                                                                                                              (encdec_reg_backwards
                                                                                                                mapping35_)
                                                                                                            if (((bne
                                                                                                                   rs1
                                                                                                                   zreg) && (← (currentlyEnabled
                                                                                                                     Ext_Zca))) : Bool)
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  (C_JR
                                                                                                                    rs1)))
                                                                                                            else
                                                                                                              (pure none))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__366 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping36_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__366
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 (encdec_reg_backwards_matches
                                                                                                                   mapping36_)) && (((Sail.BitVec.extractLsb
                                                                                                                       v__366
                                                                                                                       15
                                                                                                                       12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                       v__366
                                                                                                                       6
                                                                                                                       0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping36_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__366
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let rs1 ← do
                                                                                                                  (encdec_reg_backwards
                                                                                                                    mapping36_)
                                                                                                                if (((bne
                                                                                                                       rs1
                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                then
                                                                                                                  (pure (some
                                                                                                                      (C_JALR
                                                                                                                        rs1)))
                                                                                                                else
                                                                                                                  (pure none))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__362 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping38_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__362
                                                                                                                         6
                                                                                                                         2)
                                                                                                                     let mapping37_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__362
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping37_) && (encdec_reg_backwards_matches
                                                                                                                         mapping38_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__362
                                                                                                                           15
                                                                                                                           12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__362
                                                                                                                           1
                                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping38_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__362
                                                                                                                        6
                                                                                                                        2)
                                                                                                                    let mapping37_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__362
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping37_)), (← (encdec_reg_backwards
                                                                                                                        mapping38_))) with
                                                                                                                    | (rd, rs2) =>
                                                                                                                      (do
                                                                                                                        if (((bne
                                                                                                                               rs2
                                                                                                                               zreg) && (← (currentlyEnabled
                                                                                                                                 Ext_Zca))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              (C_MV
                                                                                                                                (rd, rs2))))
                                                                                                                        else
                                                                                                                          (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__354 :=
                                                                                                                      head_exp_
                                                                                                                    if (((← (currentlyEnabled
                                                                                                                             Ext_Zca)) && (v__354 == (0x9002#16 : (BitVec 16)))) : Bool)
                                                                                                                    then
                                                                                                                      (pure (some
                                                                                                                          (C_EBREAK
                                                                                                                            ())))
                                                                                                                    else
                                                                                                                      (do
                                                                                                                        if (((let mapping40_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__354
                                                                                                                                 6
                                                                                                                                 2)
                                                                                                                             let mapping39_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__354
                                                                                                                                 11
                                                                                                                                 7)
                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                 mapping39_) && (encdec_reg_backwards_matches
                                                                                                                                 mapping40_))) && (((Sail.BitVec.extractLsb
                                                                                                                                   v__354
                                                                                                                                   15
                                                                                                                                   12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                                   v__354
                                                                                                                                   1
                                                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let mapping40_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__354
                                                                                                                                6
                                                                                                                                2)
                                                                                                                            let mapping39_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__354
                                                                                                                                11
                                                                                                                                7)
                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                mapping39_)), (← (encdec_reg_backwards
                                                                                                                                mapping40_))) with
                                                                                                                            | (rsd, rs2) =>
                                                                                                                              (do
                                                                                                                                if (((bne
                                                                                                                                       rs2
                                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      (C_ADD
                                                                                                                                        (rsd, rs2))))
                                                                                                                                else
                                                                                                                                  (pure none)))
                                                                                                                        else
                                                                                                                          (pure none))) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (match head_exp_ with
                                                                                                                    | s =>
                                                                                                                      (pure (C_ILLEGAL
                                                                                                                          s)))))))))))))))))))))))))))))))

def encdec_compressed_forwards_matches (arg_ : instruction) : SailM Bool := do
  match arg_ with
  | .C_NOP imm =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDI4SPN (rd, nzimm) =>
    (do
      if (((nzimm != 0b00000000#8) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LW (uimm, rs1, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_LD (uimm, rs1, rd) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SW (uimm, rs1, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SD (uimm, rs1, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDI (imm, rsd) =>
    (do
      if (((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_JAL imm =>
    (do
      if (((xlen == 32) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDIW (imm, rsd) =>
    (do
      if (((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LI (imm, rd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDI16SP nzimm =>
    (do
      if (((nzimm != 0b000000#6) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LUI (imm, rd) =>
    (do
      if (((bne rd sp) && ((imm != 0b000000#6) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SRLI (shamt, rsd) =>
    (do
      if ((((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SRAI (shamt, rsd) =>
    (do
      if ((((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ANDI (imm, rsd) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SUB (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_XOR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_OR (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_AND (rsd, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SUBW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADDW (rsd, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_J imm =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_BEQZ (imm, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_BNEZ (imm, rs) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SLLI (shamt, rsd) =>
    (do
      if ((((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LWSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_LDSP (uimm, rd) =>
    (do
      if (((bne rd zreg) && ((xlen == 64) && (← (currentlyEnabled Ext_Zca)))) : Bool)
      then (pure true)
      else (pure false))
  | .C_SWSP (uimm, rs2) =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_SDSP (uimm, rs2) =>
    (do
      if (((xlen == 64) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_JR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_JALR rs1 =>
    (do
      if (((bne rs1 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_MV (rd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_EBREAK () =>
    (do
      if ((← (currentlyEnabled Ext_Zca)) : Bool)
      then (pure true)
      else (pure false))
  | .C_ADD (rsd, rs2) =>
    (do
      if (((bne rs2 zreg) && (← (currentlyEnabled Ext_Zca))) : Bool)
      then (pure true)
      else (pure false))
  | .C_ILLEGAL s => (pure true)
  | _ => (pure false)

def encdec_compressed_backwards_matches (arg_ : (BitVec 16)) : SailM Bool := do
  let head_exp_ := arg_
  match (← do
    let v__611 := head_exp_
    if (((← do
           let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__611 12 12)
           let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__611 6 2)
           let imm := (imm_5_5_ +++ imm_4_0_)
           (currentlyEnabled Ext_Zca)) && (((Sail.BitVec.extractLsb v__611 15 13) == (0b000#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                 v__611 11 7) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb v__611 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
    then
      (let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__611 12 12)
      let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__611 6 2)
      (pure (some
          (let imm := (imm_5_5_ +++ imm_4_0_)
          true))))
    else
      (do
        if (((let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__611 4 2)
             (encdec_creg_backwards_matches mapping0_)) && (((Sail.BitVec.extractLsb v__611 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                   v__611 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let nzimm_7_4_ : (BitVec 4) := (Sail.BitVec.extractLsb v__611 10 7)
            let nzimm_3_2_ : (BitVec 2) := (Sail.BitVec.extractLsb v__611 12 11)
            let nzimm_1_1_ : (BitVec 1) := (Sail.BitVec.extractLsb v__611 5 5)
            let nzimm_0_0_ : (BitVec 1) := (Sail.BitVec.extractLsb v__611 6 6)
            let mapping0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__611 4 2)
            let rd := (encdec_creg_backwards mapping0_)
            if ((← do
                 let nzimm := (((nzimm_7_4_ +++ nzimm_3_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                 (pure ((nzimm != 0b00000000#8) && (← (currentlyEnabled Ext_Zca))))) : Bool)
            then
              (pure (some
                  (let nzimm := (((nzimm_7_4_ +++ nzimm_3_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                  true)))
            else (pure none))
        else (pure none))) with
  | .some result => (pure result)
  | none =>
    (do
      match (← do
        let v__608 := head_exp_
        if (((let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__608 4 2)
             let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__608 9 7)
             ((encdec_creg_backwards_matches mapping1_) && (encdec_creg_backwards_matches mapping2_))) && (((Sail.BitVec.extractLsb
                   v__608 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb v__608 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
        then
          (do
            let uimm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__608 5 5)
            let uimm_3_1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__608 12 10)
            let uimm_0_0_ : (BitVec 1) := (Sail.BitVec.extractLsb v__608 6 6)
            let mapping2_ : (BitVec 3) := (Sail.BitVec.extractLsb v__608 4 2)
            let mapping1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__608 9 7)
            match ((encdec_creg_backwards mapping1_), (encdec_creg_backwards mapping2_)) with
            | (rs1, rd) =>
              (do
                if ((← do
                     let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                     (currentlyEnabled Ext_Zca)) : Bool)
                then
                  (pure (some
                      (let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                      true)))
                else (pure none)))
        else (pure none)) with
      | .some result => (pure result)
      | none =>
        (do
          match (← do
            let v__605 := head_exp_
            if (((let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__605 4 2)
                 let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__605 9 7)
                 ((encdec_creg_backwards_matches mapping3_) && (encdec_creg_backwards_matches
                     mapping4_))) && (((Sail.BitVec.extractLsb v__605 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                       v__605 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
            then
              (do
                let uimm_4_3_ : (BitVec 2) := (Sail.BitVec.extractLsb v__605 6 5)
                let uimm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__605 12 10)
                let mapping4_ : (BitVec 3) := (Sail.BitVec.extractLsb v__605 4 2)
                let mapping3_ : (BitVec 3) := (Sail.BitVec.extractLsb v__605 9 7)
                match ((encdec_creg_backwards mapping3_), (encdec_creg_backwards mapping4_)) with
                | (rs1, rd) =>
                  (do
                    if ((← do
                         let uimm := (uimm_4_3_ +++ uimm_2_0_)
                         (pure ((xlen == 64) && (← (currentlyEnabled Ext_Zca))))) : Bool)
                    then
                      (pure (some
                          (let uimm := (uimm_4_3_ +++ uimm_2_0_)
                          true)))
                    else (pure none)))
            else (pure none)) with
          | .some result => (pure result)
          | none =>
            (do
              match (← do
                let v__602 := head_exp_
                if (((let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__602 4 2)
                     let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__602 9 7)
                     ((encdec_creg_backwards_matches mapping5_) && (encdec_creg_backwards_matches
                         mapping6_))) && (((Sail.BitVec.extractLsb v__602 15 13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                           v__602 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                then
                  (do
                    let uimm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__602 5 5)
                    let uimm_3_1_ : (BitVec 3) := (Sail.BitVec.extractLsb v__602 12 10)
                    let uimm_0_0_ : (BitVec 1) := (Sail.BitVec.extractLsb v__602 6 6)
                    let mapping6_ : (BitVec 3) := (Sail.BitVec.extractLsb v__602 4 2)
                    let mapping5_ : (BitVec 3) := (Sail.BitVec.extractLsb v__602 9 7)
                    match ((encdec_creg_backwards mapping5_), (encdec_creg_backwards mapping6_)) with
                    | (rs1, rs2) =>
                      (do
                        if ((← do
                             let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                             (currentlyEnabled Ext_Zca)) : Bool)
                        then
                          (pure (some
                              (let uimm := ((uimm_4_4_ +++ uimm_3_1_) +++ uimm_0_0_)
                              true)))
                        else (pure none)))
                else (pure none)) with
              | .some result => (pure result)
              | none =>
                (do
                  match (← do
                    let v__599 := head_exp_
                    if (((let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__599 4 2)
                         let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__599 9 7)
                         ((encdec_creg_backwards_matches mapping7_) && (encdec_creg_backwards_matches
                             mapping8_))) && (((Sail.BitVec.extractLsb v__599 15 13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                               v__599 1 0) == (0b00#2 : (BitVec 2))))) : Bool)
                    then
                      (do
                        let uimm_4_3_ : (BitVec 2) := (Sail.BitVec.extractLsb v__599 6 5)
                        let uimm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__599 12 10)
                        let mapping8_ : (BitVec 3) := (Sail.BitVec.extractLsb v__599 4 2)
                        let mapping7_ : (BitVec 3) := (Sail.BitVec.extractLsb v__599 9 7)
                        match ((encdec_creg_backwards mapping7_), (encdec_creg_backwards mapping8_)) with
                        | (rs1, rs2) =>
                          (do
                            if ((← do
                                 let uimm := (uimm_4_3_ +++ uimm_2_0_)
                                 (pure ((xlen == 64) && (← (currentlyEnabled Ext_Zca))))) : Bool)
                            then
                              (pure (some
                                  (let uimm := (uimm_4_3_ +++ uimm_2_0_)
                                  true)))
                            else (pure none)))
                    else (pure none)) with
                  | .some result => (pure result)
                  | none =>
                    (do
                      match (← do
                        let v__596 := head_exp_
                        if (((let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__596 11 7)
                             (encdec_reg_backwards_matches mapping9_)) && (((Sail.BitVec.extractLsb
                                   v__596 15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                   v__596 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                        then
                          (do
                            let mapping9_ : (BitVec 5) := (Sail.BitVec.extractLsb v__596 11 7)
                            let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__596 12 12)
                            let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__596 6 2)
                            let rsd ← do (encdec_reg_backwards mapping9_)
                            if ((← do
                                 let imm := (imm_5_5_ +++ imm_4_0_)
                                 (pure ((bne rsd zreg) && (← (currentlyEnabled Ext_Zca))))) : Bool)
                            then
                              (pure (some
                                  (let imm := (imm_5_5_ +++ imm_4_0_)
                                  true)))
                            else (pure none))
                        else (pure none)) with
                      | .some result => (pure result)
                      | none =>
                        (do
                          match (← do
                            let v__590 := head_exp_
                            if (((← do
                                   let imm_9_9_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 8 8)
                                   let imm_8_7_ : (BitVec 2) := (Sail.BitVec.extractLsb v__590 10 9)
                                   let imm_6_6_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 6 6)
                                   let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 7 7)
                                   let imm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 2 2)
                                   let imm_3_3_ : (BitVec 1) :=
                                     (Sail.BitVec.extractLsb v__590 11 11)
                                   let imm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__590 5 3)
                                   let imm_10_10_ : (BitVec 1) :=
                                     (Sail.BitVec.extractLsb v__590 12 12)
                                   let imm :=
                                     (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                   (pure ((xlen == 32) && (← (currentlyEnabled Ext_Zca))))) && (((Sail.BitVec.extractLsb
                                       v__590 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                       v__590 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                            then
                              (let imm_9_9_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 8 8)
                              let imm_8_7_ : (BitVec 2) := (Sail.BitVec.extractLsb v__590 10 9)
                              let imm_6_6_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 6 6)
                              let imm_5_5_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 7 7)
                              let imm_4_4_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 2 2)
                              let imm_3_3_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 11 11)
                              let imm_2_0_ : (BitVec 3) := (Sail.BitVec.extractLsb v__590 5 3)
                              let imm_10_10_ : (BitVec 1) := (Sail.BitVec.extractLsb v__590 12 12)
                              (pure (some
                                  (let imm :=
                                    (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                  true))))
                            else
                              (do
                                if (((let mapping10_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__590 11 7)
                                     (encdec_reg_backwards_matches mapping10_)) && (((Sail.BitVec.extractLsb
                                           v__590 15 13) == (0b001#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__590 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping10_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__590 11 7)
                                    let imm_5_5_ : (BitVec 1) :=
                                      (Sail.BitVec.extractLsb v__590 12 12)
                                    let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__590 6 2)
                                    let rsd ← do (encdec_reg_backwards mapping10_)
                                    if ((← do
                                         let imm := (imm_5_5_ +++ imm_4_0_)
                                         (pure ((bne rsd zreg) && ((xlen == 64) && (← (currentlyEnabled
                                                   Ext_Zca)))))) : Bool)
                                    then
                                      (pure (some
                                          (let imm := (imm_5_5_ +++ imm_4_0_)
                                          true)))
                                    else (pure none))
                                else (pure none))) with
                          | .some result => (pure result)
                          | none =>
                            (do
                              match (← do
                                let v__587 := head_exp_
                                if (((let mapping11_ : (BitVec 5) :=
                                       (Sail.BitVec.extractLsb v__587 11 7)
                                     (encdec_reg_backwards_matches mapping11_)) && (((Sail.BitVec.extractLsb
                                           v__587 15 13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                           v__587 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                then
                                  (do
                                    let mapping11_ : (BitVec 5) :=
                                      (Sail.BitVec.extractLsb v__587 11 7)
                                    let imm_5_5_ : (BitVec 1) :=
                                      (Sail.BitVec.extractLsb v__587 12 12)
                                    let imm_4_0_ : (BitVec 5) := (Sail.BitVec.extractLsb v__587 6 2)
                                    let rd ← do (encdec_reg_backwards mapping11_)
                                    if ((← do
                                         let imm := (imm_5_5_ +++ imm_4_0_)
                                         (currentlyEnabled Ext_Zca)) : Bool)
                                    then
                                      (pure (some
                                          (let imm := (imm_5_5_ +++ imm_4_0_)
                                          true)))
                                    else (pure none))
                                else (pure none)) with
                              | .some result => (pure result)
                              | none =>
                                (do
                                  match (← do
                                    let v__580 := head_exp_
                                    if (((← do
                                           let nzimm_5_5_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__580 12 12)
                                           let nzimm_4_3_ : (BitVec 2) :=
                                             (Sail.BitVec.extractLsb v__580 4 3)
                                           let nzimm_2_2_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__580 5 5)
                                           let nzimm_1_1_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__580 2 2)
                                           let nzimm_0_0_ : (BitVec 1) :=
                                             (Sail.BitVec.extractLsb v__580 6 6)
                                           let nzimm :=
                                             ((((nzimm_5_5_ +++ nzimm_4_3_) +++ nzimm_2_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                                           (pure ((nzimm != 0b000000#6) && (← (currentlyEnabled
                                                   Ext_Zca))))) && (((Sail.BitVec.extractLsb v__580
                                               15 13) == (0b011#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                 v__580 11 7) == (0b00010#5 : (BitVec 5))) && ((Sail.BitVec.extractLsb
                                                 v__580 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                    then
                                      (let nzimm_5_5_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__580 12 12)
                                      let nzimm_4_3_ : (BitVec 2) :=
                                        (Sail.BitVec.extractLsb v__580 4 3)
                                      let nzimm_2_2_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__580 5 5)
                                      let nzimm_1_1_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__580 2 2)
                                      let nzimm_0_0_ : (BitVec 1) :=
                                        (Sail.BitVec.extractLsb v__580 6 6)
                                      (pure (some
                                          (let nzimm :=
                                            ((((nzimm_5_5_ +++ nzimm_4_3_) +++ nzimm_2_2_) +++ nzimm_1_1_) +++ nzimm_0_0_)
                                          true))))
                                    else
                                      (do
                                        if (((let mapping12_ : (BitVec 5) :=
                                               (Sail.BitVec.extractLsb v__580 11 7)
                                             (encdec_reg_backwards_matches mapping12_)) && (((Sail.BitVec.extractLsb
                                                   v__580 15 13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                   v__580 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                        then
                                          (do
                                            let mapping12_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__580 11 7)
                                            let imm_5_5_ : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__580 12 12)
                                            let imm_4_0_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__580 6 2)
                                            let rd ← do (encdec_reg_backwards mapping12_)
                                            if ((← do
                                                 let imm := (imm_5_5_ +++ imm_4_0_)
                                                 (pure ((bne rd sp) && ((imm != 0b000000#6) && (← (currentlyEnabled
                                                           Ext_Zca)))))) : Bool)
                                            then
                                              (pure (some
                                                  (let imm := (imm_5_5_ +++ imm_4_0_)
                                                  true)))
                                            else (pure none))
                                        else (pure none))) with
                                  | .some result => (pure result)
                                  | none =>
                                    (do
                                      match (← do
                                        let v__576 := head_exp_
                                        if (((let mapping13_ : (BitVec 3) :=
                                               (Sail.BitVec.extractLsb v__576 9 7)
                                             (encdec_creg_backwards_matches mapping13_)) && (((Sail.BitVec.extractLsb
                                                   v__576 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                     v__576 11 10) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                     v__576 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                        then
                                          (do
                                            let shamt_5_5_ : (BitVec 1) :=
                                              (Sail.BitVec.extractLsb v__576 12 12)
                                            let shamt_4_0_ : (BitVec 5) :=
                                              (Sail.BitVec.extractLsb v__576 6 2)
                                            let mapping13_ : (BitVec 3) :=
                                              (Sail.BitVec.extractLsb v__576 9 7)
                                            let rsd := (encdec_creg_backwards mapping13_)
                                            if ((← do
                                                 let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                 (pure (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled
                                                         Ext_Zca))))) : Bool)
                                            then
                                              (pure (some
                                                  (let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                  true)))
                                            else (pure none))
                                        else (pure none)) with
                                      | .some result => (pure result)
                                      | none =>
                                        (do
                                          match (← do
                                            let v__572 := head_exp_
                                            if (((let mapping14_ : (BitVec 3) :=
                                                   (Sail.BitVec.extractLsb v__572 9 7)
                                                 (encdec_creg_backwards_matches mapping14_)) && (((Sail.BitVec.extractLsb
                                                       v__572 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                         v__572 11 10) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                         v__572 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                            then
                                              (do
                                                let shamt_5_5_ : (BitVec 1) :=
                                                  (Sail.BitVec.extractLsb v__572 12 12)
                                                let shamt_4_0_ : (BitVec 5) :=
                                                  (Sail.BitVec.extractLsb v__572 6 2)
                                                let mapping14_ : (BitVec 3) :=
                                                  (Sail.BitVec.extractLsb v__572 9 7)
                                                let rsd := (encdec_creg_backwards mapping14_)
                                                if ((← do
                                                     let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                     (pure (((xlen == 64) || ((BitVec.access shamt 5) == 0#1)) && (← (currentlyEnabled
                                                             Ext_Zca))))) : Bool)
                                                then
                                                  (pure (some
                                                      (let shamt := (shamt_5_5_ +++ shamt_4_0_)
                                                      true)))
                                                else (pure none))
                                            else (pure none)) with
                                          | .some result => (pure result)
                                          | none =>
                                            (do
                                              match (← do
                                                let v__568 := head_exp_
                                                if (((let mapping15_ : (BitVec 3) :=
                                                       (Sail.BitVec.extractLsb v__568 9 7)
                                                     (encdec_creg_backwards_matches mapping15_)) && (((Sail.BitVec.extractLsb
                                                           v__568 15 13) == (0b100#3 : (BitVec 3))) && (((Sail.BitVec.extractLsb
                                                             v__568 11 10) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                             v__568 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                then
                                                  (do
                                                    let mapping15_ : (BitVec 3) :=
                                                      (Sail.BitVec.extractLsb v__568 9 7)
                                                    let imm_5_5_ : (BitVec 1) :=
                                                      (Sail.BitVec.extractLsb v__568 12 12)
                                                    let imm_4_0_ : (BitVec 5) :=
                                                      (Sail.BitVec.extractLsb v__568 6 2)
                                                    let rsd := (encdec_creg_backwards mapping15_)
                                                    if ((← do
                                                         let imm := (imm_5_5_ +++ imm_4_0_)
                                                         (currentlyEnabled Ext_Zca)) : Bool)
                                                    then
                                                      (pure (some
                                                          (let imm := (imm_5_5_ +++ imm_4_0_)
                                                          true)))
                                                    else (pure none))
                                                else (pure none)) with
                                              | .some result => (pure result)
                                              | none =>
                                                (do
                                                  match (← do
                                                    let v__562 := head_exp_
                                                    if (((let mapping17_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__562 4 2)
                                                         let mapping16_ : (BitVec 3) :=
                                                           (Sail.BitVec.extractLsb v__562 9 7)
                                                         ((encdec_creg_backwards_matches mapping16_) && (encdec_creg_backwards_matches
                                                             mapping17_))) && (((Sail.BitVec.extractLsb
                                                               v__562 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                 v__562 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                 v__562 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                    then
                                                      (do
                                                        let mapping17_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__562 4 2)
                                                        let mapping16_ : (BitVec 3) :=
                                                          (Sail.BitVec.extractLsb v__562 9 7)
                                                        match ((encdec_creg_backwards mapping16_), (encdec_creg_backwards
                                                          mapping17_)) with
                                                        | (rsd, rs2) =>
                                                          (do
                                                            if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                            then (pure (some true))
                                                            else (pure none)))
                                                    else (pure none)) with
                                                  | .some result => (pure result)
                                                  | none =>
                                                    (do
                                                      match (← do
                                                        let v__556 := head_exp_
                                                        if (((let mapping19_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__556 4 2)
                                                             let mapping18_ : (BitVec 3) :=
                                                               (Sail.BitVec.extractLsb v__556 9 7)
                                                             ((encdec_creg_backwards_matches
                                                                 mapping18_) && (encdec_creg_backwards_matches
                                                                 mapping19_))) && (((Sail.BitVec.extractLsb
                                                                   v__556 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                     v__556 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                     v__556 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                        then
                                                          (do
                                                            let mapping19_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__556 4 2)
                                                            let mapping18_ : (BitVec 3) :=
                                                              (Sail.BitVec.extractLsb v__556 9 7)
                                                            match ((encdec_creg_backwards mapping18_), (encdec_creg_backwards
                                                              mapping19_)) with
                                                            | (rsd, rs2) =>
                                                              (do
                                                                if ((← (currentlyEnabled Ext_Zca)) : Bool)
                                                                then (pure (some true))
                                                                else (pure none)))
                                                        else (pure none)) with
                                                      | .some result => (pure result)
                                                      | none =>
                                                        (do
                                                          match (← do
                                                            let v__550 := head_exp_
                                                            if (((let mapping21_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__550 4
                                                                     2)
                                                                 let mapping20_ : (BitVec 3) :=
                                                                   (Sail.BitVec.extractLsb v__550 9
                                                                     7)
                                                                 ((encdec_creg_backwards_matches
                                                                     mapping20_) && (encdec_creg_backwards_matches
                                                                     mapping21_))) && (((Sail.BitVec.extractLsb
                                                                       v__550 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                         v__550 6 5) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                         v__550 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                            then
                                                              (do
                                                                let mapping21_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__550 4 2)
                                                                let mapping20_ : (BitVec 3) :=
                                                                  (Sail.BitVec.extractLsb v__550 9 7)
                                                                match ((encdec_creg_backwards
                                                                  mapping20_), (encdec_creg_backwards
                                                                  mapping21_)) with
                                                                | (rsd, rs2) =>
                                                                  (do
                                                                    if ((← (currentlyEnabled
                                                                           Ext_Zca)) : Bool)
                                                                    then (pure (some true))
                                                                    else (pure none)))
                                                            else (pure none)) with
                                                          | .some result => (pure result)
                                                          | none =>
                                                            (do
                                                              match (← do
                                                                let v__544 := head_exp_
                                                                if (((let mapping23_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__544 4 2)
                                                                     let mapping22_ : (BitVec 3) :=
                                                                       (Sail.BitVec.extractLsb
                                                                         v__544 9 7)
                                                                     ((encdec_creg_backwards_matches
                                                                         mapping22_) && (encdec_creg_backwards_matches
                                                                         mapping23_))) && (((Sail.BitVec.extractLsb
                                                                           v__544 15 10) == (0b100011#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                             v__544 6 5) == (0b11#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                             v__544 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                then
                                                                  (do
                                                                    let mapping23_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__544
                                                                        4 2)
                                                                    let mapping22_ : (BitVec 3) :=
                                                                      (Sail.BitVec.extractLsb v__544
                                                                        9 7)
                                                                    match ((encdec_creg_backwards
                                                                      mapping22_), (encdec_creg_backwards
                                                                      mapping23_)) with
                                                                    | (rsd, rs2) =>
                                                                      (do
                                                                        if ((← (currentlyEnabled
                                                                               Ext_Zca)) : Bool)
                                                                        then (pure (some true))
                                                                        else (pure none)))
                                                                else (pure none)) with
                                                              | .some result => (pure result)
                                                              | none =>
                                                                (do
                                                                  match (← do
                                                                    let v__538 := head_exp_
                                                                    if (((let mapping25_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__538 4 2)
                                                                         let mapping24_ : (BitVec 3) :=
                                                                           (Sail.BitVec.extractLsb
                                                                             v__538 9 7)
                                                                         ((encdec_creg_backwards_matches
                                                                             mapping24_) && (encdec_creg_backwards_matches
                                                                             mapping25_))) && (((Sail.BitVec.extractLsb
                                                                               v__538 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                 v__538 6 5) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                 v__538 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                    then
                                                                      (do
                                                                        let mapping25_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__538 4 2)
                                                                        let mapping24_ : (BitVec 3) :=
                                                                          (Sail.BitVec.extractLsb
                                                                            v__538 9 7)
                                                                        match ((encdec_creg_backwards
                                                                          mapping24_), (encdec_creg_backwards
                                                                          mapping25_)) with
                                                                        | (rsd, rs2) =>
                                                                          (do
                                                                            if (((xlen == 64) && (← (currentlyEnabled
                                                                                     Ext_Zca))) : Bool)
                                                                            then (pure (some true))
                                                                            else (pure none)))
                                                                    else (pure none)) with
                                                                  | .some result => (pure result)
                                                                  | none =>
                                                                    (do
                                                                      match (← do
                                                                        let v__532 := head_exp_
                                                                        if (((let mapping27_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__532 4 2)
                                                                             let mapping26_ : (BitVec 3) :=
                                                                               (Sail.BitVec.extractLsb
                                                                                 v__532 9 7)
                                                                             ((encdec_creg_backwards_matches
                                                                                 mapping26_) && (encdec_creg_backwards_matches
                                                                                 mapping27_))) && (((Sail.BitVec.extractLsb
                                                                                   v__532 15 10) == (0b100111#6 : (BitVec 6))) && (((Sail.BitVec.extractLsb
                                                                                     v__532 6 5) == (0b01#2 : (BitVec 2))) && ((Sail.BitVec.extractLsb
                                                                                     v__532 1 0) == (0b01#2 : (BitVec 2)))))) : Bool)
                                                                        then
                                                                          (do
                                                                            let mapping27_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__532 4 2)
                                                                            let mapping26_ : (BitVec 3) :=
                                                                              (Sail.BitVec.extractLsb
                                                                                v__532 9 7)
                                                                            match ((encdec_creg_backwards
                                                                              mapping26_), (encdec_creg_backwards
                                                                              mapping27_)) with
                                                                            | (rsd, rs2) =>
                                                                              (do
                                                                                if (((xlen == 64) && (← (currentlyEnabled
                                                                                         Ext_Zca))) : Bool)
                                                                                then
                                                                                  (pure (some true))
                                                                                else (pure none)))
                                                                        else (pure none)) with
                                                                      | .some result =>
                                                                        (pure result)
                                                                      | none =>
                                                                        (do
                                                                          match (← do
                                                                            let v__526 := head_exp_
                                                                            if (((← do
                                                                                   let imm_9_9_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 8 8)
                                                                                   let imm_8_7_ : (BitVec 2) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 10 9)
                                                                                   let imm_6_6_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 6 6)
                                                                                   let imm_5_5_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 7 7)
                                                                                   let imm_4_4_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 2 2)
                                                                                   let imm_3_3_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 11 11)
                                                                                   let imm_2_0_ : (BitVec 3) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 5 3)
                                                                                   let imm_10_10_ : (BitVec 1) :=
                                                                                     (Sail.BitVec.extractLsb
                                                                                       v__526 12 12)
                                                                                   let imm :=
                                                                                     (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                                                                   (currentlyEnabled
                                                                                     Ext_Zca)) && (((Sail.BitVec.extractLsb
                                                                                       v__526 15 13) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                       v__526 1 0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                            then
                                                                              (let imm_9_9_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 8 8)
                                                                              let imm_8_7_ : (BitVec 2) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 10 9)
                                                                              let imm_6_6_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 6 6)
                                                                              let imm_5_5_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 7 7)
                                                                              let imm_4_4_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 2 2)
                                                                              let imm_3_3_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 11 11)
                                                                              let imm_2_0_ : (BitVec 3) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 5 3)
                                                                              let imm_10_10_ : (BitVec 1) :=
                                                                                (Sail.BitVec.extractLsb
                                                                                  v__526 12 12)
                                                                              (pure (some
                                                                                  (let imm :=
                                                                                    (((((((imm_10_10_ +++ imm_9_9_) +++ imm_8_7_) +++ imm_6_6_) +++ imm_5_5_) +++ imm_4_4_) +++ imm_3_3_) +++ imm_2_0_)
                                                                                  true))))
                                                                            else
                                                                              (do
                                                                                if (((let mapping28_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__526 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping28_)) && (((Sail.BitVec.extractLsb
                                                                                           v__526 15
                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__526 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping28_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__526 9 7)
                                                                                    let imm_7_7_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__526 12 12)
                                                                                    let imm_6_5_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__526 6 5)
                                                                                    let imm_4_4_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__526 2 2)
                                                                                    let imm_3_2_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__526 11 10)
                                                                                    let imm_1_0_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__526 4 3)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping28_)
                                                                                    if ((← do
                                                                                         let imm :=
                                                                                           ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                         (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          (let imm :=
                                                                                            ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                          true)))
                                                                                    else (pure none))
                                                                                else (pure none))) with
                                                                          | .some result =>
                                                                            (pure result)
                                                                          | none =>
                                                                            (do
                                                                              match (← do
                                                                                let v__523 :=
                                                                                  head_exp_
                                                                                if (((let mapping29_ : (BitVec 3) :=
                                                                                       (Sail.BitVec.extractLsb
                                                                                         v__523 9 7)
                                                                                     (encdec_creg_backwards_matches
                                                                                       mapping29_)) && (((Sail.BitVec.extractLsb
                                                                                           v__523 15
                                                                                           13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                           v__523 1
                                                                                           0) == (0b01#2 : (BitVec 2))))) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let mapping29_ : (BitVec 3) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__523 9 7)
                                                                                    let imm_7_7_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__523 12 12)
                                                                                    let imm_6_5_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__523 6 5)
                                                                                    let imm_4_4_ : (BitVec 1) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__523 2 2)
                                                                                    let imm_3_2_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__523 11 10)
                                                                                    let imm_1_0_ : (BitVec 2) :=
                                                                                      (Sail.BitVec.extractLsb
                                                                                        v__523 4 3)
                                                                                    let rs :=
                                                                                      (encdec_creg_backwards
                                                                                        mapping29_)
                                                                                    if ((← do
                                                                                         let imm :=
                                                                                           ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                         (currentlyEnabled
                                                                                           Ext_Zca)) : Bool)
                                                                                    then
                                                                                      (pure (some
                                                                                          (let imm :=
                                                                                            ((((imm_7_7_ +++ imm_6_5_) +++ imm_4_4_) +++ imm_3_2_) +++ imm_1_0_)
                                                                                          true)))
                                                                                    else (pure none))
                                                                                else (pure none)) with
                                                                              | .some result =>
                                                                                (pure result)
                                                                              | none =>
                                                                                (do
                                                                                  match (← do
                                                                                    let v__520 :=
                                                                                      head_exp_
                                                                                    if (((let mapping30_ : (BitVec 5) :=
                                                                                           (Sail.BitVec.extractLsb
                                                                                             v__520
                                                                                             11 7)
                                                                                         (encdec_reg_backwards_matches
                                                                                           mapping30_)) && (((Sail.BitVec.extractLsb
                                                                                               v__520
                                                                                               15 13) == (0b000#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                               v__520
                                                                                               1 0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let shamt_5_5_ : (BitVec 1) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__520
                                                                                            12 12)
                                                                                        let shamt_4_0_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__520 6
                                                                                            2)
                                                                                        let mapping30_ : (BitVec 5) :=
                                                                                          (Sail.BitVec.extractLsb
                                                                                            v__520
                                                                                            11 7)
                                                                                        let rsd ← do
                                                                                          (encdec_reg_backwards
                                                                                            mapping30_)
                                                                                        if ((← do
                                                                                             let shamt :=
                                                                                               (shamt_5_5_ +++ shamt_4_0_)
                                                                                             (pure (((xlen == 64) || ((BitVec.access
                                                                                                       shamt
                                                                                                       5) == 0#1)) && (← (currentlyEnabled
                                                                                                     Ext_Zca))))) : Bool)
                                                                                        then
                                                                                          (pure (some
                                                                                              (let shamt :=
                                                                                                (shamt_5_5_ +++ shamt_4_0_)
                                                                                              true)))
                                                                                        else
                                                                                          (pure none))
                                                                                    else (pure none)) with
                                                                                  | .some result =>
                                                                                    (pure result)
                                                                                  | none =>
                                                                                    (do
                                                                                      match (← do
                                                                                        let v__517 :=
                                                                                          head_exp_
                                                                                        if (((let mapping31_ : (BitVec 5) :=
                                                                                               (Sail.BitVec.extractLsb
                                                                                                 v__517
                                                                                                 11
                                                                                                 7)
                                                                                             (encdec_reg_backwards_matches
                                                                                               mapping31_)) && (((Sail.BitVec.extractLsb
                                                                                                   v__517
                                                                                                   15
                                                                                                   13) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                   v__517
                                                                                                   1
                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let uimm_5_4_ : (BitVec 2) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__517
                                                                                                3 2)
                                                                                            let uimm_3_3_ : (BitVec 1) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__517
                                                                                                12
                                                                                                12)
                                                                                            let uimm_2_0_ : (BitVec 3) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__517
                                                                                                6 4)
                                                                                            let mapping31_ : (BitVec 5) :=
                                                                                              (Sail.BitVec.extractLsb
                                                                                                v__517
                                                                                                11 7)
                                                                                            let rd ← do
                                                                                              (encdec_reg_backwards
                                                                                                mapping31_)
                                                                                            if ((← do
                                                                                                 let uimm :=
                                                                                                   ((uimm_5_4_ +++ uimm_3_3_) +++ uimm_2_0_)
                                                                                                 (pure ((bne
                                                                                                       rd
                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                         Ext_Zca))))) : Bool)
                                                                                            then
                                                                                              (pure (some
                                                                                                  (let uimm :=
                                                                                                    ((uimm_5_4_ +++ uimm_3_3_) +++ uimm_2_0_)
                                                                                                  true)))
                                                                                            else
                                                                                              (pure none))
                                                                                        else
                                                                                          (pure none)) with
                                                                                      | .some result =>
                                                                                        (pure result)
                                                                                      | none =>
                                                                                        (do
                                                                                          match (← do
                                                                                            let v__514 :=
                                                                                              head_exp_
                                                                                            if (((let mapping32_ : (BitVec 5) :=
                                                                                                   (Sail.BitVec.extractLsb
                                                                                                     v__514
                                                                                                     11
                                                                                                     7)
                                                                                                 (encdec_reg_backwards_matches
                                                                                                   mapping32_)) && (((Sail.BitVec.extractLsb
                                                                                                       v__514
                                                                                                       15
                                                                                                       13) == (0b011#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                       v__514
                                                                                                       1
                                                                                                       0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let uimm_5_3_ : (BitVec 3) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__514
                                                                                                    4
                                                                                                    2)
                                                                                                let uimm_2_2_ : (BitVec 1) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__514
                                                                                                    12
                                                                                                    12)
                                                                                                let uimm_1_0_ : (BitVec 2) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__514
                                                                                                    6
                                                                                                    5)
                                                                                                let mapping32_ : (BitVec 5) :=
                                                                                                  (Sail.BitVec.extractLsb
                                                                                                    v__514
                                                                                                    11
                                                                                                    7)
                                                                                                let rd ← do
                                                                                                  (encdec_reg_backwards
                                                                                                    mapping32_)
                                                                                                if ((← do
                                                                                                     let uimm :=
                                                                                                       ((uimm_5_3_ +++ uimm_2_2_) +++ uimm_1_0_)
                                                                                                     (pure ((bne
                                                                                                           rd
                                                                                                           zreg) && ((xlen == 64) && (← (currentlyEnabled
                                                                                                               Ext_Zca)))))) : Bool)
                                                                                                then
                                                                                                  (pure (some
                                                                                                      (let uimm :=
                                                                                                        ((uimm_5_3_ +++ uimm_2_2_) +++ uimm_1_0_)
                                                                                                      true)))
                                                                                                else
                                                                                                  (pure none))
                                                                                            else
                                                                                              (pure none)) with
                                                                                          | .some result =>
                                                                                            (pure result)
                                                                                          | none =>
                                                                                            (do
                                                                                              match (← do
                                                                                                let v__511 :=
                                                                                                  head_exp_
                                                                                                if (((let mapping33_ : (BitVec 5) :=
                                                                                                       (Sail.BitVec.extractLsb
                                                                                                         v__511
                                                                                                         6
                                                                                                         2)
                                                                                                     (encdec_reg_backwards_matches
                                                                                                       mapping33_)) && (((Sail.BitVec.extractLsb
                                                                                                           v__511
                                                                                                           15
                                                                                                           13) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                           v__511
                                                                                                           1
                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let uimm_5_4_ : (BitVec 2) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__511
                                                                                                        8
                                                                                                        7)
                                                                                                    let uimm_3_0_ : (BitVec 4) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__511
                                                                                                        12
                                                                                                        9)
                                                                                                    let mapping33_ : (BitVec 5) :=
                                                                                                      (Sail.BitVec.extractLsb
                                                                                                        v__511
                                                                                                        6
                                                                                                        2)
                                                                                                    let rs2 ← do
                                                                                                      (encdec_reg_backwards
                                                                                                        mapping33_)
                                                                                                    if ((← do
                                                                                                         let uimm :=
                                                                                                           (uimm_5_4_ +++ uimm_3_0_)
                                                                                                         (currentlyEnabled
                                                                                                           Ext_Zca)) : Bool)
                                                                                                    then
                                                                                                      (pure (some
                                                                                                          (let uimm :=
                                                                                                            (uimm_5_4_ +++ uimm_3_0_)
                                                                                                          true)))
                                                                                                    else
                                                                                                      (pure none))
                                                                                                else
                                                                                                  (pure none)) with
                                                                                              | .some result =>
                                                                                                (pure result)
                                                                                              | none =>
                                                                                                (do
                                                                                                  match (← do
                                                                                                    let v__508 :=
                                                                                                      head_exp_
                                                                                                    if (((let mapping34_ : (BitVec 5) :=
                                                                                                           (Sail.BitVec.extractLsb
                                                                                                             v__508
                                                                                                             6
                                                                                                             2)
                                                                                                         (encdec_reg_backwards_matches
                                                                                                           mapping34_)) && (((Sail.BitVec.extractLsb
                                                                                                               v__508
                                                                                                               15
                                                                                                               13) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.extractLsb
                                                                                                               v__508
                                                                                                               1
                                                                                                               0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let uimm_5_3_ : (BitVec 3) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__508
                                                                                                            9
                                                                                                            7)
                                                                                                        let uimm_2_0_ : (BitVec 3) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__508
                                                                                                            12
                                                                                                            10)
                                                                                                        let mapping34_ : (BitVec 5) :=
                                                                                                          (Sail.BitVec.extractLsb
                                                                                                            v__508
                                                                                                            6
                                                                                                            2)
                                                                                                        let rs2 ← do
                                                                                                          (encdec_reg_backwards
                                                                                                            mapping34_)
                                                                                                        if ((← do
                                                                                                             let uimm :=
                                                                                                               (uimm_5_3_ +++ uimm_2_0_)
                                                                                                             (pure ((xlen == 64) && (← (currentlyEnabled
                                                                                                                     Ext_Zca))))) : Bool)
                                                                                                        then
                                                                                                          (pure (some
                                                                                                              (let uimm :=
                                                                                                                (uimm_5_3_ +++ uimm_2_0_)
                                                                                                              true)))
                                                                                                        else
                                                                                                          (pure none))
                                                                                                    else
                                                                                                      (pure none)) with
                                                                                                  | .some result =>
                                                                                                    (pure result)
                                                                                                  | none =>
                                                                                                    (do
                                                                                                      match (← do
                                                                                                        let v__503 :=
                                                                                                          head_exp_
                                                                                                        if (((let mapping35_ : (BitVec 5) :=
                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                 v__503
                                                                                                                 11
                                                                                                                 7)
                                                                                                             (encdec_reg_backwards_matches
                                                                                                               mapping35_)) && (((Sail.BitVec.extractLsb
                                                                                                                   v__503
                                                                                                                   15
                                                                                                                   12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                   v__503
                                                                                                                   6
                                                                                                                   0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let mapping35_ : (BitVec 5) :=
                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                v__503
                                                                                                                11
                                                                                                                7)
                                                                                                            let rs1 ← do
                                                                                                              (encdec_reg_backwards
                                                                                                                mapping35_)
                                                                                                            if (((bne
                                                                                                                   rs1
                                                                                                                   zreg) && (← (currentlyEnabled
                                                                                                                     Ext_Zca))) : Bool)
                                                                                                            then
                                                                                                              (pure (some
                                                                                                                  true))
                                                                                                            else
                                                                                                              (pure none))
                                                                                                        else
                                                                                                          (pure none)) with
                                                                                                      | .some result =>
                                                                                                        (pure result)
                                                                                                      | none =>
                                                                                                        (do
                                                                                                          match (← do
                                                                                                            let v__498 :=
                                                                                                              head_exp_
                                                                                                            if (((let mapping36_ : (BitVec 5) :=
                                                                                                                   (Sail.BitVec.extractLsb
                                                                                                                     v__498
                                                                                                                     11
                                                                                                                     7)
                                                                                                                 (encdec_reg_backwards_matches
                                                                                                                   mapping36_)) && (((Sail.BitVec.extractLsb
                                                                                                                       v__498
                                                                                                                       15
                                                                                                                       12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                       v__498
                                                                                                                       6
                                                                                                                       0) == (0b0000010#7 : (BitVec 7))))) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let mapping36_ : (BitVec 5) :=
                                                                                                                  (Sail.BitVec.extractLsb
                                                                                                                    v__498
                                                                                                                    11
                                                                                                                    7)
                                                                                                                let rs1 ← do
                                                                                                                  (encdec_reg_backwards
                                                                                                                    mapping36_)
                                                                                                                if (((bne
                                                                                                                       rs1
                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                then
                                                                                                                  (pure (some
                                                                                                                      true))
                                                                                                                else
                                                                                                                  (pure none))
                                                                                                            else
                                                                                                              (pure none)) with
                                                                                                          | .some result =>
                                                                                                            (pure result)
                                                                                                          | none =>
                                                                                                            (do
                                                                                                              match (← do
                                                                                                                let v__494 :=
                                                                                                                  head_exp_
                                                                                                                if (((let mapping38_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__494
                                                                                                                         6
                                                                                                                         2)
                                                                                                                     let mapping37_ : (BitVec 5) :=
                                                                                                                       (Sail.BitVec.extractLsb
                                                                                                                         v__494
                                                                                                                         11
                                                                                                                         7)
                                                                                                                     ((encdec_reg_backwards_matches
                                                                                                                         mapping37_) && (encdec_reg_backwards_matches
                                                                                                                         mapping38_))) && (((Sail.BitVec.extractLsb
                                                                                                                           v__494
                                                                                                                           15
                                                                                                                           12) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                           v__494
                                                                                                                           1
                                                                                                                           0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let mapping38_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__494
                                                                                                                        6
                                                                                                                        2)
                                                                                                                    let mapping37_ : (BitVec 5) :=
                                                                                                                      (Sail.BitVec.extractLsb
                                                                                                                        v__494
                                                                                                                        11
                                                                                                                        7)
                                                                                                                    match ((← (encdec_reg_backwards
                                                                                                                        mapping37_)), (← (encdec_reg_backwards
                                                                                                                        mapping38_))) with
                                                                                                                    | (rd, rs2) =>
                                                                                                                      (do
                                                                                                                        if (((bne
                                                                                                                               rs2
                                                                                                                               zreg) && (← (currentlyEnabled
                                                                                                                                 Ext_Zca))) : Bool)
                                                                                                                        then
                                                                                                                          (pure (some
                                                                                                                              true))
                                                                                                                        else
                                                                                                                          (pure none)))
                                                                                                                else
                                                                                                                  (pure none)) with
                                                                                                              | .some result =>
                                                                                                                (pure result)
                                                                                                              | none =>
                                                                                                                (do
                                                                                                                  match (← do
                                                                                                                    let v__486 :=
                                                                                                                      head_exp_
                                                                                                                    if (((← (currentlyEnabled
                                                                                                                             Ext_Zca)) && (v__486 == (0x9002#16 : (BitVec 16)))) : Bool)
                                                                                                                    then
                                                                                                                      (pure (some
                                                                                                                          true))
                                                                                                                    else
                                                                                                                      (do
                                                                                                                        if (((let mapping40_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__486
                                                                                                                                 6
                                                                                                                                 2)
                                                                                                                             let mapping39_ : (BitVec 5) :=
                                                                                                                               (Sail.BitVec.extractLsb
                                                                                                                                 v__486
                                                                                                                                 11
                                                                                                                                 7)
                                                                                                                             ((encdec_reg_backwards_matches
                                                                                                                                 mapping39_) && (encdec_reg_backwards_matches
                                                                                                                                 mapping40_))) && (((Sail.BitVec.extractLsb
                                                                                                                                   v__486
                                                                                                                                   15
                                                                                                                                   12) == (0x9#4 : (BitVec 4))) && ((Sail.BitVec.extractLsb
                                                                                                                                   v__486
                                                                                                                                   1
                                                                                                                                   0) == (0b10#2 : (BitVec 2))))) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let mapping40_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__486
                                                                                                                                6
                                                                                                                                2)
                                                                                                                            let mapping39_ : (BitVec 5) :=
                                                                                                                              (Sail.BitVec.extractLsb
                                                                                                                                v__486
                                                                                                                                11
                                                                                                                                7)
                                                                                                                            match ((← (encdec_reg_backwards
                                                                                                                                mapping39_)), (← (encdec_reg_backwards
                                                                                                                                mapping40_))) with
                                                                                                                            | (rsd, rs2) =>
                                                                                                                              (do
                                                                                                                                if (((bne
                                                                                                                                       rs2
                                                                                                                                       zreg) && (← (currentlyEnabled
                                                                                                                                         Ext_Zca))) : Bool)
                                                                                                                                then
                                                                                                                                  (pure (some
                                                                                                                                      true))
                                                                                                                                else
                                                                                                                                  (pure none)))
                                                                                                                        else
                                                                                                                          (pure none))) with
                                                                                                                  | .some result =>
                                                                                                                    (pure result)
                                                                                                                  | none =>
                                                                                                                    (match head_exp_ with
                                                                                                                    | s =>
                                                                                                                      (pure true))))))))))))))))))))))))))))))

def execute_ZICBOZ (rs1 : regidx) : SailM ExecutionResult := SailME.run do
  match (← (feature_enabled_for_priv (← readReg cur_privilege)
      (_get_MEnvcfg_CBZE (← readReg menvcfg)) (_get_SEnvcfg_CBZE (← (read_senvcfg ()))) 0#1)) with
  | .FEATURE_ENABLED => (pure ())
  | .FEATURE_ILLEGAL => SailME.throw ((Illegal_Instruction ()) : ExecutionResult)
  | .FEATURE_VIRTUAL => SailME.throw ((Virtual_Instruction ()) : ExecutionResult)
  let rs1_val ← do (rX_bits rs1)
  let cache_block_size := (2 ^i plat_cache_block_size_exp)
  let access : (MemoryAccessType mem_payload) := (CacheAccess (CB_zero ()))
  let negative_offset :=
    ((rs1_val &&& (Complement.complement
          (zero_extend (m := 64) (ones (n := plat_cache_block_size_exp))))) - rs1_val)
  match (← (get_transformed_data_addr rs1 negative_offset access cache_block_size)) with
  | .Ext_DataAddr_Error e => (pure (Ext_DataAddr_Check_Failure e))
  | .Ext_DataAddr_OK vaddr =>
    (do
      match (← (translateAddr vaddr access)) with
      | .Err (e, _) => (memory_exception (sub_virtaddr_xlenbits vaddr negative_offset) e)
      | .Ok (paddr, pbmt, _) =>
        (do
          match (← (mem_write_ea paddr cache_block_size access pbmt false false false)) with
          | .Err (exc_addr, e) =>
            (do
              assert (exc_addr == paddr) "extensions/Zicboz/zicboz_insts.sail:57.38-57.39"
              (memory_exception (sub_virtaddr_xlenbits vaddr negative_offset) e))
          | .Ok _ =>
            (do
              match (← (mem_write_value paddr cache_block_size
                  (zeros (n := (8 *i (2 ^i plat_cache_block_size_exp)))) access pbmt false false
                  false)) with
              | .Ok true => (pure RETIRE_SUCCESS)
              | .Ok false =>
                (internal_error "extensions/Zicboz/zicboz_insts.sail" 63
                  "store got false from mem_write_value")
              | .Err (exc_addr, e) =>
                (do
                  assert (exc_addr == paddr) "extensions/Zicboz/zicboz_insts.sail:66.42-66.43"
                  (memory_exception (sub_virtaddr_xlenbits vaddr negative_offset) e)))))

def execute_ZICBOM (arg0 : cbop_zicbom) (arg1 : regidx) : SailM ExecutionResult := do
  let merge_var := (arg0, arg1)
  match merge_var with
  | (.CBO_CLEAN, rs1) =>
    (do
      match (← (feature_enabled_for_priv (← readReg cur_privilege)
          (_get_MEnvcfg_CBCFE (← readReg menvcfg)) (_get_SEnvcfg_CBCFE (← (read_senvcfg ())))
          0#1)) with
      | .FEATURE_ENABLED => (process_clean_inval rs1 CBO_CLEAN)
      | .FEATURE_ILLEGAL => (pure (Illegal_Instruction ()))
      | .FEATURE_VIRTUAL => (pure (Virtual_Instruction ())))
  | (.CBO_FLUSH, rs1) =>
    (do
      match (← (feature_enabled_for_priv (← readReg cur_privilege)
          (_get_MEnvcfg_CBCFE (← readReg menvcfg)) (_get_SEnvcfg_CBCFE (← (read_senvcfg ())))
          0#1)) with
      | .FEATURE_ENABLED => (process_clean_inval rs1 CBO_FLUSH)
      | .FEATURE_ILLEGAL => (pure (Illegal_Instruction ()))
      | .FEATURE_VIRTUAL => (pure (Virtual_Instruction ())))
  | (.CBO_INVAL, rs1) =>
    (do
      match (← (cbop_priv_check (← readReg cur_privilege))) with
      | .CBOP_ILLEGAL => (pure (Illegal_Instruction ()))
      | .CBOP_ILLEGAL_VIRTUAL =>
        (internal_error "extensions/Zicbom/zicbom_insts.sail" 124 "unimplemented")
      | .CBOP_INVAL_INVAL => (process_clean_inval rs1 CBO_INVAL)
      | .CBOP_INVAL_FLUSH => (process_clean_inval rs1 CBO_FLUSH))

def execute_WFI (_ : Unit) : SailM ExecutionResult := do
  match (← readReg cur_privilege) with
  | .Machine => (pure (Enter_Wait WAIT_WFI))
  | .Supervisor => (pure (Enter_Wait WAIT_WFI))
  | .User =>
    (if (plat_wfi_available_to_usermode : Bool)
    then (pure (Enter_Wait WAIT_WFI))
    else (pure (Illegal_Instruction ())))
  | .VirtualUser =>
    (internal_error "extensions/I/base_insts.sail" 665 "Hypervisor extension not supported")
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 666 "Hypervisor extension not supported")

def execute_UTYPE (imm : (BitVec 20)) (rd : regidx) (op : uop) : SailM ExecutionResult := do
  let off : xlenbits := (sign_extend (m := 64) (imm +++ 0x000#12))
  (wX_bits rd
    (← do
      match op with
      | .LUI => (pure off)
      | .AUIPC => (pure ((← (get_arch_pc ())) + off))))
  (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, width ∈ {1, 2, 4, 8} -/
def execute_STORE (imm : (BitVec 12)) (rs2 : regidx) (rs1 : regidx) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  assert (width ≤b xlen_bytes) "extensions/I/base_insts.sail:320.28-320.29"
  let data ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) ((width *i 8) -i 1) 0))
  match (← (vmem_write rs1 offset width data (Store Data) false false false)) with
  | .Ok _ => (pure RETIRE_SUCCESS)
  | .Err e => (pure e)

def execute_SRET (_ : Unit) : SailM ExecutionResult := do
  let sret_illegal ← (( do
    match (← readReg cur_privilege) with
    | .User => (pure true)
    | .Supervisor =>
      (pure ((not (← (currentlyEnabled Ext_S))) || ((_get_Mstatus_TSR (← readReg mstatus)) == 1#1)))
    | .Machine => (pure (not (← (currentlyEnabled Ext_S))))
    | .VirtualUser =>
      (internal_error "extensions/I/base_insts.sail" 607 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 608 "Hypervisor extension not supported") ) :
    SailM Bool )
  if (sret_illegal : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Supervisor)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          let prev_priv ← do readReg cur_privilege
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 1 1
            (_get_Mstatus_SPIE (← readReg mstatus)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 5 5 1#1)
          writeReg cur_privilege (← do
            if (((_get_Mstatus_SPP (← readReg mstatus)) == 1#1) : Bool)
            then (pure Supervisor)
            else (pure User))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 8 8 0#1)
          if ((bne (← readReg cur_privilege) Machine) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
          else (pure ())
          if ((hartSupports Ext_Zicfilp) : Bool)
          then (zicfilp_restore_elp_on_xret sRET (← readReg cur_privilege))
          else (pure ())
          (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
          if ((get_config_print_exception ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "ret-ing from "
                  (HAppend.hAppend (← (privLevel_to_str prev_priv))
                    (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
          else (pure ())
          (set_next_pc (← (prepare_xret_target Supervisor)))
          let _ : Unit := (xret_callback false)
          (pure RETIRE_SUCCESS)))

def execute_SHIFTIWOP (shamt : (BitVec 5)) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .SLLIW => (shift_bits_left rs1_val shamt)
    | .SRLIW => (shift_bits_right rs1_val shamt)
    | .SRAIW => (shift_bits_right_arith rs1_val shamt)
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_SHIFTIOP (shamt : (BitVec 6)) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let shamt := (Sail.BitVec.extractLsb shamt (log2_xlen -i 1) 0)
  (wX_bits rd
    (← do
      match op with
      | .SLLI => (pure (shift_bits_left (← (rX_bits rs1)) shamt))
      | .SRLI => (pure (shift_bits_right (← (rX_bits rs1)) shamt))
      | .SRAI => (pure (shift_bits_right_arith (← (rX_bits rs1)) shamt))))
  (pure RETIRE_SUCCESS)

def execute_SFENCE_VMA (rs1 : regidx) (rs2 : regidx) : SailM ExecutionResult := do
  let addr ← do
    if ((bne rs1 zreg) : Bool)
    then (pure (some (← (rX_bits rs1))))
    else (pure none)
  let asid ← do
    if ((bne rs2 zreg) : Bool)
    then (pure (some (Sail.BitVec.extractLsb (← (rX_bits rs2)) (asidlen -i 1) 0)))
    else (pure none)
  match (← readReg cur_privilege) with
  | .User => (pure (Illegal_Instruction ()))
  | .Supervisor =>
    (do
      match (_get_Mstatus_TVM (← readReg mstatus)) with
      | 1 => (pure (Illegal_Instruction ()))
      | _ =>
        (do
          (flush_TLB asid addr)
          (pure RETIRE_SUCCESS)))
  | .Machine =>
    (do
      (flush_TLB asid addr)
      (pure RETIRE_SUCCESS))
  | .VirtualUser => (pure (Virtual_Instruction ()))
  | .VirtualSupervisor =>
    (internal_error "extensions/I/base_insts.sail" 692 "Hypervisor extension not supported")

def execute_RTYPEW (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs1)) 31 0))
  let rs2_val ← do (pure (Sail.BitVec.extractLsb (← (rX_bits rs2)) 31 0))
  let result : (BitVec 32) :=
    match op with
    | .ADDW => (rs1_val + rs2_val)
    | .SUBW => (rs1_val - rs2_val)
    | .SLLW => (shift_bits_left rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRLW => (shift_bits_right rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
    | .SRAW => (shift_bits_right_arith rs1_val (Sail.BitVec.extractLsb rs2_val 4 0))
  (wX_bits rd (sign_extend (m := 64) result))
  (pure RETIRE_SUCCESS)

def execute_RTYPE (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  (wX_bits rd
    (← do
      match op with
      | .ADD => (pure ((← (rX_bits rs1)) + (← (rX_bits rs2))))
      | .SLT =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .SLTU =>
        (pure (zero_extend (m := 64)
            (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))))
      | .AND => (pure ((← (rX_bits rs1)) &&& (← (rX_bits rs2))))
      | .OR => (pure ((← (rX_bits rs1)) ||| (← (rX_bits rs2))))
      | .XOR => (pure ((← (rX_bits rs1)) ^^^ (← (rX_bits rs2))))
      | .SLL =>
        (pure (shift_bits_left (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SRL =>
        (pure (shift_bits_right (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))
      | .SUB => (pure ((← (rX_bits rs1)) - (← (rX_bits rs2))))
      | .SRA =>
        (pure (shift_bits_right_arith (← (rX_bits rs1))
            (Sail.BitVec.extractLsb (← (rX_bits rs2)) (log2_xlen -i 1) 0)))))
  (pure RETIRE_SUCCESS)

def execute_MRET (_ : Unit) : SailM ExecutionResult := do
  if ((bne (← readReg cur_privilege) Machine) : Bool)
  then (pure (Illegal_Instruction ()))
  else
    (do
      if ((not (ext_check_xret_priv Machine)) : Bool)
      then (pure (Ext_XRET_Priv_Failure ()))
      else
        (do
          let prev_priv ← do readReg cur_privilege
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 3 3
            (_get_Mstatus_MPIE (← readReg mstatus)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 7 7 1#1)
          writeReg cur_privilege (← (privLevel_bits_forwards
              ((_get_Mstatus_MPP (← readReg mstatus)), 0#1)))
          writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 12 11
            (privLevel_to_bits
              (← do
                if ((← (currentlyEnabled Ext_U)) : Bool)
                then (pure User)
                else (pure Machine))))
          if ((bne (← readReg cur_privilege) Machine) : Bool)
          then writeReg mstatus (Sail.BitVec.updateSubrange (← readReg mstatus) 17 17 0#1)
          else (pure ())
          if ((hartSupports Ext_Zicfilp) : Bool)
          then (zicfilp_restore_elp_on_xret mRET (← readReg cur_privilege))
          else (pure ())
          (long_csr_write_callback "mstatus" "mstatush" (← readReg mstatus))
          if ((get_config_print_exception ()) : Bool)
          then
            (pure (print_endline
                (HAppend.hAppend "ret-ing from "
                  (HAppend.hAppend (← (privLevel_to_str prev_priv))
                    (HAppend.hAppend " to " (← (privLevel_to_str (← readReg cur_privilege))))))))
          else (pure ())
          (set_next_pc (← (prepare_xret_target Machine)))
          let _ : Unit := (xret_callback true)
          (pure RETIRE_SUCCESS)))

def execute_LPAD (lpl : (BitVec 20)) : SailM ExecutionResult := do
  if ((← (is_landing_pad_expected ())) : Bool)
  then
    (do
      let unaligned_pc ← do (pure ((Sail.BitVec.extractLsb (← (get_arch_pc ())) 1 0) != 0b00#2))
      let label_mismatch ← do
        (pure (((Sail.BitVec.extractLsb (← (rX (Regno 7))) 31 12) != lpl) && (lpl != (zeros
                (n := 20)))))
      if ((unaligned_pc || label_mismatch) : Bool)
      then (trap (make_landing_pad_exception ()))
      else
        (do
          (reset_elp ())
          (pure RETIRE_SUCCESS)))
  else (pure RETIRE_SUCCESS)

/-- Type quantifiers: width : Nat, k_ex609834_ : Bool, width ∈ {1, 2, 4, 8} -/
def execute_LOAD (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) (width : Nat) : SailM ExecutionResult := do
  let offset : xlenbits := (sign_extend (m := 64) imm)
  assert (width ≤b xlen_bytes) "extensions/I/base_insts.sail:289.28-289.29"
  match (← (vmem_read rs1 offset width (Load Data) false false false)) with
  | .Ok data =>
    (do
      (wX_bits rd (extend_value is_unsigned data))
      (pure RETIRE_SUCCESS))
  | .Err e => (pure e)

def execute_JALR (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  (update_elp_state rs1)
  let link_address ← do (get_next_pc ())
  let target ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  match (← (jump_to (BitVec.update target 0 0#1))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_JAL (imm : (BitVec 21)) (rd : regidx) : SailM ExecutionResult := do
  let link_address ← do (get_next_pc ())
  match (← (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))) with
  | .Retire_Success () =>
    (do
      (wX_bits rd link_address)
      (pure (Retire_Success ())))
  | failure => (pure failure)

def execute_ITYPE (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext : xlenbits := (sign_extend (m := 64) imm)
  (wX_bits rd
    (← do
      match op with
      | .ADDI => (pure ((← (rX_bits rs1)) + immext))
      | .SLTI => (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_s (← (rX_bits rs1)) immext))))
      | .SLTIU =>
        (pure (zero_extend (m := 64) (bool_to_bit (zopz0zI_u (← (rX_bits rs1)) immext))))
      | .ANDI => (pure ((← (rX_bits rs1)) &&& immext))
      | .ORI => (pure ((← (rX_bits rs1)) ||| immext))
      | .XORI => (pure ((← (rX_bits rs1)) ^^^ immext))))
  (pure RETIRE_SUCCESS)

def execute_ILLEGAL (_s : (BitVec 32)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_FENCE_TSO (_ : Unit) : SailM ExecutionResult := do
  (sail_barrier Barrier_RISCV_tso)
  (pure RETIRE_SUCCESS)

def execute_FENCE (_fm : (BitVec 4)) (pred : (BitVec 4)) (succ : (BitVec 4)) (_rs : regidx) (_rd : regidx) : SailM ExecutionResult := do
  let fiom ← do (is_fiom_active ())
  let pred := (effective_fence_set pred fiom)
  let succ := (effective_fence_set succ fiom)
  match ((Sail.BitVec.extractLsb pred 1 0), (Sail.BitVec.extractLsb succ 1 0)) with
  | (0b11, 0b11) => (sail_barrier Barrier_RISCV_rw_rw)
  | (0b10, 0b11) => (sail_barrier Barrier_RISCV_r_rw)
  | (0b10, 0b10) => (sail_barrier Barrier_RISCV_r_r)
  | (0b11, 0b01) => (sail_barrier Barrier_RISCV_rw_w)
  | (0b01, 0b01) => (sail_barrier Barrier_RISCV_w_w)
  | (0b01, 0b11) => (sail_barrier Barrier_RISCV_w_rw)
  | (0b11, 0b10) => (sail_barrier Barrier_RISCV_rw_r)
  | (0b10, 0b01) => (sail_barrier Barrier_RISCV_r_w)
  | (0b01, 0b10) => (sail_barrier Barrier_RISCV_w_r)
  | (_, 0b00) => (pure ())
  | (_, _) => (pure ())
  (pure RETIRE_SUCCESS)

def execute_ECALL (_ : Unit) : SailM ExecutionResult := do
  let exc_type ← (( do
    match (← readReg cur_privilege) with
    | .User => (pure (E_U_EnvCall ()))
    | .Supervisor => (pure (E_S_EnvCall ()))
    | .Machine => (pure (E_M_EnvCall ()))
    | .VirtualUser =>
      (internal_error "extensions/I/base_insts.sail" 546 "Hypervisor extension not supported")
    | .VirtualSupervisor =>
      (internal_error "extensions/I/base_insts.sail" 547 "Hypervisor extension not supported") ) :
    SailM ExceptionType )
  let t : sync_exception :=
    { trap := exc_type
      excinfo := none
      ext := none }
  (trap t)

def execute_EBREAK (_ : Unit) : SailM ExecutionResult := do
  (trap (make_sync_exception (E_Breakpoint Brk_Software) (← readReg PC)))

def execute_C_XOR (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (ExecuteAs (RTYPE (rs2, rsd, rsd, XOR)))

def execute_C_SWSP (uimm : (BitVec 6)) (rs2 : regidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b00#2))
  (ExecuteAs (STORE (imm, rs2, sp, 4)))

def execute_C_SW (uimm : (BitVec 5)) (rsc1 : cregidx) (rsc2 : cregidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b00#2))
  let rs1 := (creg2reg_idx rsc1)
  let rs2 := (creg2reg_idx rsc2)
  (ExecuteAs (STORE (imm, rs2, rs1, 4)))

def execute_C_SUBW (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (ExecuteAs (RTYPEW (rs2, rsd, rsd, SUBW)))

def execute_C_SUB (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (ExecuteAs (RTYPE (rs2, rsd, rsd, SUB)))

def execute_C_SRLI (shamt : (BitVec 6)) (rsd : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SRLI)))

def execute_C_SRAI (shamt : (BitVec 6)) (rsd : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SRAI)))

def execute_C_SLLI (shamt : (BitVec 6)) (rsd : regidx) : ExecutionResult :=
  (ExecuteAs (SHIFTIOP (shamt, rsd, rsd, SLLI)))

def execute_C_SDSP (uimm : (BitVec 6)) (rs2 : regidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b000#3))
  (ExecuteAs (STORE (imm, rs2, sp, 8)))

def execute_C_SD (uimm : (BitVec 5)) (rsc1 : cregidx) (rsc2 : cregidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b000#3))
  let rs1 := (creg2reg_idx rsc1)
  let rs2 := (creg2reg_idx rsc2)
  (ExecuteAs (STORE (imm, rs2, rs1, 8)))

def execute_C_OR (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (ExecuteAs (RTYPE (rs2, rsd, rsd, OR)))

def execute_C_NOP (g__169 : (BitVec 6)) : ExecutionResult :=
  RETIRE_SUCCESS

def execute_C_MV (rd : regidx) (rs2 : regidx) : ExecutionResult :=
  (ExecuteAs (RTYPE (rs2, zreg, rd, ADD)))

def execute_C_LWSP (uimm : (BitVec 6)) (rd : regidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b00#2))
  (ExecuteAs (LOAD (imm, sp, rd, false, 4)))

def execute_C_LW (uimm : (BitVec 5)) (rsc : cregidx) (rdc : cregidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b00#2))
  let rd := (creg2reg_idx rdc)
  let rs := (creg2reg_idx rsc)
  (ExecuteAs (LOAD (imm, rs, rd, false, 4)))

def execute_C_LUI (imm : (BitVec 6)) (rd : regidx) : ExecutionResult :=
  let res : (BitVec 20) := (sign_extend (m := 20) imm)
  (ExecuteAs (UTYPE (res, rd, LUI)))

def execute_C_LI (imm : (BitVec 6)) (rd : regidx) : ExecutionResult :=
  let imm : (BitVec 12) := (sign_extend (m := 12) imm)
  (ExecuteAs (ITYPE (imm, zreg, rd, ADDI)))

def execute_C_LDSP (uimm : (BitVec 6)) (rd : regidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b000#3))
  (ExecuteAs (LOAD (imm, sp, rd, false, 8)))

def execute_C_LD (uimm : (BitVec 5)) (rsc : cregidx) (rdc : cregidx) : ExecutionResult :=
  let imm : (BitVec 12) := (zero_extend (m := 12) (uimm +++ 0b000#3))
  let rd := (creg2reg_idx rdc)
  let rs := (creg2reg_idx rsc)
  (ExecuteAs (LOAD (imm, rs, rd, false, 8)))

def execute_C_JR (rs1 : regidx) : ExecutionResult :=
  (ExecuteAs (JALR ((zeros (n := 12)), rs1, zreg)))

def execute_C_JALR (rs1 : regidx) : ExecutionResult :=
  (ExecuteAs (JALR ((zeros (n := 12)), rs1, ra)))

def execute_C_JAL (imm : (BitVec 11)) : ExecutionResult :=
  (ExecuteAs (JAL ((sign_extend (m := 21) (imm +++ 0#1)), ra)))

def execute_C_J (imm : (BitVec 11)) : ExecutionResult :=
  (ExecuteAs (JAL ((sign_extend (m := 21) (imm +++ 0#1)), zreg)))

def execute_C_ILLEGAL (_s : (BitVec 16)) : ExecutionResult :=
  (Illegal_Instruction ())

def execute_C_EBREAK (_ : Unit) : ExecutionResult :=
  (ExecuteAs (EBREAK ()))

def execute_C_BNEZ (imm : (BitVec 8)) (rs : cregidx) : ExecutionResult :=
  (ExecuteAs (BTYPE ((sign_extend (m := 13) (imm +++ 0#1)), zreg, (creg2reg_idx rs), BNE)))

def execute_C_BEQZ (imm : (BitVec 8)) (rs : cregidx) : ExecutionResult :=
  (ExecuteAs (BTYPE ((sign_extend (m := 13) (imm +++ 0#1)), zreg, (creg2reg_idx rs), BEQ)))

def execute_C_ANDI (imm : (BitVec 6)) (rsd : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  (ExecuteAs (ITYPE ((sign_extend (m := 12) imm), rsd, rsd, ANDI)))

def execute_C_AND (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (ExecuteAs (RTYPE (rs2, rsd, rsd, AND)))

def execute_C_ADDW (rsd : cregidx) (rs2 : cregidx) : ExecutionResult :=
  let rsd := (creg2reg_idx rsd)
  let rs2 := (creg2reg_idx rs2)
  (ExecuteAs (RTYPEW (rs2, rsd, rsd, ADDW)))

def execute_C_ADDIW (imm : (BitVec 6)) (rsd : regidx) : ExecutionResult :=
  (ExecuteAs (ADDIW ((sign_extend (m := 12) imm), rsd, rsd)))

def execute_C_ADDI4SPN (rdc : cregidx) (nzimm : (BitVec 8)) : ExecutionResult :=
  let imm : (BitVec 12) := (0b00#2 +++ (nzimm +++ 0b00#2))
  let rd := (creg2reg_idx rdc)
  (ExecuteAs (ITYPE (imm, sp, rd, ADDI)))

def execute_C_ADDI16SP (imm : (BitVec 6)) : ExecutionResult :=
  let imm : (BitVec 12) := (sign_extend (m := 12) (imm +++ 0x0#4))
  (ExecuteAs (ITYPE (imm, sp, sp, ADDI)))

def execute_C_ADDI (imm : (BitVec 6)) (rsd : regidx) : ExecutionResult :=
  let imm : (BitVec 12) := (sign_extend (m := 12) imm)
  (ExecuteAs (ITYPE (imm, rsd, rsd, ADDI)))

def execute_C_ADD (rsd : regidx) (rs2 : regidx) : ExecutionResult :=
  (ExecuteAs (RTYPE (rs2, rsd, rsd, ADD)))

def execute_CSRReg (csr : (BitVec 12)) (rs1 : regidx) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (rs1 == zreg))
  (doCSR csr (← (rX_bits rs1)) rd op access_type)

def execute_CSRImm (csr : (BitVec 12)) (imm : (BitVec 5)) (rd : regidx) (op : csrop) : SailM ExecutionResult := do
  let access_type := (csr_access_type op (rd == zreg) (imm == (zeros (n := 5))))
  (doCSR csr (zero_extend (m := 64) imm) rd op access_type)

def execute_BTYPE (imm : (BitVec 13)) (rs2 : regidx) (rs1 : regidx) (op : bop) : SailM ExecutionResult := do
  let taken ← (( do
    match op with
    | .BEQ => (pure ((← (rX_bits rs1)) == (← (rX_bits rs2))))
    | .BNE => (pure ((← (rX_bits rs1)) != (← (rX_bits rs2))))
    | .BLT => (pure (zopz0zI_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGE => (pure (zopz0zKzJ_s (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BLTU => (pure (zopz0zI_u (← (rX_bits rs1)) (← (rX_bits rs2))))
    | .BGEU => (pure (zopz0zKzJ_u (← (rX_bits rs1)) (← (rX_bits rs2)))) ) : SailM Bool )
  if (taken : Bool)
  then (jump_to ((← readReg PC) + (sign_extend (m := 64) imm)))
  else (pure RETIRE_SUCCESS)

def execute_ADDIW (imm : (BitVec 12)) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let result ← do (pure ((← (rX_bits rs1)) + (sign_extend (m := 64) imm)))
  (wX_bits rd (sign_extend (m := 64) (Sail.BitVec.extractLsb result 31 0)))
  (pure RETIRE_SUCCESS)

def execute (merge_var : instruction) : SailM ExecutionResult := do
  match merge_var with
  | .LPAD lpl => (execute_LPAD lpl)
  | .UTYPE (imm, rd, op) => (execute_UTYPE imm rd op)
  | .JAL (imm, rd) => (execute_JAL imm rd)
  | .BTYPE (imm, rs2, rs1, op) => (execute_BTYPE imm rs2 rs1 op)
  | .ITYPE (imm, rs1, rd, op) => (execute_ITYPE imm rs1 rd op)
  | .SHIFTIOP (shamt, rs1, rd, op) => (execute_SHIFTIOP shamt rs1 rd op)
  | .RTYPE (rs2, rs1, rd, op) => (execute_RTYPE rs2 rs1 rd op)
  | .LOAD (imm, rs1, rd, is_unsigned, width) => (execute_LOAD imm rs1 rd is_unsigned width)
  | .STORE (imm, rs2, rs1, width) => (execute_STORE imm rs2 rs1 width)
  | .ADDIW (imm, rs1, rd) => (execute_ADDIW imm rs1 rd)
  | .RTYPEW (rs2, rs1, rd, op) => (execute_RTYPEW rs2 rs1 rd op)
  | .SHIFTIWOP (shamt, rs1, rd, op) => (execute_SHIFTIWOP shamt rs1 rd op)
  | .FENCE_TSO arg0 => (execute_FENCE_TSO arg0)
  | .FENCE (_fm, pred, succ, _rs, _rd) => (execute_FENCE _fm pred succ _rs _rd)
  | .ECALL arg0 => (execute_ECALL arg0)
  | .MRET arg0 => (execute_MRET arg0)
  | .SRET arg0 => (execute_SRET arg0)
  | .EBREAK arg0 => (execute_EBREAK arg0)
  | .WFI arg0 => (execute_WFI arg0)
  | .SFENCE_VMA (rs1, rs2) => (execute_SFENCE_VMA rs1 rs2)
  | .JALR (imm, rs1, rd) => (execute_JALR imm rs1 rd)
  | .C_NOP g__169 => (pure (execute_C_NOP g__169))
  | .C_ADDI4SPN (rdc, nzimm) => (pure (execute_C_ADDI4SPN rdc nzimm))
  | .C_LW (uimm, rsc, rdc) => (pure (execute_C_LW uimm rsc rdc))
  | .C_LD (uimm, rsc, rdc) => (pure (execute_C_LD uimm rsc rdc))
  | .C_SW (uimm, rsc1, rsc2) => (pure (execute_C_SW uimm rsc1 rsc2))
  | .C_SD (uimm, rsc1, rsc2) => (pure (execute_C_SD uimm rsc1 rsc2))
  | .C_ADDI (imm, rsd) => (pure (execute_C_ADDI imm rsd))
  | .C_JAL imm => (pure (execute_C_JAL imm))
  | .C_ADDIW (imm, rsd) => (pure (execute_C_ADDIW imm rsd))
  | .C_LI (imm, rd) => (pure (execute_C_LI imm rd))
  | .C_ADDI16SP imm => (pure (execute_C_ADDI16SP imm))
  | .C_LUI (imm, rd) => (pure (execute_C_LUI imm rd))
  | .C_SRLI (shamt, rsd) => (pure (execute_C_SRLI shamt rsd))
  | .C_SRAI (shamt, rsd) => (pure (execute_C_SRAI shamt rsd))
  | .C_ANDI (imm, rsd) => (pure (execute_C_ANDI imm rsd))
  | .C_SUB (rsd, rs2) => (pure (execute_C_SUB rsd rs2))
  | .C_XOR (rsd, rs2) => (pure (execute_C_XOR rsd rs2))
  | .C_OR (rsd, rs2) => (pure (execute_C_OR rsd rs2))
  | .C_AND (rsd, rs2) => (pure (execute_C_AND rsd rs2))
  | .C_SUBW (rsd, rs2) => (pure (execute_C_SUBW rsd rs2))
  | .C_ADDW (rsd, rs2) => (pure (execute_C_ADDW rsd rs2))
  | .C_J imm => (pure (execute_C_J imm))
  | .C_BEQZ (imm, rs) => (pure (execute_C_BEQZ imm rs))
  | .C_BNEZ (imm, rs) => (pure (execute_C_BNEZ imm rs))
  | .C_SLLI (shamt, rsd) => (pure (execute_C_SLLI shamt rsd))
  | .C_LWSP (uimm, rd) => (pure (execute_C_LWSP uimm rd))
  | .C_LDSP (uimm, rd) => (pure (execute_C_LDSP uimm rd))
  | .C_SWSP (uimm, rs2) => (pure (execute_C_SWSP uimm rs2))
  | .C_SDSP (uimm, rs2) => (pure (execute_C_SDSP uimm rs2))
  | .C_JR rs1 => (pure (execute_C_JR rs1))
  | .C_JALR rs1 => (pure (execute_C_JALR rs1))
  | .C_MV (rd, rs2) => (pure (execute_C_MV rd rs2))
  | .C_EBREAK arg0 => (pure (execute_C_EBREAK arg0))
  | .C_ADD (rsd, rs2) => (pure (execute_C_ADD rsd rs2))
  | .CSRReg (csr, rs1, rd, op) => (execute_CSRReg csr rs1 rd op)
  | .CSRImm (csr, imm, rd, op) => (execute_CSRImm csr imm rd op)
  | .ZICBOM (arg0, rs1) => (execute_ZICBOM arg0 rs1)
  | .ZICBOZ rs1 => (execute_ZICBOZ rs1)
  | .ILLEGAL _s => (pure (execute_ILLEGAL _s))
  | .C_ILLEGAL _s => (pure (execute_C_ILLEGAL _s))

def assembly_backwards (arg_ : String) : SailM instruction := do
  match arg_ with
  | _ => throw Error.Exit

def assembly_backwards_matches (arg_ : String) : SailM Bool := do
  match arg_ with
  | _ => throw Error.Exit

