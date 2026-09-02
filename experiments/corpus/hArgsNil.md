# hArgsNil

- kind: field
- consumes/consumed-by: TermResidualsCore.hArgsNil
- note: args loop seg-identity evalArgsLoopPC→evalArgsContPC | skeleton: `hArgsNil`/`eval_argsNil_row`.  Supplier: `ArgsNilResid` seg-identity at `evalArgsLoopPC`→`evalArgsContPC`.
- entry: 0x800031dc (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (28 blocks, truncated closure)

- Block(0x800031dc..0x80003220 jal kind=jal succs=['0x80003224'])
- Block(0x80003224..0x80003250 bne kind=br succs=['0x800031dc', '0x80003254'])
- Block(0x80003254..0x8000327c beq kind=br succs=['0x800039e0', '0x80003280'])
- Block(0x800039e0..0x800039f4 jalr kind=jalrcall succs=['0x800039f8'])
- Block(0x80003280..0x80003284 bne kind=br succs=['0x80003da4', '0x80003288'])
- Block(0x800039f8..0x800039fc j kind=j succs=['0x800033ec'])
- Block(0x80003da4..0x80003dcc jal kind=jal succs=['0x80003dd0'])
- Block(0x80003288..0x80003298 bne kind=br succs=['0x80003d60', '0x8000329c'])
- Block(0x800033ec..0x80003404 ret kind=ret succs=[])
- Block(0x80003dd0..0x80003de8 jal kind=jal succs=['0x80003dec'])
- Block(0x80003d60..0x80003d70 beqz kind=br succs=['0x80003dec', '0x80003d74'])
- Block(0x8000329c..0x800032b0 blt kind=br succs=['0x80003ca4', '0x800032b4'])
- Block(0x80003dec..0x80003df4 j kind=j succs=['0x80003d74'])
- Block(0x80003d74..0x80003d84 jal kind=jal succs=['0x80003d88'])
- Block(0x80003ca4..0x80003cc4 jal kind=jal succs=['0x80003cc8'])
- Block(0x800032b4..0x800032bc jal kind=jal succs=['0x800032c0'])
- Block(0x80003d88..0x80003da0 jal kind=jal succs=['0x80003da4'])
- Block(0x80003cc8..0x80003ce8 jal kind=jal succs=['0x80003cec'])
- Block(0x800032c0..0x800032c8 blez kind=br succs=['0x80003324', '0x800032cc'])
- Block(0x80003cec..0x80003d14 jal kind=jal succs=['0x80003d18'])
- Block(0x80003324..0x80003328 jal kind=jal succs=['0x8000332c'])
- Block(0x800032cc..0x800032d8 fall kind=fallthrough succs=['0x800032dc'])
- Block(0x80003d18..0x80003d34 fall kind=fallthrough succs=['0x80003d38'])
- Block(0x8000332c..0x80003338 bgtz kind=br succs=['0x80003354', '0x8000333c'])
- Block(0x800032dc..0x80003310 jal kind=jal succs=['0x80003314'])
- Block(0x80003d38..0x80003d3c jal kind=jal succs=['0x80003d40'])
- Block(0x80003354..0x80003374 jal kind=jal succs=['0x80003378'])
- Block(0x8000333c..0x8000333c j kind=j succs=['0x80003954'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, jalrcall, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `eval_expr` → NONE
- `value_kind_name` → NONE
- `runtime_error` → LANDED (runtime_error_spec)
- `snprintf` → LANDED (SnprintfContract, snprintf_lld_spec, snprintf_lld_spec', snprintfPreCall_spec, snprintf_lld_nn_spec, SnprintfFrameContract)
- `env_new` → LANDED (env_new_spec, callClosureEnvNewRetFoldRow, CallClosureEnvNewRetFoldPost, callClosureEnvNewRetBypassRow)
- `value_null` → LANDED (value_null_spec, value_null_spec_full)
- `env_define` → LANDED (env_define_append_spec)
- `exec_stmt` → NONE

## Register/memory outcome sketch

- regs written on slice: a2, a1, a4, a5, a0, a6, a3, s7, s5, ra, s0, s2, s1, sp, s3, s6
- loads: 35, stores: 48

## Disasm slice

```
  -- block 0x800031dc [jal] LOOP-HEAD
  800031dc: ld a2,16(s0)
  800031e0: sext.w a1,a6
  800031e4: slli a4,a6,0x3
  800031e8: add a2,a2,a4
  800031ec: slli a4,a1,0x1
  800031f0: add a4,a4,a1
  800031f4: ld a2,0(a2)
  800031f8: slli a4,a4,0x3
  800031fc: sd a5,24(sp)
  80003200: addi a5,a4,976
  80003204: addi a4,sp,32
  80003208: add a4,a5,a4
  8000320c: mv a1,s2
  80003210: addi a0,sp,64
  80003214: sd a6,16(sp)
  80003218: sd a3,8(sp)
  8000321c: sd a4,0(sp)
  80003220: jal 80003164 <eval_expr>
  -- block 0x80003224 [br]
  80003224: ld a2,64(sp)
  80003228: ld a4,0(sp)
  8000322c: ld a6,16(sp)
  80003230: ld a5,24(sp)
  80003234: sd a2,-768(a4)
  80003238: ld a2,72(sp)
  8000323c: addi a6,a6,1
  80003240: ld a3,8(sp)
  80003244: sd a2,-760(a4)
  80003248: ld a2,80(sp)
  8000324c: sd a2,-752(a4)
  80003250: bne a6,a5,800031dc <eval_expr+0x78>
  -- block 0x80003254 [br]
  80003254: ld a4,96(sp)
  80003258: ld a3,104(sp)
  8000325c: ld a6,112(sp)
  80003260: lw a1,4(s0)
  80003264: sd a4,120(sp)
  80003268: lw a4,96(sp)
  8000326c: sd a3,128(sp)
  80003270: sd a6,136(sp)
  80003274: li a2,5
  80003278: mv s7,a1
  8000327c: beq a4,a2,800039e0 <eval_expr+0x87c>
  -- block 0x800039e0 [jalrcall]
  800039e0: mv a4,a1
  800039e4: mv a2,a5
  800039e8: mv a1,s2
  800039ec: addi a3,sp,240
  800039f0: mv a0,s1
  800039f4: jalr a6
  -- block 0x80003280 [br]
  80003280: li a2,4
  80003284: bne a4,a2,80003da4 <eval_expr+0xc40>
  -- block 0x800039f8 [j]
  800039f8: ld s7,1016(sp)
  800039fc: j 800033ec <eval_expr+0x288>
  -- block 0x80003da4 [jal]
  80003da4: sw a4,120(sp)
  80003da8: ld a5,120(sp)
  80003dac: addi a0,sp,64
  80003db0: sd a3,72(sp)
  80003db4: sd s3,1048(sp)
  80003db8: sd s4,1040(sp)
  80003dbc: sd s5,1032(sp)
  80003dc0: sd s6,1024(sp)
  80003dc4: sd a6,80(sp)
  80003dc8: sd a5,64(sp)
  80003dcc: jal 800029c8 <value_kind_name>
  -- block 0x80003288 [br]
  80003288: ld a4,0(a3)
  8000328c: sd s5,1032(sp)
  80003290: mv s5,a4
  80003294: lw a4,24(a4)
  80003298: bne a5,a4,80003d60 <eval_expr+0xbfc>
  -- block 0x800033ec [ret] LOOP-HEAD
  800033ec: ld ra,1080(sp)
  800033f0: ld s0,1072(sp)
  800033f4: ld s2,1056(sp)
  800033f8: mv a0,s1
  800033fc: ld s1,1064(sp)
  80003400: addi sp,sp,1088
  80003404: ret 
  -- block 0x80003dd0 [jal]
  80003dd0: mv a3,a0
  80003dd4: mv a1,s7
  80003dd8: mv a0,s2
  80003ddc: li a4,0
  80003de0: auipc a2,0x15
  80003de4: addi a2,a2,1712
  80003de8: jal 80002da8 <runtime_error>
  -- block 0x80003d60 [br]
  80003d60: ld a3,8(s5)
  80003d64: sd s3,1048(sp)
  80003d68: sd s4,1040(sp)
  80003d6c: sd s6,1024(sp)
  80003d70: beqz a3,80003dec <eval_expr+0xc88>
  -- block 0x8000329c [br]
  8000329c: lw a4,8(s2)
  800032a0: li a2,1000
  800032a4: addiw a4,a4,1
  800032a8: sw a4,8(s2)
  … (disasm capped at 90 lines)
```
