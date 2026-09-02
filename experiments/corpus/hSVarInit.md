# hSVarInit

- kind: field
- consumes/consumed-by: TermResidualsCore.hSVarInit
- note: exec var-decl init arm (env_define glue) | skeleton: `hSVarInit`/`exec_varInit_row`.  Supplier: `VarInitResid` = `ExecVarInitGeom` (`hGlue` threads the `env_define` callee oracle, `TermCallees.envDefine`).
- entry: 0x800040d8 (inside `exec_stmt` [0x80003fe0, 0x80004308))
- containing-fn CFG: 54 blocks, 17 branches, loop-template=no

## Case slice (7 blocks)

- Block(0x800040d8..0x800040dc beqz kind=br succs=['0x800042fc', '0x800040e0'])
- Block(0x800042fc..0x80004300 jal kind=jal succs=['0x80004304'])
- Block(0x800040e0..0x800040ec jal kind=jal succs=['0x800040f0'])
- Block(0x80004304..0x80004304 j kind=j succs=['0x800040f0'])
- Block(0x800040f0..0x80004114 jal kind=jal succs=['0x80004118'])
- Block(0x80004118..0x8000411c j kind=j succs=['0x8000409c'])
- Block(0x8000409c..0x800040b4 ret kind=ret succs=[])

## Terminator/loop classification

- terminators on slice: br, j, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `value_null` → LANDED (value_null_spec, value_null_spec_full)
- `eval_expr` → NONE
- `env_define` → LANDED (env_define_append_spec)

## Register/memory outcome sketch

- regs written on slice: a2, a0, a1, a3, a4, a5, ra, s0, s1, s2, s3, sp
- loads: 10, stores: 3

## Disasm slice

```
  -- block 0x800040d8 [br]
  800040d8: ld a2,16(s0)
  800040dc: beqz a2,800042fc <exec_stmt+0x31c>
  -- block 0x800042fc [jal]
  800042fc: addi a0,sp,104
  80004300: jal 800027ec <value_null>
  -- block 0x800040e0 [jal]
  800040e0: mv a1,s1
  800040e4: mv a3,s3
  800040e8: addi a0,sp,104
  800040ec: jal 80003164 <eval_expr>
  -- block 0x80004304 [j]
  80004304: j 800040f0 <exec_stmt+0x110>
  -- block 0x800040f0 [jal] LOOP-HEAD
  800040f0: ld a1,8(s0)
  800040f4: ld a3,104(sp)
  800040f8: ld a4,112(sp)
  800040fc: ld a5,120(sp)
  80004100: mv a0,s3
  80004104: addi a2,sp,16
  80004108: sd a3,16(sp)
  8000410c: sd a4,24(sp)
  80004110: sd a5,32(sp)
  80004114: jal 80002a5c <env_define>
  -- block 0x80004118 [j]
  80004118: li a0,0
  8000411c: j 8000409c <exec_stmt+0xbc>
  -- block 0x8000409c [ret] LOOP-HEAD
  8000409c: ld ra,168(sp)
  800040a0: ld s0,160(sp)
  800040a4: ld s1,152(sp)
  800040a8: ld s2,144(sp)
  800040ac: ld s3,136(sp)
  800040b0: addi sp,sp,176
  800040b4: ret 
```
