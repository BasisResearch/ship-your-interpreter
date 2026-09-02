# io_sfvwrite_r

- kind: io
- consumes/consumed-by: TermResidualsCore.hCallPrint / hCallPrintln / hCallAssertOk (native rows) via rows/ValuePrintContract's three contracts
- note: BOTH arms: unbuffered (real stdout) + buffered (only under __sbprintf synthetic FILE)
- entry: 0x8000de8c (inside `__sfvwrite_r` [0x8000de8c, 0x8000e368))
- containing-fn CFG: 91 blocks, 43 branches, loop-template=no

## Case slice (28 blocks, truncated closure)

- Block(0x8000de8c..0x8000de90 beqz kind=br succs=['0x8000e0cc', '0x8000de94'])
- Block(0x8000e0cc..0x8000e0d0 ret kind=ret succs=[])
- Block(0x8000de94..0x8000debc beqz kind=br succs=['0x8000df68', '0x8000dec0'])
- Block(0x8000df68..0x8000df70 jal kind=jal succs=['0x8000df74'])
- Block(0x8000dec0..0x8000dec4 beqz kind=br succs=['0x8000df68', '0x8000dec8'])
- Block(0x8000df74..0x8000df74 bnez kind=br succs=['0x8000e20c', '0x8000df78'])
- Block(0x8000dec8..0x8000dee0 beqz kind=br succs=['0x8000df98', '0x8000dee4'])
- Block(0x8000e20c..0x8000e210 j kind=j succs=['0x8000df50'])
- Block(0x8000df78..0x8000df94 bnez kind=br succs=['0x8000dee4', '0x8000df98'])
- Block(0x8000df98..0x8000dfa8 bnez kind=br succs=['0x8000e0d4', '0x8000dfac'])
- Block(0x8000dee4..0x8000def0 fall kind=fallthrough succs=['0x8000def4'])
- Block(0x8000df50..0x8000df64 ret kind=ret succs=[])
- Block(0x8000e0d4..0x8000e0e4 beqz kind=br succs=['0x8000e164', '0x8000e0e8'])
- Block(0x8000dfac..0x8000dfbc fall kind=fallthrough succs=['0x8000dfc0'])
- Block(0x8000def4..0x8000defc beqz kind=br succs=['0x8000e0bc', '0x8000df00'])
- Block(0x8000e164..0x8000e170 beqz kind=br succs=['0x8000e164', '0x8000e174'])
- Block(0x8000e0e8..0x8000e0e8 beqz kind=br succs=['0x8000e178', '0x8000e0ec'])
- Block(0x8000dfc0..0x8000dfc0 beqz kind=br succs=['0x8000e0ac', '0x8000dfc4'])
- Block(0x8000e0bc..0x8000e0c8 j kind=j succs=['0x8000def4'])
- Block(0x8000df00..0x8000df04 bgeu kind=br succs=['0x8000df10', '0x8000df08'])
- Block(0x8000e174..0x8000e174 fall kind=fallthrough succs=['0x8000e178'])
- Block(0x8000e178..0x8000e184 jal kind=jal succs=['0x8000e188'])
- Block(0x8000e0ec..0x8000e0f0 bgeu kind=br succs=['0x8000e0f8', '0x8000e0f4'])
- Block(0x8000e0ac..0x8000e0b8 j kind=j succs=['0x8000dfc0'])
- Block(0x8000dfc4..0x8000dfd0 beqz kind=br succs=['0x8000e214', '0x8000dfd4'])
- Block(0x8000df10..0x8000df1c jalr kind=jalrcall succs=['0x8000df20'])
- Block(0x8000df08..0x8000df0c fall kind=fallthrough succs=['0x8000df10'])
- Block(0x8000e188..0x8000e188 beqz kind=br succs=['0x8000e32c', '0x8000e18c'])

## Terminator/loop classification

- terminators on slice: br, fallthrough, j, jal, jalrcall, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `__swsetup_r` → NONE
- `memchr` → NONE

## Register/memory outcome sketch

- regs written on slice: a5, a0, a3, sp, s0, s5, s4, a1, s1, s6, s3, s2, ra, s7, s8, s9, a4, a2
- loads: 20, stores: 15

## Disasm slice

```
  -- block 0x8000de8c [br]
  8000de8c: ld a5,16(a2)
  8000de90: beqz a5,8000e0cc <__sfvwrite_r+0x240>
  -- block 0x8000e0cc [ret]
  8000e0cc: li a0,0
  8000e0d0: ret 
  -- block 0x8000de94 [br]
  8000de94: lh a3,16(a1)
  8000de98: addi sp,sp,-96
  8000de9c: sd s0,80(sp)
  8000dea0: sd s4,48(sp)
  8000dea4: sd s5,40(sp)
  8000dea8: sd ra,88(sp)
  8000deac: andi a5,a3,8
  8000deb0: mv s0,a1
  8000deb4: mv s5,a0
  8000deb8: mv s4,a2
  8000debc: beqz a5,8000df68 <__sfvwrite_r+0xdc>
  -- block 0x8000df68 [jal]
  8000df68: mv a1,s0
  8000df6c: mv a0,s5
  8000df70: jal 8000f230 <__swsetup_r>
  -- block 0x8000dec0 [br]
  8000dec0: ld a5,24(a1)
  8000dec4: beqz a5,8000df68 <__sfvwrite_r+0xdc>
  -- block 0x8000df74 [br]
  8000df74: bnez a0,8000e20c <__sfvwrite_r+0x380>
  -- block 0x8000dec8 [br]
  8000dec8: sd s1,72(sp)
  8000decc: sd s2,64(sp)
  8000ded0: sd s3,56(sp)
  8000ded4: sd s6,32(sp)
  8000ded8: andi a5,a3,2
  8000dedc: ld s1,0(s4)
  8000dee0: beqz a5,8000df98 <__sfvwrite_r+0x10c>
  -- block 0x8000e20c [j]
  8000e20c: li a0,-1
  8000e210: j 8000df50 <__sfvwrite_r+0xc4>
  -- block 0x8000df78 [br]
  8000df78: lh a3,16(s0)
  8000df7c: sd s1,72(sp)
  8000df80: sd s2,64(sp)
  8000df84: sd s3,56(sp)
  8000df88: sd s6,32(sp)
  8000df8c: andi a5,a3,2
  8000df90: ld s1,0(s4)
  8000df94: bnez a5,8000dee4 <__sfvwrite_r+0x58>
  -- block 0x8000df98 [br]
  8000df98: sd s7,24(sp)
  8000df9c: sd s8,16(sp)
  8000dfa0: sd s9,8(sp)
  8000dfa4: andi a5,a3,1
  8000dfa8: bnez a5,8000e0d4 <__sfvwrite_r+0x248>
  -- block 0x8000dee4 [fallthrough] LOOP-HEAD
  8000dee4: lui s6,0x80000
  8000dee8: xori s6,s6,-1024
  8000deec: li s3,0
  8000def0: li s2,0
  -- block 0x8000df50 [ret] LOOP-HEAD
  8000df50: ld ra,88(sp)
  8000df54: ld s0,80(sp)
  8000df58: ld s4,48(sp)
  8000df5c: ld s5,40(sp)
  8000df60: addi sp,sp,96
  8000df64: ret 
  -- block 0x8000e0d4 [br]
  8000e0d4: li s7,0
  8000e0d8: li s8,0
  8000e0dc: li a0,0
  8000e0e0: li s9,0
  8000e0e4: beqz s7,8000e164 <__sfvwrite_r+0x2d8>
  -- block 0x8000dfac [fallthrough]
  8000dfac: ld a5,0(s0)
  8000dfb0: lui a4,0x80000
  8000dfb4: not s8,a4
  8000dfb8: li s6,0
  8000dfbc: li s3,0
  -- block 0x8000def4 [br] LOOP-HEAD
  8000def4: mv a2,s3
  8000def8: mv a0,s5
  8000defc: beqz s2,8000e0bc <__sfvwrite_r+0x230>
  -- block 0x8000e164 [br] LOOP-HEAD
  8000e164: ld s7,8(s1)
  8000e168: mv a5,s1
  8000e16c: addi s1,s1,16
  8000e170: beqz s7,8000e164 <__sfvwrite_r+0x2d8>
  -- block 0x8000e0e8 [br] LOOP-HEAD
  8000e0e8: beqz a0,8000e178 <__sfvwrite_r+0x2ec>
  -- block 0x8000dfc0 [br] LOOP-HEAD
  8000dfc0: beqz s3,8000e0ac <__sfvwrite_r+0x220>
  -- block 0x8000e0bc [j]
  8000e0bc: ld s3,0(s1)
  8000e0c0: ld s2,8(s1)
  8000e0c4: addi s1,s1,16
  8000e0c8: j 8000def4 <__sfvwrite_r+0x68>
  -- block 0x8000df00 [br]
  8000df00: mv a3,s2
  8000df04: bgeu s6,s2,8000df10 <__sfvwrite_r+0x84>
  -- block 0x8000e174 [fallthrough]
  8000e174: ld s9,0(a5)
  -- block 0x8000e178 [jal]
  8000e178: mv a2,s7
  8000e17c: li a1,10
  8000e180: mv a0,s9
  8000e184: jal 8000f394 <memchr>
  -- block 0x8000e0ec [br] LOOP-HEAD
  8000e0ec: mv s3,s8
  8000e0f0: bgeu s7,s8,8000e0f8 <__sfvwrite_r+0x26c>
  -- block 0x8000e0ac [j]
  8000e0ac: ld s6,0(s1)
  8000e0b0: ld s3,8(s1)
  8000e0b4: addi s1,s1,16
  8000e0b8: j 8000dfc0 <__sfvwrite_r+0x134>
  -- block 0x8000dfc4 [br]
  8000dfc4: andi a4,a3,512
  … (disasm capped at 90 lines)
```
