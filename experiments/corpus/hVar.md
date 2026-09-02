# hVar

- kind: field
- consumes/consumed-by: TermResidualsCore.hVar
- note: var arm; env_get call bridge (env_get_found_uncond'') | skeleton: `hVar`/`eval_var_row`.  Supplier: `VarLeafResid` — carries the `env_get_found` caller-linkage oracle (dischargeable from `env_get_found_uncond''` once the eval-var-arm call bridge lands; the `TermCallees.envGet` contract
- entry: 0x80003434 (inside `eval_expr` [0x80003164, 0x80003fe0))
- containing-fn CFG: 185 blocks, 48 branches, loop-template=no

## Case slice (5 blocks)

- Block(0x80003434..0x80003440 jal kind=jal succs=['0x80003444'])
- Block(0x80003444..0x80003444 beqz kind=br succs=['0x80003f80', '0x80003448'])
- Block(0x80003f80..0x80003fac jal kind=jal succs=['0x80003fb0'])
- Block(0x80003448..0x80003478 ret kind=ret succs=[])
- Block(0x80003fb0..0x80003fdc jal kind=jal succs=['0x80003fe0'])

## Terminator/loop classification

- terminators on slice: br, jal, ret
- back-edge/loop on slice: YES

## Calls (landed-summary status)

- `env_get` → LANDED (env_get_scan_spec, env_get_found_spec, env_get_scan_spec', envGetContract_of_storeRepr)
- `runtime_error` → LANDED (runtime_error_spec)

## Register/memory outcome sketch

- regs written on slice: a1, a0, a2, a3, a4, a5, ra, s0, s2, s1, sp
- loads: 11, stores: 13

## Disasm slice

```
  -- block 0x80003434 [jal]
  80003434: ld a1,8(a2)
  80003438: mv a0,a3
  8000343c: addi a2,sp,240
  80003440: jal 80002c10 <env_get>
  -- block 0x80003444 [br]
  80003444: beqz a0,80003f80 <eval_expr+0xe1c>
  -- block 0x80003f80 [jal]
  80003f80: ld a3,8(s0)
  80003f84: lw a1,4(s0)
  80003f88: mv a0,s2
  80003f8c: li a4,0
  80003f90: auipc a2,0x15
  80003f94: addi a2,a2,1016
  80003f98: sd s3,1048(sp)
  80003f9c: sd s4,1040(sp)
  80003fa0: sd s5,1032(sp)
  80003fa4: sd s6,1024(sp)
  80003fa8: sd s7,1016(sp)
  80003fac: jal 80002da8 <runtime_error>
  -- block 0x80003448 [ret] LOOP-HEAD
  80003448: ld a3,240(sp)
  8000344c: ld a4,248(sp)
  80003450: ld a5,256(sp)
  80003454: ld ra,1080(sp)
  80003458: ld s0,1072(sp)
  8000345c: sd a3,0(s1)
  80003460: sd a4,8(s1)
  80003464: sd a5,16(s1)
  80003468: ld s2,1056(sp)
  8000346c: mv a0,s1
  80003470: ld s1,1064(sp)
  80003474: addi sp,sp,1088
  80003478: ret 
  -- block 0x80003fb0 [jal]
  80003fb0: lw a1,4(s0)
  80003fb4: mv a0,s2
  80003fb8: li a4,0
  80003fbc: li a3,0
  80003fc0: auipc a2,0x15
  80003fc4: addi a2,a2,1200
  80003fc8: sd s3,1048(sp)
  80003fcc: sd s4,1040(sp)
  80003fd0: sd s5,1032(sp)
  80003fd4: sd s6,1024(sp)
  80003fd8: sd s7,1016(sp)
  80003fdc: jal 80002da8 <runtime_error>
```
