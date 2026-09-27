import VsaIris.Vsa.AllocRun

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail

namespace Vsa.Sim

def axT_80006abc : List BBlock := [⟨[], some (⟨0x80006abc#64, 0xfee598e3#32, 0xe3#8, 0x98#8, 0xe5#8, 0xfe#8, .br bop.BNE true, 11, 14, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006abc : List BBlock := [⟨[], some (⟨0x80006abc#64, 0xfee598e3#32, 0xe3#8, 0x98#8, 0xe5#8, 0xfe#8, .br bop.BNE false, 11, 14, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006ac0 : List BBlock := [{ body := [mkLine 0x80006ac0#64 0x00868713#32], term := none }]
def ax_80006ac4 : List BBlock := [{ body := [mkLine 0x80006ac4#64 0x01c705b3#32], term := none }]
def ax_80006ac8 : List BBlock := [{ body := [mkLine 0x80006ac8#64 0x00f707b3#32], term := none }]
def ax_80006acc : List BBlock := [{ body := [mkLine 0x80006acc#64 0x00767613#32], term := none }]
def ax_80006ad0 : List BBlock := [⟨[], some (⟨0x80006ad0#64, 0xf2dff06f#32, 0x6f#8, 0xf0#8, 0xdf#8, 0xf2#8, .j, 0, 0, 0x0#13, 0x1fff2c#21, 0#12⟩ : TInstr)⟩]
def ax_80006ae0 : List BBlock := [⟨[], some (⟨0x80006ae0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006ae4 : List BBlock := [{ body := [mkLine 0x80006ae4#64 0x00068613#32], term := none }]
def ax_80006ae8 : List BBlock := [⟨[], some (⟨0x80006ae8#64, 0xf15ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf1#8, .j, 0, 0, 0x0#13, 0x1fff14#21, 0#12⟩ : TInstr)⟩]
def ax_80006bc8 : List BBlock := [{ body := [mkLine 0x80006bc8#64 0x00a5c7b3#32], term := none }]
def ax_80006bcc : List BBlock := [{ body := [mkLine 0x80006bcc#64 0x0077f793#32], term := none }]
def ax_80006bd0 : List BBlock := [{ body := [mkLine 0x80006bd0#64 0x00c508b3#32], term := none }]
def axT_80006bd4 : List BBlock := [⟨[], some (⟨0x80006bd4#64, 0x06079663#32, 0x63#8, 0x96#8, 0x07#8, 0x06#8, .br bop.BNE true, 15, 0, 0x6c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006bd4 : List BBlock := [⟨[], some (⟨0x80006bd4#64, 0x06079663#32, 0x63#8, 0x96#8, 0x07#8, 0x06#8, .br bop.BNE false, 15, 0, 0x6c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axT_80006bdc : List BBlock := [⟨[], some (⟨0x80006bdc#64, 0x06061263#32, 0x63#8, 0x12#8, 0x06#8, 0x06#8, .br bop.BNE true, 12, 0, 0x64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006bdc : List BBlock := [⟨[], some (⟨0x80006bdc#64, 0x06061263#32, 0x63#8, 0x12#8, 0x06#8, 0x06#8, .br bop.BNE false, 12, 0, 0x64#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006be0 : List BBlock := [{ body := [mkLine 0x80006be0#64 0x00757793#32], term := none }]
def ax_80006be4 : List BBlock := [{ body := [mkLine 0x80006be4#64 0x00050713#32], term := none }]
def axT_80006be8 : List BBlock := [⟨[], some (⟨0x80006be8#64, 0x0c079a63#32, 0x63#8, 0x9a#8, 0x07#8, 0x0c#8, .br bop.BNE true, 15, 0, 0xd4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006be8 : List BBlock := [⟨[], some (⟨0x80006be8#64, 0x0c079a63#32, 0x63#8, 0x9a#8, 0x07#8, 0x0c#8, .br bop.BNE false, 15, 0, 0xd4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006bec : List BBlock := [{ body := [mkLine 0x80006bec#64 0xff88f613#32], term := none }]
def ax_80006bf0 : List BBlock := [{ body := [mkLine 0x80006bf0#64 0x40e606b3#32], term := none }]
def ax_80006bf4 : List BBlock := [{ body := [mkLine 0x80006bf4#64 0x04000793#32], term := none }]
def axT_80006bf8 : List BBlock := [⟨[], some (⟨0x80006bf8#64, 0x06d7c463#32, 0x63#8, 0xc4#8, 0xd7#8, 0x06#8, .br bop.BLT true, 15, 13, 0x68#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006bf8 : List BBlock := [⟨[], some (⟨0x80006bf8#64, 0x06d7c463#32, 0x63#8, 0xc4#8, 0xd7#8, 0x06#8, .br bop.BLT false, 15, 13, 0x68#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006bfc : List BBlock := [{ body := [mkLine 0x80006bfc#64 0x00058693#32], term := none }]
def ax_80006c00 : List BBlock := [{ body := [mkLine 0x80006c00#64 0x00070793#32], term := none }]
def axT_80006c04 : List BBlock := [⟨[], some (⟨0x80006c04#64, 0x02c77a63#32, 0x63#8, 0x7a#8, 0xc7#8, 0x02#8, .br bop.BGEU true, 14, 12, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006c04 : List BBlock := [⟨[], some (⟨0x80006c04#64, 0x02c77a63#32, 0x63#8, 0x7a#8, 0xc7#8, 0x02#8, .br bop.BGEU false, 14, 12, 0x34#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c08 : List BBlock := [{ body := [mkLine 0x80006c08#64 0x0006b803#32], term := none }]
def ax_80006c0c : List BBlock := [{ body := [mkLine 0x80006c0c#64 0x00878793#32], term := none }]
def ax_80006c10 : List BBlock := [{ body := [mkLine 0x80006c10#64 0x00868693#32], term := none }]
def ax_80006c14 : List BBlock := [{ body := [mkLine 0x80006c14#64 0xff07bc23#32], term := none }]
def axT_80006c18 : List BBlock := [⟨[], some (⟨0x80006c18#64, 0xfec7e8e3#32, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, .br bop.BLTU true, 15, 12, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006c18 : List BBlock := [⟨[], some (⟨0x80006c18#64, 0xfec7e8e3#32, 0xe3#8, 0xe8#8, 0xc7#8, 0xfe#8, .br bop.BLTU false, 15, 12, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c1c : List BBlock := [{ body := [mkLine 0x80006c1c#64 0xfff60613#32], term := none }]
def ax_80006c20 : List BBlock := [{ body := [mkLine 0x80006c20#64 0x40e60633#32], term := none }]
def ax_80006c24 : List BBlock := [{ body := [mkLine 0x80006c24#64 0xff867613#32], term := none }]
def ax_80006c28 : List BBlock := [{ body := [mkLine 0x80006c28#64 0x00858593#32], term := none }]
def ax_80006c2c : List BBlock := [{ body := [mkLine 0x80006c2c#64 0x00870713#32], term := none }]
def ax_80006c30 : List BBlock := [{ body := [mkLine 0x80006c30#64 0x00c585b3#32], term := none }]
def ax_80006c34 : List BBlock := [{ body := [mkLine 0x80006c34#64 0x00c70733#32], term := none }]
def axT_80006c38 : List BBlock := [⟨[], some (⟨0x80006c38#64, 0x01176863#32, 0x63#8, 0x68#8, 0x17#8, 0x01#8, .br bop.BLTU true, 14, 17, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006c38 : List BBlock := [⟨[], some (⟨0x80006c38#64, 0x01176863#32, 0x63#8, 0x68#8, 0x17#8, 0x01#8, .br bop.BLTU false, 14, 17, 0x10#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c3c : List BBlock := [⟨[], some (⟨0x80006c3c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c40 : List BBlock := [{ body := [mkLine 0x80006c40#64 0x00050713#32], term := none }]
def axT_80006c44 : List BBlock := [⟨[], some (⟨0x80006c44#64, 0xff157ce3#32, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, .br bop.BGEU true, 10, 17, 0x1ff8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006c44 : List BBlock := [⟨[], some (⟨0x80006c44#64, 0xff157ce3#32, 0xe3#8, 0x7c#8, 0x15#8, 0xff#8, .br bop.BGEU false, 10, 17, 0x1ff8#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c48 : List BBlock := [{ body := [mkLine 0x80006c48#64 0x0005c783#32], term := none }]
def ax_80006c4c : List BBlock := [{ body := [mkLine 0x80006c4c#64 0x00170713#32], term := none }]
def ax_80006c50 : List BBlock := [{ body := [mkLine 0x80006c50#64 0x00158593#32], term := none }]
def ax_80006c54 : List BBlock := [{ body := [mkLine 0x80006c54#64 0xfef70fa3#32], term := none }]
def axT_80006c58 : List BBlock := [⟨[], some (⟨0x80006c58#64, 0xfee898e3#32, 0xe3#8, 0x98#8, 0xe8#8, 0xfe#8, .br bop.BNE true, 17, 14, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006c58 : List BBlock := [⟨[], some (⟨0x80006c58#64, 0xfee898e3#32, 0xe3#8, 0x98#8, 0xe8#8, 0xfe#8, .br bop.BNE false, 17, 14, 0x1ff0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c5c : List BBlock := [⟨[], some (⟨0x80006c5c#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006c60 : List BBlock := [{ body := [mkLine 0x80006c60#64 0x0005b683#32], term := none }]
def ax_80006c64 : List BBlock := [{ body := [mkLine 0x80006c64#64 0x0085b283#32], term := none }]
def ax_80006c68 : List BBlock := [{ body := [mkLine 0x80006c68#64 0x0105bf83#32], term := none }]
def ax_80006c6c : List BBlock := [{ body := [mkLine 0x80006c6c#64 0x0185bf03#32], term := none }]
def ax_80006c70 : List BBlock := [{ body := [mkLine 0x80006c70#64 0x0205be83#32], term := none }]
def ax_80006c74 : List BBlock := [{ body := [mkLine 0x80006c74#64 0x0285be03#32], term := none }]
def ax_80006c78 : List BBlock := [{ body := [mkLine 0x80006c78#64 0x0305b303#32], term := none }]
def ax_80006c7c : List BBlock := [{ body := [mkLine 0x80006c7c#64 0x0385b803#32], term := none }]
def ax_80006c80 : List BBlock := [{ body := [mkLine 0x80006c80#64 0x00d73023#32], term := none }]
def ax_80006c84 : List BBlock := [{ body := [mkLine 0x80006c84#64 0x0405b683#32], term := none }]
def ax_80006c88 : List BBlock := [{ body := [mkLine 0x80006c88#64 0x04870713#32], term := none }]
def ax_80006c8c : List BBlock := [{ body := [mkLine 0x80006c8c#64 0xfc573023#32], term := none }]
def ax_80006c90 : List BBlock := [{ body := [mkLine 0x80006c90#64 0xfed73c23#32], term := none }]
def ax_80006c94 : List BBlock := [{ body := [mkLine 0x80006c94#64 0xfdf73423#32], term := none }]
def ax_80006c98 : List BBlock := [{ body := [mkLine 0x80006c98#64 0x40e606b3#32], term := none }]
def ax_80006c9c : List BBlock := [{ body := [mkLine 0x80006c9c#64 0xfde73823#32], term := none }]
def ax_80006ca0 : List BBlock := [{ body := [mkLine 0x80006ca0#64 0xfdd73c23#32], term := none }]
def ax_80006ca4 : List BBlock := [{ body := [mkLine 0x80006ca4#64 0xffc73023#32], term := none }]
def ax_80006ca8 : List BBlock := [{ body := [mkLine 0x80006ca8#64 0xfe673423#32], term := none }]
def ax_80006cac : List BBlock := [{ body := [mkLine 0x80006cac#64 0xff073823#32], term := none }]
def ax_80006cb0 : List BBlock := [{ body := [mkLine 0x80006cb0#64 0x04858593#32], term := none }]
def axT_80006cb4 : List BBlock := [⟨[], some (⟨0x80006cb4#64, 0xfad7c6e3#32, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, .br bop.BLT true, 15, 13, 0x1fac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006cb4 : List BBlock := [⟨[], some (⟨0x80006cb4#64, 0xfad7c6e3#32, 0xe3#8, 0xc6#8, 0xd7#8, 0xfa#8, .br bop.BLT false, 15, 13, 0x1fac#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006cb8 : List BBlock := [⟨[], some (⟨0x80006cb8#64, 0xf45ff06f#32, 0x6f#8, 0xf0#8, 0x5f#8, 0xf4#8, .j, 0, 0, 0x0#13, 0x1fff44#21, 0#12⟩ : TInstr)⟩]
def ax_80006cbc : List BBlock := [{ body := [mkLine 0x80006cbc#64 0x0005c683#32], term := none }]
def ax_80006cc0 : List BBlock := [{ body := [mkLine 0x80006cc0#64 0x00170713#32], term := none }]
def ax_80006cc4 : List BBlock := [{ body := [mkLine 0x80006cc4#64 0x00777793#32], term := none }]
def ax_80006cc8 : List BBlock := [{ body := [mkLine 0x80006cc8#64 0xfed70fa3#32], term := none }]
def ax_80006ccc : List BBlock := [{ body := [mkLine 0x80006ccc#64 0x00158593#32], term := none }]
def axT_80006cd0 : List BBlock := [⟨[], some (⟨0x80006cd0#64, 0xf0078ee3#32, 0xe3#8, 0x8e#8, 0x07#8, 0xf0#8, .br bop.BEQ true, 15, 0, 0x1f1c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006cd0 : List BBlock := [⟨[], some (⟨0x80006cd0#64, 0xf0078ee3#32, 0xe3#8, 0x8e#8, 0x07#8, 0xf0#8, .br bop.BEQ false, 15, 0, 0x1f1c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006cd4 : List BBlock := [{ body := [mkLine 0x80006cd4#64 0x0005c683#32], term := none }]
def ax_80006cd8 : List BBlock := [{ body := [mkLine 0x80006cd8#64 0x00170713#32], term := none }]
def ax_80006cdc : List BBlock := [{ body := [mkLine 0x80006cdc#64 0x00777793#32], term := none }]
def ax_80006ce0 : List BBlock := [{ body := [mkLine 0x80006ce0#64 0xfed70fa3#32], term := none }]
def ax_80006ce4 : List BBlock := [{ body := [mkLine 0x80006ce4#64 0x00158593#32], term := none }]
def axT_80006ce8 : List BBlock := [⟨[], some (⟨0x80006ce8#64, 0xfc079ae3#32, 0xe3#8, 0x9a#8, 0x07#8, 0xfc#8, .br bop.BNE true, 15, 0, 0x1fd4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80006ce8 : List BBlock := [⟨[], some (⟨0x80006ce8#64, 0xfc079ae3#32, 0xe3#8, 0x9a#8, 0x07#8, 0xfc#8, .br bop.BNE false, 15, 0, 0x1fd4#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006cec : List BBlock := [⟨[], some (⟨0x80006cec#64, 0xf01ff06f#32, 0x6f#8, 0xf0#8, 0x1f#8, 0xf0#8, .j, 0, 0, 0x0#13, 0x1fff00#21, 0#12⟩ : TInstr)⟩]
def ax_80006fe0 : List BBlock := [⟨[], some (⟨0x80006fe0#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80006ff8 : List BBlock := [⟨[], some (⟨0x80006ff8#64, 0x00008067#32, 0x67#8, 0x80#8, 0x00#8, 0x00#8, .jr, 1, 0, 0x0#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_8000722c : List BBlock := [{ body := [mkLine 0x8000722c#64 0xfd010113#32], term := none }]
def ax_80007230 : List BBlock := [{ body := [mkLine 0x80007230#64 0x02813023#32], term := none }]
def ax_80007234 : List BBlock := [{ body := [mkLine 0x80007234#64 0x00913c23#32], term := none }]
def ax_80007238 : List BBlock := [{ body := [mkLine 0x80007238#64 0x01213823#32], term := none }]
def ax_8000723c : List BBlock := [{ body := [mkLine 0x8000723c#64 0x01313423#32], term := none }]
def ax_80007240 : List BBlock := [{ body := [mkLine 0x80007240#64 0x00058413#32], term := none }]
def ax_80007244 : List BBlock := [{ body := [mkLine 0x80007244#64 0x02113423#32], term := none }]
def ax_80007248 : List BBlock := [{ body := [mkLine 0x80007248#64 0x00050913#32], term := none }]
def ax_8000724c : List BBlock := [{ body := [mkLine 0x8000724c#64 0x00014997#32], term := none }]
def ax_80007250 : List BBlock := [{ body := [mkLine 0x80007250#64 0xac498993#32], term := none }]
def ax_80007258 : List BBlock := [{ body := [mkLine 0x80007258#64 0x0109b783#32], term := none }]
def ax_8000725c : List BBlock := [{ body := [mkLine 0x8000725c#64 0x00001737#32], term := none }]
def ax_80007260 : List BBlock := [{ body := [mkLine 0x80007260#64 0x0087b483#32], term := none }]
def ax_80007264 : List BBlock := [{ body := [mkLine 0x80007264#64 0xffc4f493#32], term := none }]
def ax_80007268 : List BBlock := [{ body := [mkLine 0x80007268#64 0x7ff48793#32], term := none }]
def ax_8000726c : List BBlock := [{ body := [mkLine 0x8000726c#64 0x7e078793#32], term := none }]
def ax_80007270 : List BBlock := [{ body := [mkLine 0x80007270#64 0x40878433#32], term := none }]
def ax_80007274 : List BBlock := [{ body := [mkLine 0x80007274#64 0x00c45413#32], term := none }]
def ax_80007278 : List BBlock := [{ body := [mkLine 0x80007278#64 0xfff40413#32], term := none }]
def ax_8000727c : List BBlock := [{ body := [mkLine 0x8000727c#64 0x00c41413#32], term := none }]
def axT_80007280 : List BBlock := [⟨[], some (⟨0x80007280#64, 0x00e44e63#32, 0x63#8, 0x4e#8, 0xe4#8, 0x00#8, .br bop.BLT true, 8, 14, 0x1c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80007280 : List BBlock := [⟨[], some (⟨0x80007280#64, 0x00e44e63#32, 0x63#8, 0x4e#8, 0xe4#8, 0x00#8, .br bop.BLT false, 8, 14, 0x1c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_80007284 : List BBlock := [{ body := [mkLine 0x80007284#64 0x00000593#32], term := none }]
def ax_80007288 : List BBlock := [{ body := [mkLine 0x80007288#64 0x00090513#32], term := none }]
def ax_80007290 : List BBlock := [{ body := [mkLine 0x80007290#64 0x0109b783#32], term := none }]
def ax_80007294 : List BBlock := [{ body := [mkLine 0x80007294#64 0x009787b3#32], term := none }]
def axT_80007298 : List BBlock := [⟨[], some (⟨0x80007298#64, 0x02f50663#32, 0x63#8, 0x06#8, 0xf5#8, 0x02#8, .br bop.BEQ true, 10, 15, 0x2c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def axF_80007298 : List BBlock := [⟨[], some (⟨0x80007298#64, 0x02f50663#32, 0x63#8, 0x06#8, 0xf5#8, 0x02#8, .br bop.BEQ false, 10, 15, 0x2c#13, 0x0#21, 0#12⟩ : TInstr)⟩]
def ax_8000729c : List BBlock := [{ body := [mkLine 0x8000729c#64 0x00090513#32], term := none }]
def ax_800072a4 : List BBlock := [{ body := [mkLine 0x800072a4#64 0x02813083#32], term := none }]
def ax_800072a8 : List BBlock := [{ body := [mkLine 0x800072a8#64 0x02013403#32], term := none }]
def ax_800072ac : List BBlock := [{ body := [mkLine 0x800072ac#64 0x01813483#32], term := none }]

end Vsa.Sim

namespace VsaIris.Sym

open Vsa.Sim Vsa.MemRepr VsaIris.Inst VsaIris.MallocFast

theorem st_80006abc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 11) ≠ (R 14) → AW live S Q 0x80006aac#64 R Mt) (hF : ¬ ((R 11) ≠ (R 14)) → AW live S Q 0x80006ac0#64 R Mt) :
    AW live S Q 0x80006abc#64 R Mt := by
  by_cases hc : (R 11) ≠ (R 14)
  · exact
    swp_step axT_80006abc [11, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80006abc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_bne _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80006abc [11, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80006abc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_bne _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80006ac0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80006ac4#64 (upd R 14 ((R 13) + sign_extend (m := 64) (0x008#12))) Mt) :
    AW live S Q 0x80006ac0#64 R Mt :=
  swp_step ax_80006ac0 [13, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ac0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [13, 14])))) rfl hk

theorem st_80006ac4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80006ac8#64 (upd R 11 ((R 14) + (R 28))) Mt) :
    AW live S Q 0x80006ac4#64 R Mt :=
  swp_step ax_80006ac4 [11, 14, 28] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ac4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11, 14, 28])))) rfl hk

theorem st_80006ac8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80006acc#64 (upd R 15 ((R 14) + (R 15))) Mt) :
    AW live S Q 0x80006ac8#64 R Mt :=
  swp_step ax_80006ac8 [14, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ac8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [14, 15])))) rfl hk

theorem st_80006acc {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80006ad0#64 (upd R 12 ((R 12) &&& sign_extend (m := 64) (0x007#12))) Mt) :
    AW live S Q 0x80006acc#64 R Mt :=
  swp_step ax_80006acc [12] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006acc ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12])))) rfl hk

theorem st_80006ad0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x800069fc#64 R Mt) :
    AW live S Q 0x80006ad0#64 R Mt :=
  swp_step ax_80006ad0 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ad0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => nomatch h) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80006ae0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : AW live S Q (R 1) R Mt) :
    AW live S Q 0x80006ae0#64 R Mt :=
  swp_step ax_80006ae0 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ae0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80006ae4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80006ae8#64 (upd R 12 ((R 13) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80006ae4#64 R Mt :=
  swp_step ax_80006ae4 [12, 13] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ae4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 12 ∈ [12, 13])))) rfl hk

theorem st_80006ae8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x800069fc#64 R Mt) :
    AW live S Q 0x80006ae8#64 R Mt :=
  swp_step ax_80006ae8 [] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ae8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => nomatch h) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (fun _ h => nomatch h)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80006fe0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : AW live S Q (R 1) R Mt) :
    AW live S Q 0x80006fe0#64 R Mt :=
  swp_step ax_80006fe0 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006fe0 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80006ff8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hal : (R 1).toNat % 4 = 0) (hk : AW live S Q (R 1) R Mt) :
    AW live S Q 0x80006ff8#64 R Mt :=
  swp_step ax_80006ff8 [1] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80006ff8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; show (Sail.BitVec.update (R 1 + sign_extend (m := 64) (0x000#12)) 0 0#1).toNat % 4 = 0; rw [ret_tgt _ hal]; exact hal)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) (ret_tgt _ hal)
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_8000722c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007230#64 (upd R 2 ((R 2) + sign_extend (m := 64) (0xfd0#12))) Mt) :
    AW live S Q 0x8000722c#64 R Mt :=
  swp_step ax_8000722c [2] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_8000722c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 2 ∈ [2])))) rfl hk

theorem st_80007230 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : AW live S Q 0x80007234#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x020#12)).toNat, 8, (R 8))])) :
    AW live S Q 0x80007230#64 R Mt :=
  swp_step ax_80007230 [2, 8] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80007230 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80007234 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : AW live S Q 0x80007238#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x018#12)).toNat, 8, (R 9))])) :
    AW live S Q 0x80007234#64 R Mt :=
  swp_step ax_80007234 [2, 9] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80007234 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80007238 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x8000723c#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x010#12)).toNat, 8, (R 18))])) :
    AW live S Q 0x80007238#64 R Mt :=
  swp_step ax_80007238 [2, 18] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x010#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80007238 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_8000723c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80007240#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x008#12)).toNat, 8, (R 19))])) :
    AW live S Q 0x8000723c#64 R Mt :=
  swp_step ax_8000723c [2, 19] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x008#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_8000723c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80007240 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007244#64 (upd R 8 ((R 11) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80007240#64 R Mt :=
  swp_step ax_80007240 [8, 11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007240 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 11])))) rfl hk

theorem st_80007244 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : StOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : AW live S Q 0x80007248#64 R (writeLog Mt [(((R 2) + sign_extend (m := 64) (0x028#12)).toNat, 8, (R 1))])) :
    AW live S Q 0x80007244#64 R Mt :=
  swp_step ax_80007244 [1, 2] [] [] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) 0 rfl (by decide) (by decide) (by decide)
    (fun a ha => outL_single _ ha) hlive
    (fun m hm hLD => by unfold ax_80007244 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact hea)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    hS rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun _ _ _ _ => rfl) rfl hk

theorem st_80007248 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x8000724c#64 (upd R 18 ((R 10) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80007248#64 R Mt :=
  swp_step ax_80007248 [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007248 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 18 ∈ [10, 18])))) rfl hk

theorem st_8000724c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007250#64 (upd R 19 ((0x8000724c#64) + (sign_extend (m := 64) ((0x00014#20) +++ (0x000#12))))) Mt) :
    AW live S Q 0x8000724c#64 R Mt :=
  swp_step ax_8000724c [19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_8000724c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [19])))) rfl hk

theorem st_80007250 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007254#64 (upd R 19 ((R 19) + sign_extend (m := 64) (0xac4#12))) Mt) :
    AW live S Q 0x80007250#64 R Mt :=
  swp_step ax_80007250 [19] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007250 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 19 ∈ [19])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_80007254 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x80007254 [0xef#8, 0xd0#8, 0x5f#8, 0xe1#8], live p.1) :
    JalExec (vsaModel live) 0x80007254 [0xef#8, 0xd0#8, 0x5f#8, 0xe1#8] 0x80005068#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x80007254, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x80007255, .discard, 0xd0#8) (by simp [codeFoot])
  have hb2 := hb (0x80007256, .discard, 0x5f#8) (by simp [codeFoot])
  have hb3 := hb (0x80007257, .discard, 0xe1#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x80007254#64) vm (0xe15fd0ef#32) (0x1fde14#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x80007254#64) 4)
      (0xef#8) (0xd0#8) (0x5f#8) (0xe1#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_e15fd0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x80007254#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80005068#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x80007254#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x80007254 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem st_80007254 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80005068#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x80007254 + 4))) Mt) :
    AW live S Q 0x80007254#64 R Mt :=
  swp_jal 0x80007254 [0xef#8, 0xd0#8, 0x5f#8, 0xe1#8] 0x80005068#64
    (jalx_80007254 live fun p hp => hlive _ (alloc_code_80007254 p hp)) alloc_code_80007254
    (by decide) (by decide) rfl hk

theorem st_80007258 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x8000725c#64 (upd R 15 (ldv .ld Mt ((R 19) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    AW live S Q 0x80007258#64 R Mt :=
  swp_step ax_80007258 [15, 19] [bytesAt (imgM Mt) ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007258 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 19])))) rfl hk

theorem st_8000725c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007260#64 (upd R 14 ((sign_extend (m := 64) ((0x00001#20) +++ (0x000#12))))) Mt) :
    AW live S Q 0x8000725c#64 R Mt :=
  swp_step ax_8000725c [14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_8000725c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 14 ∈ [14])))) rfl hk

theorem st_80007260 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8, S b)
    (hk : AW live S Q 0x80007264#64 (upd R 9 (ldv .ld Mt ((R 15) + sign_extend (m := 64) (0x008#12)).toNat)) Mt) :
    AW live S Q 0x80007260#64 R Mt :=
  swp_step ax_80007260 [9, 15] [bytesAt (imgM Mt) ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8] (accAddrs ((R 15) + sign_extend (m := 64) (0x008#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007260 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9, 15])))) rfl hk

theorem st_80007264 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007268#64 (upd R 9 ((R 9) &&& sign_extend (m := 64) (0xffc#12))) Mt) :
    AW live S Q 0x80007264#64 R Mt :=
  swp_step ax_80007264 [9] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007264 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [9])))) rfl hk

theorem st_80007268 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x8000726c#64 (upd R 15 ((R 9) + sign_extend (m := 64) (0x7ff#12))) Mt) :
    AW live S Q 0x80007268#64 R Mt :=
  swp_step ax_80007268 [9, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007268 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [9, 15])))) rfl hk

theorem st_8000726c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007270#64 (upd R 15 ((R 15) + sign_extend (m := 64) (0x7e0#12))) Mt) :
    AW live S Q 0x8000726c#64 R Mt :=
  swp_step ax_8000726c [15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_8000726c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15])))) rfl hk

theorem st_80007270 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007274#64 (upd R 8 ((R 15) - (R 8))) Mt) :
    AW live S Q 0x80007270#64 R Mt :=
  swp_step ax_80007270 [8, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007270 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8, 15])))) rfl hk

theorem st_80007274 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007278#64 (upd R 8 (shift_bits_right (R 8) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) Mt) :
    AW live S Q 0x80007274#64 R Mt :=
  swp_step ax_80007274 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007274 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem st_80007278 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x8000727c#64 (upd R 8 ((R 8) + sign_extend (m := 64) (0xfff#12))) Mt) :
    AW live S Q 0x80007278#64 R Mt :=
  swp_step ax_80007278 [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007278 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem st_8000727c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007280#64 (upd R 8 (shift_bits_left (R 8) (Sail.BitVec.extractLsb (0x0c#6) 5 0))) Mt) :
    AW live S Q 0x8000727c#64 R Mt :=
  swp_step ax_8000727c [8] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_8000727c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [8])))) rfl hk

theorem st_80007280 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 8).toInt < (R 14).toInt → AW live S Q 0x8000729c#64 R Mt) (hF : ¬ ((R 8).toInt < (R 14).toInt) → AW live S Q 0x80007284#64 R Mt) :
    AW live S Q 0x80007280#64 R Mt := by
  by_cases hc : (R 8).toInt < (R 14).toInt
  · exact
    swp_step axT_80007280 [8, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80007280 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_blt _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80007280 [8, 14] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80007280 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_blt _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_80007284 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007288#64 (upd R 11 ((0#64) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80007284#64 R Mt :=
  swp_step ax_80007284 [11] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007284 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 11 ∈ [11])))) rfl hk

theorem st_80007288 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x8000728c#64 (upd R 10 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x80007288#64 R Mt :=
  swp_step ax_80007288 [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007288 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 18])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_8000728c (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x8000728c [0xef#8, 0xf0#8, 0x0f#8, 0xee#8], live p.1) :
    JalExec (vsaModel live) 0x8000728c [0xef#8, 0xf0#8, 0x0f#8, 0xee#8] 0x8000696c#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x8000728c, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x8000728d, .discard, 0xf0#8) (by simp [codeFoot])
  have hb2 := hb (0x8000728e, .discard, 0x0f#8) (by simp [codeFoot])
  have hb3 := hb (0x8000728f, .discard, 0xee#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x8000728c#64) vm (0xee0ff0ef#32) (0x1ff6e0#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x8000728c#64) 4)
      (0xef#8) (0xf0#8) (0x0f#8) (0xee#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_ee0ff0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x8000728c#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x8000696c#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x8000728c#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x8000728c + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem st_8000728c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x8000696c#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x8000728c + 4))) Mt) :
    AW live S Q 0x8000728c#64 R Mt :=
  swp_jal 0x8000728c [0xef#8, 0xf0#8, 0x0f#8, 0xee#8] 0x8000696c#64
    (jalx_8000728c live fun p hp => hlive _ (alloc_code_8000728c p hp)) alloc_code_8000728c
    (by decide) (by decide) rfl hk

theorem st_80007290 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8, S b)
    (hk : AW live S Q 0x80007294#64 (upd R 15 (ldv .ld Mt ((R 19) + sign_extend (m := 64) (0x010#12)).toNat)) Mt) :
    AW live S Q 0x80007290#64 R Mt :=
  swp_step ax_80007290 [15, 19] [bytesAt (imgM Mt) ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8] (accAddrs ((R 19) + sign_extend (m := 64) (0x010#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007290 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [15, 19])))) rfl hk

theorem st_80007294 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80007298#64 (upd R 15 ((R 15) + (R 9))) Mt) :
    AW live S Q 0x80007294#64 R Mt :=
  swp_step ax_80007294 [9, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_80007294 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 15 ∈ [9, 15])))) rfl hk

theorem st_80007298 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hT : (R 10) = (R 15) → AW live S Q 0x800072c4#64 R Mt) (hF : ¬ ((R 10) = (R 15)) → AW live S Q 0x8000729c#64 R Mt) :
    AW live S Q 0x80007298#64 R Mt := by
  by_cases hc : (R 10) = (R 15)
  · exact
    swp_step axT_80007298 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axT_80007298 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_beq _ _).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hT hc)
  · exact
    swp_step axF_80007298 [10, 15] [] [] [] 0 rfl (by decide) (by decide) (by decide)
      (fun a _ => trivial) hlive
      (fun m hm hLD => by unfold axF_80007298 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact (guard_false (guard_beq _ _)).2 hc)
      (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
      (fun a h => by cases h) rfl
      (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
      (fun _ _ _ _ => rfl) rfl (hF hc)

theorem st_8000729c {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x800072a0#64 (upd R 10 ((R 18) + sign_extend (m := 64) (0x000#12))) Mt) :
    AW live S Q 0x8000729c#64 R Mt :=
  swp_step ax_8000729c [10, 18] [] [] [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_8000729c ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_")
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) (fun a h => by cases h)
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 10 ∈ [10, 18])))) rfl hk

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail in

theorem jalx_800072a0 (live : Nat → Prop)
    (hlive : ∀ p ∈ codeFoot 0x800072a0 [0xef#8, 0xd0#8, 0x1f#8, 0xdd#8], live p.1) :
    JalExec (vsaModel live) 0x800072a0 [0xef#8, 0xd0#8, 0x1f#8, 0xdd#8] 0x80005070#64 := by
  refine jalExec_of_site live _ _ _ hlive fun c hG hi hpc hb => ?_
  obtain ⟨vm, hmi⟩ := hG.minstret
  have hb0 := hb (0x800072a0, .discard, 0xef#8) (by simp [codeFoot])
  have hb1 := hb (0x800072a1, .discard, 0xd0#8) (by simp [codeFoot])
  have hb2 := hb (0x800072a2, .discard, 0x1f#8) (by simp [codeFoot])
  have hb3 := hb (0x800072a3, .discard, 0xdd#8) (by simp [codeFoot])
  obtain ⟨σ', i', hs, hi', hG', hmem, hobs⟩ :=
    stepObs_jal c.σ c.tick c.steps (0x800072a0#64) vm (0xdd1fd0ef#32) (0x1fddd0#21)
      (regidx.Regidx 0x01#5) Register.x1 (BitVec.addInt (0x800072a0#64) 4)
      (0xef#8) (0xd0#8) (0x1f#8) (0xdd#8)
      hG hpc hmi hb0 hb1 hb2 hb3 (by decide) (by decide) (by decide)
      (by apply BitVec.eq_of_toNat_eq; decide) (by apply BitVec.eq_of_toNat_eq; decide)
      (Vsa.Sim.DecodeTable.decode_dd1fd0ef (afterPrelude c.σ)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.misa)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.cur_privilege)
        (by rw [get?_afterPrelude c.σ _ (by decide)]; exact hG.mseccfg))
      (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (wX_bits_x1 _ (BitVec.addInt (0x800072a0#64) 4)) hi
  have h := jalStep_of_obs (calleeEntry := 0x80005070#64) hs hi' hG' hmem hobs
    (by apply BitVec.eq_of_toNat_eq; decide)
  refine ⟨?_, stepConFrame_of_jalObs hs hobs⟩
  rwa [show BitVec.addInt (0x800072a0#64 : BitVec 64) 4 = BitVec.ofNat 64 (0x800072a0 + 4) from by
    apply BitVec.eq_of_toNat_eq; decide] at h

theorem st_800072a0 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hk : AW live S Q 0x80005070#64 (upd R VsaIris.ra (BitVec.ofNat 64 (0x800072a0 + 4))) Mt) :
    AW live S Q 0x800072a0#64 R Mt :=
  swp_jal 0x800072a0 [0xef#8, 0xd0#8, 0x1f#8, 0xdd#8] 0x80005070#64
    (jalx_800072a0 live fun p hp => hlive _ (alloc_code_800072a0 p hp)) alloc_code_800072a0
    (by decide) (by decide) rfl hk

theorem st_800072a4 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8, S b)
    (hk : AW live S Q 0x800072a8#64 (upd R 1 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x028#12)).toNat)) Mt) :
    AW live S Q 0x800072a4#64 R Mt :=
  swp_step ax_800072a4 [1, 2] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x028#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_800072a4 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 1 ∈ [1, 2])))) rfl hk

theorem st_800072a8 {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8, S b)
    (hk : AW live S Q 0x800072ac#64 (upd R 8 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x020#12)).toNat)) Mt) :
    AW live S Q 0x800072a8#64 R Mt :=
  swp_step ax_800072a8 [2, 8] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x020#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_800072a8 ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 8 ∈ [2, 8])))) rfl hk

theorem st_800072ac {live : Nat → Prop} {S : Nat → Prop}
    {Q : (Nat → BitVec 64) → (Nat → BitVec 8) → Prop} {R : Nat → BitVec 64} {Mt : Mem}
    (hlive : ∀ p ∈ allocText, live p.1)
    (hea : LdOK ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8)
    (hLDS : ∀ b ∈ accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8, S b)
    (hk : AW live S Q 0x800072b0#64 (upd R 9 (ldv .ld Mt ((R 2) + sign_extend (m := 64) (0x018#12)).toNat)) Mt) :
    AW live S Q 0x800072ac#64 R Mt :=
  swp_step ax_800072ac [2, 9] [bytesAt (imgM Mt) ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8] (accAddrs ((R 2) + sign_extend (m := 64) (0x018#12)).toNat 8) [] 0 rfl (by decide) (by decide) (by decide)
    (fun a _ => trivial) hlive
    (fun m hm hLD => by unfold ax_800072ac ChainFacts; chain_facts hm with "VsaIris.Sym.alloc_at_"; exact ⟨hea, lpins8_img hLD⟩)
    (by decide) (by decide) (fun h => absurd h (by decide)) (by decide) hLDS
    (fun a h => by cases h) rfl
    (by intro x hx hg; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; rcases hx with rfl | rfl <;> first | rfl | exact absurd rfl hg)
    (fun x _ _ hx => upd_other _ _ (fun e => hx (e ▸ (by decide : 9 ∈ [2, 9])))) rfl hk

end VsaIris.Sym
