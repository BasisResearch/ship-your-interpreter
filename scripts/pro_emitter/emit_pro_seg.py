#!/usr/bin/env python3
"""House-style (SnprintfSpec22-pattern) segment emitter for the svfprintf
prologue segments SnprintfSpec27-33.  Each segment module is emitted from a
python step table; the repetitive per-step ceremony (obtain/step/pc/minstret/
rd/pins/mem threading + Steps assembly) is generated; hypotheses, guards and
postconditions are supplied as strings with $p:xN / $mE / final-name
placeholders."""
import re

OBS = {"alu": "alu", "store": "store", "jal": "jal", "jalr": "jalr",
       "jr": "jr", "btaken": "btaken", "bnottaken": "bnottaken"}
PINSFN = {"alu": "pins_alu", "store": "pins_store", "jal": "pins_jal",
          "jalr": "pins_jalr", "jr": "pins_jr", "btaken": "pins_btaken",
          "bnottaken": "pins_bnottaken"}
WRITES = {"alu", "jal", "jalr"}


class Seg:
    def __init__(self, pins, mem0="c.σ.mem"):
        self.pins = list(pins)      # [(reg,"x2"), valexpr]
        self.mem = mem0
        self.out = []
        self.k = 0

    # ---------- helpers ----------
    def pinpath(self, reg, hp):
        idx = [i for i, (r, _) in enumerate(self.pins) if r == reg]
        if not idx:
            raise KeyError(f"{reg} not pinned; pins={[r for r,_ in self.pins]}")
        return hp + ".2" * idx[0] + ".1"

    def subst(self, s, hp, mE, P):
        s = re.sub(r"\$p:(x\d+)", lambda m: self.pinpath(m.group(1), hp), s)
        s = re.sub(r"\$L:(\w+)", lambda m: m.group(1) + str(P), s)
        s = s.replace("$L", "hsl" + str(P))
        s = s.replace("$mE", mE)
        s = s.replace("$K", str(P))
        return s

    def emit(self, *lines):
        self.out.extend(lines)

    # ---------- one machine step ----------
    def step(self, addr, cls, site, vals="", hyps="", nextpc=None, pcrw="add4",
             jal_imm=None, rd=None, rdval=None, rdrw=None, track=False,
             memw=None, pre=(), post=(), comment=""):
        self.k += 1
        k, P = self.k, self.k - 1
        sP = "c.σ" if P == 0 else f"σ{P}"
        iP = "c.tick" if P == 0 else f"i{P}"
        uP = "c.steps" if P == 0 else f"(c.steps + {P})"
        vmiP = "vmi0" if P == 0 else f"vmi{P}"
        hGP = "hG" if P == 0 else f"hG{P}"
        hpcP = "hpc" if P == 0 else f"hpc{P}"
        hmiP = "hmi0" if P == 0 else f"hmi{P}"
        hiP = "htick" if P == 0 else f"hi{P}"
        hpP = "hp0" if P == 0 else f"hp{P}"
        mEP = None if P == 0 else f"hmE{P}"
        ocls = OBS[cls]
        sub = lambda s: self.subst(s, hpP, mEP or "rfl", P)

        self.emit(f"  -- === 0x{addr:x}: {comment} ===")
        for ln in pre:
            self.emit("  " + sub(ln))
        vals_s = (" " + sub(vals)) if vals else ""
        self.emit(
            f"  obtain ⟨σ{k}, i{k}, hs{k}, hi{k}, hG{k}, hmem{k}, hobs{k}⟩ :=",
            f"    {site} {sP} {iP} {uP} _ {vmiP}{vals_s}",
            f"      {hGP} {hpcP} {hmiP} {sub(hyps)} {hiP}",
        )
        if k == 1:
            self.emit("  have hstep1 : Step c ⟨σ1, i1, c.steps + 1⟩ := by cases c; exact hs1")
        else:
            self.emit(f"  have hstep{k} : Step ⟨σ{P}, i{P}, c.steps + {P}⟩"
                      f" ⟨σ{k}, i{k}, c.steps + {k}⟩ := hs{k}")
        # PC
        if pcrw == "add4":
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_{ocls}_pc hobs{k}",
                f"    rwa [show BitVec.addInt (0x{addr:08x}#64) 4 = (0x{nextpc:08x}#64 : BitVec 64)"
                f" from by apply BitVec.eq_of_toNat_eq; decide] at this",
            )
        elif pcrw == "tgt":
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_btaken_pc hobs{k}",
                f"    rwa [{site}_tgt] at this",
            )
        elif pcrw == "jal":
            imm = jal_imm if jal_imm is not None else (nextpc - addr) & 0x1FFFFF
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_jal_pc hobs{k}",
                f"    rwa [show (0x{addr:08x}#64 : BitVec 64) + sign_extend (m := 64)"
                f" (0x{imm:06x}#21) = (0x{nextpc:08x}#64 : BitVec 64) from by"
                f" apply BitVec.eq_of_toNat_eq; decide] at this",
            )
        elif isinstance(pcrw, tuple) and pcrw[0] == "btshow":
            imm13 = pcrw[1]
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_btaken_pc hobs{k}",
                f"    rwa [show (0x{addr:08x}#64 : BitVec 64) + sign_extend (m := 64)"
                f" (0x{imm13:04x}#13) = (0x{nextpc:08x}#64 : BitVec 64) from by"
                f" apply BitVec.eq_of_toNat_eq; decide] at this",
            )
        elif pcrw == "ret":
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_jr_pc hobs{k}",
                f"    rwa [ret_tgt _ (by decide)] at this",
            )
        elif isinstance(pcrw, tuple) and pcrw[0] == "jrshow":
            # pcrw = ("jrshow", have_name) referencing a pre-emitted equality have
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_jr_pc hobs{k}",
                f"    rwa [{pcrw[1]}] at this",
            )
        elif isinstance(pcrw, tuple) and pcrw[0] == "jalrshow":
            self.emit(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some (0x{nextpc:08x}#64) := by",
                f"    have := obs_jalr_pc hobs{k}",
                f"    rwa [{pcrw[1]}] at this",
            )
        else:
            raise ValueError(pcrw)
        # minstret
        self.emit(f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_{ocls}_minstret hobs{k}")
        # rd
        if rd is not None:
            rdfn = {"alu": "obs_alu_rd", "jal": "obs_jal_rd", "jalr": "obs_jalr_rd"}[cls]
            dec5 = "(by decide) (by decide) (by decide) (by decide) (by decide)"
            if rdrw is None:
                self.emit(f"  have hrd{k} : σ{k}.regs.get? Register.{rd} = some ({sub(rdval)}) :=",
                          f"    {rdfn} hobs{k} {dec5}")
            elif rdrw == "raw":
                self.emit(f"  have hrd{k} := {rdfn} hobs{k} {dec5}")
            else:
                self.emit(
                    f"  have hrd{k} : σ{k}.regs.get? Register.{rd} = some ({sub(rdval)}) := by",
                    f"    have := {rdfn} hobs{k} {dec5}",
                    f"    rwa [{sub(rdrw)}] at this",
                )
        # pins
        pfn = PINSFN[cls]
        if cls in WRITES and rd is not None:
            idx = [i for i, (r, _) in enumerate(self.pins) if r == rd]
            if idx:
                j = idx[0]
                base = f"{hpP}.2" if j == 0 else f"(pins_drop{j+1}_pro {hpP})"
                del self.pins[j]
            else:
                base = hpP
            transported = f"{pfn} hobs{k} (by rfl) {base}"
            if track:
                self.emit(f"  have hp{k} := pins_cons_pro hrd{k} ({transported})")
                self.pins.insert(0, (rd, rdval))
            else:
                self.emit(f"  have hp{k} := {transported}")
        else:
            self.emit(f"  have hp{k} := {pfn} hobs{k} (by rfl) {hpP}")
        # mem
        if memw is None:
            if P == 0:
                self.emit(f"  have hmE1 : σ1.mem = c.σ.mem := hmem1")
            else:
                self.emit(f"  have hmE{k} : σ{k}.mem = {self.mem} := hmem{k}.trans hmE{P}")
        else:
            kind, key, data, rws = memw
            wrap = {"w8": "writeMap8", "w4": "writeMap4"}.get(kind)
            if wrap:
                new = f"{wrap} ({self.mem}) ({key}) ({data})"
            else:
                new = f"({self.mem}).insert ({key}) ({data})"
            rwl = ", ".join(["mem_afterNextPC"] + ([mEP] if mEP else []) + list(rws))
            self.emit(
                f"  have hmE{k} : σ{k}.mem = {new} := by",
                f"    rw [hmem{k}, {rwl}]",
            )
            self.mem = new
        for ln in post:
            self.emit("  " + self.subst(ln, f"hp{k}", f"hmE{k}", k))
        self.emit("")

    # ---------- finish ----------
    def finish(self, post_lines, refine_items):
        N = self.k
        for ln in post_lines:
            self.out.append("  " + self.subst(ln, f"hp{N}", f"hmE{N}", N))
        items = ",\n    ".join(
            self.subst(x, f"hp{N}", f"hmE{N}", N) for x in refine_items)
        self.out.append(f"  refine ⟨⟨σ{N}, i{N}, c.steps + {N}⟩, ?_,")
        self.out.append(f"    {items}⟩")
        chain = f"(Steps.single hstep{N})"
        for j in range(N - 1, 0, -1):
            chain = f"((Steps.single hstep{j}).trans {chain})"
        # strip outer parens
        self.out.append("  exact " + chain[1:-1])
        return "\n".join(self.out)


def module(imports, doc, body, opens_extra=""):
    imp = "\n".join(f"import {m}" for m in imports)
    return f"""{imp}

/-!
{doc}
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic
{opens_extra}
set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace Vsa.Sim

{body}

end Vsa.Sim
"""
