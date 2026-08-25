#!/usr/bin/env python3
"""gen_segment.py — whole-segment COMPOSITION emitter (Layer-3 house style).

Where scripts/gen_sites.py generates the per-instruction `site_*` StepObs
batteries, this tool generates the *composition ceremony* on top of them: a
Lean theorem `tr_<name> : Triple Pre Post` that chains an obtain per site,
the PC rewrite, ONE `pins_*` register-bundle transport per step (RegPins),
minstret threading, memory threading (`hmemE<k>` equations + code-pin
survival), ghost register-frame threading, the `Steps.single/.trans` chain,
and the final postcondition assembly.

Modes
=====
  --mode straight   plain straight-line segment; the spec JSON is the core
                    segment-spec format (see below).
  --mode prologue   frame-table front-end: `addi sp,sp,-K` + `sd` spills
                    (+ interleaved straight steps).  Emits inline Pre/Post
                    structures, mechanical `hkey` offset lemmas, SlotFrame
                    `slot_save`/`slot_survives_writeMap8` post facts.
  --mode epilogue   frame-table front-end: `ld` reloads fed from SlotHolds
                    via `slot_reload_bytes`/`slot_reassemble`, `addi sp,sp,K`,
                    `ret` (via `ret_tgt`).  Emits inline Pre/Post structures.
  --mode call       same core format as straight; requires >= 1 step of
                    class "call" (jal + callee-spec glue via `pins_of_frame`).
  --mode loop       whole `Triple.loop` instantiation from a loop-spec JSON
                    (see LOOP-SPEC below): AtHead/LoopI defs, the measure,
                    the loopmu_head lemma, loop_body, loop_to_done — the
                    StrcpySpec/SnprintfSpec18 loop-layer structure.

Boundary option ("boundary": "segst", straight mode)
====================================================
With `"boundary": "segst"` the generated theorem's Pre and Post are `SegSt`
instances (Vsa/Sim/SegState.lean): `SegSt pcv L P` with the pins list `L`
from the spec's `pins` and payload
`P = fun σ => <loaded_pred> σ.mem ∧ σ.mem = <mem> ∧ [frame blanket]`.
`pre`/`post`/`pre_bind`/`post_proof` are all synthesized: the Pre is
destructured mechanically, the Post pins list / PC / memory expression are
computed by the step threading, and the closing assembly is emitted complete
— zero holes, no `hclose`.  Extra spec fields: `entry` (the pre PC),
`mem_param` (the Pre memory name, default "m0"; must be a theorem param).
Pure ghosts that lived in a bespoke Pre record (MvRegions/MvBytes-style)
become theorem parameters.  Straight-line only (no call steps), and every
store's accumulated memory expression must be parameter-level.

LOOP-SPEC JSON (--mode loop)
============================
{
  "namespace": "Vsa.Sim", "imports": [...], "doc": "...",
  "params": ["(g : ...) (r dst src : BitVec 64)", ...],  # shared binders
  "args": "g r dst src n m0 bs",       # the binders applied, in order
  "names": { "at_head": "AtHeadMv_gen", "loop_inv": "LoopIMv_gen",
             "loop_mu": "LoopMuMv_gen", "loopmu_head": "loopmu_head_mv_gen",
             "loop_body": "loop_body_mv_gen",
             "loop_to_done": "loop_to_done_mv_gen" },
  "head": "StMv g $i r dst src n m0 bs",     # head state at iteration $i
  "done": "StMvDone g r dst src n m0 bs",    # done state
  "body_lemma": "iterMv g $i r dst src n m0 bs",           # head(i) → pre-branch
  "back_lemma": "tr_bne_back_mv g $i r dst src n m0 bs $hlt",  # i+1 < bound
  "done_lemma": "tr_bne_done_mv g $i r dst src n m0 bs $heq",  # i+1 = bound
  "bound": "n",                        # iteration bound (head has i < bound)
  "mu_reg": "x15",                     # measure register
  "mu_field": "a5",                    # head-structure field pinning mu_reg
  "done_mu_field": "a5",               # done-structure field pinning mu_reg
  "mu_expr": "2^64 - (dst.toNat + $i)",      # measure value at head($i)
  "mu_done_expr": "2^64 - (dst.toNat + n)",  # measure value at done
  "mu_head_proof": ["rw [ptr_toNat dst i (by ... omega)]"],  # after the simp
  "mu_done_proof": ["rw [ptr_toNat dst n (by omega)]"],      # after the simp
  "body_prelude": ["have hnw := hSt.regions.dst_nowrap"]     # facts for omega
}
The emitted layer assumes the Spec18 loop shape: the head existential is
strict (`i < bound`), the guard B is AtHead itself, and the exit runs
through the body's `i+1 = bound` branch (`done_lemma`).  The two branch
lemmas themselves stay hand-written (or gen via the site battery) — the
loop mode consumes them by name.

Core segment-spec JSON
======================
{
  "theorem": "tr_setup_mv_gen",
  "doc": "...",                         # docstring for the theorem
  "namespace": "Vsa.Sim",
  "imports": ["Vsa.Sim.SnprintfSpec18", "Vsa.Sim.RegPins"],
  "decls": ["...raw Lean emitted before the theorem (Pre/Post structs)..."],
  "params": ["(g : ...)", "(n : Nat) ..."],   # theorem binders, one per line
  "pre":  "StMvF0 g r dst src n m0 bs",       # Pre predicate applied to args
  "post": "AtHeadMv g r dst src n m0 bs",     # Post; or "post_abstract": true
  "loaded_pred": "Vsa.Sim.Code.MemmoveLoaded",
  "pre_bind": {                    # names bound by the Pre destructuring
    "obtain": "⟨hgood, hloaded, hpc, ..., ⟨vmi, hmi⟩, htick, ...⟩",
    "good": "hgood", "pc": "hpc", "minstret_var": "vmi", "minstret": "hmi",
    "tick": "htick", "loaded": "hloaded",
    "mem0": "m0", "memeq": "hmemeq"  # or "mem0": "c.σ.mem" (no memeq)
  },
  "pins": [ {"reg": "x10", "val": "dst", "hyp": "ha0"}, ... ],
  "frame": {                       # optional ghost register-frame threading
    "pred": "NotWrittenMv", "rhs": "g R", "init": "hframe",
    "tmpl": { "alu": "frame_alu_mv $hobs R hR.$rd hR",
              "bnottaken": "frame_bnottaken_mv $hobs R hR", ... } },
  "prelude": ["have hn1 := hreg.n1", ...],
  "steps": [ ...step dicts... ],
  "post_proof": ["refine ⟨...⟩", ...]   # omitted => hclose hypothesis param
  "hclose_extra": [{"type": "...σ'...", "arg": "hcopied2"}, ...]
}

Step dict (site step):
  { "addr": "0x800069f0", "site": "site_69f0",
    "class": "alu" | "sd" | "sw" | "sb" | "btaken" | "bnottaken"
           | "jal" | "jr" | "j" | "call",
    "call": "$vmi ... $hG $hpc $hmi $pin:x12 $hmem rfl $hi",
    "pre_lines": ["...raw Lean before the obtain..."],
    # branch steps whose operands are CONCRETE at spec time (constant
    # registers / immediate data, e.g. parse-loop tests over known
    # format-string bytes): `"guard": "decide"` makes the `$guard`
    # placeholder in "call" expand to `(by decide)` — no pre_lines
    # guard fact needed.  Using `$guard` without the option is an error.
    "guard": "decide",
    # register write (alu/jal):
    "rd": "x15", "rd_val": "(0x1f#64)", "rw": "li31_val",
    # branches / jumps:
    "imm": "0x0030#13", "target": "0x800069f8",     # btaken / j / jal
    "pc_rw": "ret_tgt r halign", "pc_val": "r",     # jr (raw)
    # stores (sd/sw/sb):
    "key": "vsp.toNat - 24", "key_rw": "hkey40",    # EA.toNat normalization
    "src_val": "v9",                                # stored value expression
    "data_rw": "stData_zext",                       # optional (sb)
    "loaded_via": "ssputs_writeMap8_ss _ _ _ (by omega) $prev" }

Placeholders ($-sigil; `@` collides with Lean explicit-application):
  $sigma $tick $u        previous state / tick / step-count expressions
  $vmi $hG $hpc $hmi     previous minstret value / GoodState / PC / minstret
  $hmem                  previous loaded-predicate fact
  $memeq                 previous accumulated memory equation (hmemE<k-1>)
  $hi                    previous tick bound
  $pin:xN                hypothesis for tracked register xN (bundle projection)
  $v:xN                  current tracked value expression of register xN
  $k                     the current step index
  $prev                  (inside "loaded_via") previous loaded fact

Call step (class "call"), after a jal step:
  { "class": "call", "callee": "memmove_fwd_spec",
    "args": "(fun R => $sigma.regs.get? R) (0x800143c4#64) d s n m0 bs (by decide)",
    "pre_fields": ["$hG", "...", "$pin:x10", ...],     # callee Pre, in order
    "post_obtain": "⟨hG2c, hpc2c, ...⟩",
    "post_good": "hG2c", "post_pc": "hpc2c", "post_tick": "htick2",
    "pc_val": "(0x800143c4#64 : BitVec 64)",
    "pins_drop": ["x11"],
    "pins_add": [{"reg": "x10", "val": "d", "hyp": "hx10c"}],
    "write_set": ["x11", "x13", ..., "mip"],   # = callee NotWritten tuple order
    "frame_hyp": "hrf2",
    "loaded_lines": ["have hload$k : ... := ..."],     # optional raw
    "mem_expr": "...", "mem_lines": [...],             # optional raw hmemE$k
    "frame_lines": [...] }                             # optional raw hframe$k

Every mechanical part is emitted complete; the parts that stay hand-written
are marked in the spec: guard facts (`pre_lines`), value rewrites (`rw`),
store-key normalizations (`key_rw` lemmas in `prelude`), code-pin survival
for stores (`loaded_via`), callee Pre fields, and the final `post_proof`
(or, if omitted, the whole postcondition assembly becomes an `hclose`
hypothesis parameter so the generated theorem still compiles green).
"""

import argparse
import json
import re
import sys
from pathlib import Path

# ---------------------------------------------------------------------------
# small helpers

PIN_FAM = {"alu": "alu", "sd": "store", "sw": "store", "sb": "store",
           "btaken": "btaken", "bnottaken": "bnottaken",
           "jal": "jal", "jr": "jr", "j": "jr"}
OBS_FAM = {"alu": "alu", "sd": "store", "sw": "store", "sb": "store",
           "btaken": "btaken", "bnottaken": "bnottaken",
           "jal": "jal", "jr": "jr", "j": "jr"}
STORE_FN = {"sd": ("writeMap8", "sdData_val"), "sw": ("writeMap4", "swData"),
            "sb": (None, None)}  # sb handled specially (insert)
SEXT_K = {8: "sext_ff8_toNat", 16: "sext_ff0_toNat", 32: "sext_fe0_toNat",
          48: "sext_fd0_toNat", 64: "sext_fc0_toNat"}


def hexint(s):
    return int(str(s), 16) if isinstance(s, str) else int(s)


def bv64(addr: int) -> str:
    return f"(0x{addr:08x}#64)"


def proj(base: str, idx: int) -> str:
    return base + ".2" * idx + ".1"


def pin_term(reg: str, val: str) -> str:
    return f"⟨Register.{reg}, {val}⟩"


def pin_list(pins) -> str:
    return "[" + ", ".join(pin_term(r, v) for r, v in pins) + "]"


class SpecError(Exception):
    pass


def file_header(spec: dict) -> str:
    header = "\n".join(f"import {m}" for m in spec["imports"])
    header += f"""

/-!
Generated by scripts/gen_segment.py — do not hand-edit; regenerate instead.
{spec.get('doc', '')}
-/

open LeanRV64DExecutable LeanRV64DExecutable.Functions Sail ConcurrencyInterfaceV1 Vsa
open Register
open Sail.ConcurrencyInterfaceV1.PreSail
open Vsa.Machine (MState Config Step Steps)
open Vsa.Logic

set_option maxHeartbeats 8000000
set_option maxRecDepth 1000000

namespace {spec.get('namespace', 'Vsa.Sim')}
"""
    return header


# ---------------------------------------------------------------------------
# core emitter

class SegmentEmitter:
    def __init__(self, spec: dict):
        self.spec = spec
        self.pins = [(p["reg"], p["val"]) for p in spec.get("pins", [])]
        self.pin_hyps = [p.get("hyp") for p in spec.get("pins", [])]
        self.segst = spec.get("boundary") == "segst"
        self.frame = spec.get("frame")
        self.lines: list[str] = []
        self.chain: str | None = None          # Steps chain expression so far
        self.state = "c.σ"                     # current state expression
        self.tick = "c.tick"
        self.u_base = "c.steps"                # step-count base expression
        self.u_plus = 0
        self.has_memE = "memeq" in spec.get("pre_bind", {}) or True
        self.mem_expr = None                   # accumulated memory expression
        self.k = 0                             # last completed step index

    # -- previous-fact names -------------------------------------------------

    def pv(self, key: str) -> str:
        """Name of the previous step's standard fact `key`."""
        pb = self.spec["pre_bind"]
        if self.k == 0:
            return {"hG": pb["good"], "hpc": pb["pc"], "vmi": pb["minstret_var"],
                    "hmi": pb["minstret"], "hi": pb["tick"],
                    "hmem": pb["loaded"], "hp": "hp0",
                    "memeq": pb.get("memeq"), "hframe":
                        (self.frame or {}).get("init")}[key]
        return {"hG": f"hG{self.k}", "hpc": f"hpc{self.k}", "vmi": f"vmi{self.k}",
                "hmi": f"hmi{self.k}", "hi": f"hi{self.k}",
                "hmem": f"hload{self.k}", "hp": f"hp{self.k}",
                "memeq": f"hmemE{self.k}" if self.mem_expr is not None else None,
                "hframe": f"hframe{self.k}"}[key]

    def u_expr(self) -> str:
        return self.u_base + " + 1" * self.u_plus

    # -- placeholder substitution -------------------------------------------

    def subst(self, text: str, k: int) -> str:
        def pin_repl(m):
            reg = m.group(1)
            for i, (r, _) in enumerate(self.pins):
                if r == reg:
                    return proj(self.pv("hp"), i)
            raise SpecError(f"step {k}: $pin:{reg} not in the tracked bundle "
                            f"{[r for r, _ in self.pins]}")

        def val_repl(m):
            reg = m.group(1)
            for r, v in self.pins:
                if r == reg:
                    return v
            raise SpecError(f"step {k}: $v:{reg} not tracked")

        text = re.sub(r"\$pin:(\w+)", pin_repl, text)
        text = re.sub(r"\$v:(\w+)", val_repl, text)
        memeq = self.pv("memeq")
        table = {
            "$sigma": self.state, "$tick": self.tick, "$u": self.u_expr(),
            "$vmi": self.pv("vmi"), "$hG": self.pv("hG"),
            "$hpc": self.pv("hpc"), "$hmi": self.pv("hmi"),
            "$hmem": self.pv("hmem"), "$hi": self.pv("hi"),
            "$memeq": memeq if memeq else "$memeq(NONE)",
            "$k": str(k),
        }
        for key in sorted(table, key=len, reverse=True):
            text = text.replace(key, table[key])
        return text

    # -- pins maintenance ----------------------------------------------------

    def emit_pins(self, k: int, cls: str, rd: str | None, rd_val: str | None,
                  track_rd: bool):
        fam = PIN_FAM[cls]
        prev_hp = self.pv("hp")
        idx = next((i for i, (r, _) in enumerate(self.pins) if r == rd), None) \
            if rd else None
        if rd is not None and idx is not None:
            # rd is currently in the bundle: restrict, transport, re-add
            rest = [p for i, p in enumerate(self.pins) if i != idx]
            projs = [proj(prev_hp, i) for i in range(len(self.pins)) if i != idx]
            self.lines.append(
                f"  have hq{k} : PinsHold {self.state} {pin_list(rest)} :=\n"
                f"    ⟨{', '.join(projs + ['trivial'])}⟩")
            transported = f"pins_{fam} hobs{k} (by rfl) hq{k}"
            base = rest
        else:
            transported = f"pins_{fam} hobs{k} (by rfl) {prev_hp}"
            base = self.pins
        if rd is not None and track_rd:
            assert rd_val is not None
            new_pins = [(rd, rd_val)] + base
            self.lines.append(
                f"  have hp{k} : PinsHold σ{k} {pin_list(new_pins)} :=\n"
                f"    ⟨hrd{k}, {transported}⟩")
            self.pins = new_pins
        else:
            self.lines.append(
                f"  have hp{k} : PinsHold σ{k} {pin_list(base)} :=\n"
                f"    {transported}")
            self.pins = base

    # -- per-step emission ---------------------------------------------------

    def emit_site_step(self, st: dict):
        k = self.k + 1
        cls = st["class"]
        addr = hexint(st["addr"])
        site = st["site"]
        for ln in st.get("pre_lines", []):
            self.lines.append("  " + self.subst(ln, k))
        call = st["call"]
        if "$guard" in call:
            if st.get("guard") != "decide":
                raise SpecError(
                    f"step {k}: `$guard` in the call needs "
                    f"'\"guard\": \"decide\"' (concrete-operand branch); "
                    f"otherwise derive the fact in pre_lines")
            if cls not in ("btaken", "bnottaken"):
                raise SpecError(
                    f"step {k}: guard=decide is for branch steps "
                    f"(class btaken/bnottaken), got {cls}")
            call = call.replace("$guard", "(by decide)")
        elif st.get("guard") == "decide":
            raise SpecError(
                f"step {k}: guard=decide set but no `$guard` in the call")
        call = self.subst(call, k)
        self.lines.append(
            f"  -- === step {k}: 0x{addr:08x} `{site}` ({cls}) ===")
        self.lines.append(
            f"  obtain ⟨σ{k}, i{k}, hs{k}, hi{k}, hG{k}, hmem{k}, hobs{k}⟩ :=")
        self.lines.append(
            f"    {site} {self.state} {self.tick} ({self.u_expr()}) "
            f"{bv64(addr)}\n      {call}")
        obs = OBS_FAM[cls]
        # PC
        if cls in ("alu", "sd", "sw", "sb", "bnottaken"):
            nxt = addr + 4
            self.lines.append(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some "
                f"({bv64(nxt)[1:-1]} : BitVec 64) := by\n"
                f"    have := obs_{obs}_pc hobs{k}\n"
                f"    rwa [show BitVec.addInt {bv64(addr)} 4 = "
                f"({bv64(nxt)[1:-1]} : BitVec 64) from by decide] at this")
            end_pc = bv64(nxt)[1:-1]
        elif cls in ("btaken", "j", "jal"):
            tgt = hexint(st["target"])
            imm = st["imm"]
            self.lines.append(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some "
                f"({bv64(tgt)[1:-1]} : BitVec 64) := by\n"
                f"    rw [obs_{obs}_pc hobs{k},\n"
                f"      show ({bv64(addr)[1:-1]} : BitVec 64) + "
                f"sign_extend (m := 64) ({imm}) = ({bv64(tgt)[1:-1]} : BitVec 64)"
                f" from by apply BitVec.eq_of_toNat_eq; decide]")
            end_pc = bv64(tgt)[1:-1]
        elif cls == "jr":
            pc_val = self.subst(st["pc_val"], k)
            pc_rw = self.subst(st["pc_rw"], k)
            self.lines.append(
                f"  have hpc{k} : σ{k}.regs.get? Register.PC = some {pc_val} "
                f":= by\n    rw [obs_jr_pc hobs{k}, {pc_rw}]")
            end_pc = pc_val
        else:
            raise SpecError(f"unknown class {cls}")
        self.end_pc = end_pc
        # rd
        rd = st.get("rd")
        rd_val = st.get("rd_val")
        if cls == "jal" and rd_val is None and rd is not None:
            ret = addr + 4
            rd_val = f"({bv64(ret)[1:-1]} : BitVec 64)"
            st.setdefault("rw", f"show BitVec.addInt {bv64(addr)} 4 = "
                                f"({bv64(ret)[1:-1]} : BitVec 64) from by decide")
        if rd is not None:
            rdfam = "jal" if cls == "jal" else "alu"
            dec5 = "(by decide) " * 5
            if st.get("rw"):
                self.lines.append(
                    f"  have hrd{k} : σ{k}.regs.get? Register.{rd} = some "
                    f"{rd_val} := by\n"
                    f"    have := obs_{rdfam}_rd hobs{k} {dec5.strip()}\n"
                    f"    rwa [{self.subst(st['rw'], k)}] at this")
            else:
                self.lines.append(
                    f"  have hrd{k} : σ{k}.regs.get? Register.{rd} = some "
                    f"{rd_val} :=\n"
                    f"    obs_{rdfam}_rd hobs{k} {dec5.strip()}")
        # pins
        self.emit_pins(k, cls, rd, rd_val,
                       st.get("track_rd", rd_val is not None))
        # minstret
        self.lines.append(
            f"  obtain ⟨vmi{k}, hmi{k}⟩ := obs_{obs}_minstret hobs{k}")
        # memory threading
        pred = self.spec["loaded_pred"]
        if cls in ("sd", "sw", "sb"):
            prev = self.mem_expr if self.mem_expr is not None else \
                self.spec["pre_bind"]["mem0"]
            key = self.subst(st["key"], k)
            src = self.subst(st["src_val"], k)
            if cls == "sb":
                new_mem = f"(({prev}).insert ({key}) ({src}))"
            else:
                fn, data = STORE_FN[cls]
                new_mem = f"{fn} ({prev}) ({key}) ({data} {src})"
            rws = [f"hmem{k}", "mem_afterNextPC"]
            pm = self.pv("memeq")
            if pm:
                rws.append(pm)
            if st.get("key_rw"):
                rws.append(self.subst(st["key_rw"], k))
            if st.get("data_rw"):
                rws.append(self.subst(st["data_rw"], k))
            self.lines.append(
                f"  have hmemE{k} : σ{k}.mem = {new_mem} := by\n"
                f"    rw [{', '.join(rws)}]")
            self.mem_expr = new_mem
            lv = st.get("loaded_via")
            if lv is None:
                raise SpecError(f"store step {k}: 'loaded_via' required")
            # $prev = previous loaded fact, transported to the accumulated
            # memory *expression* (the survival lemma peels the new write).
            prev_load = self.pv("hmem")
            prev_at_expr = f"({pm} ▸ {prev_load})" if pm else prev_load
            lv = self.subst(lv, k).replace("$prev", prev_at_expr)
            self.lines.append(
                f"  have hload{k} : {pred} σ{k}.mem := by\n"
                f"    rw [hmemE{k}]\n    exact {lv}")
        else:
            prev = self.mem_expr if self.mem_expr is not None else \
                self.spec["pre_bind"]["mem0"]
            pm = self.pv("memeq")
            if pm:
                self.lines.append(
                    f"  have hmemE{k} : σ{k}.mem = {prev} := by\n"
                    f"    rw [hmem{k}]; exact {pm}")
            else:
                self.lines.append(
                    f"  have hmemE{k} : σ{k}.mem = {prev} := hmem{k}")
            self.mem_expr = prev
            self.lines.append(
                f"  have hload{k} : {pred} σ{k}.mem := by\n"
                f"    rw [hmem{k}]; exact {self.pv('hmem')}")
        # ghost register frame
        if self.frame:
            tmpl = self.frame["tmpl"][cls]
            tmpl = tmpl.replace("$hobs", f"hobs{k}")
            if rd is not None:
                tmpl = tmpl.replace("$rd", rd)
            self.lines.append(
                f"  have hframe{k} : ∀ R : Register, {self.frame['pred']} R → "
                f"σ{k}.regs.get? R = {self.frame['rhs']} :=\n"
                f"    fun R hR => ({tmpl}).trans ({self.pv('hframe')} R hR)")
        # advance
        step = f"Steps.single hs{k}"
        self.chain = step if self.chain is None else \
            f"({self.chain}).trans ({step})"
        self.state, self.tick = f"σ{k}", f"i{k}"
        self.u_plus += 1
        self.k = k

    def emit_call_step(self, st: dict):
        k = self.k + 1
        callee = st["callee"]
        for ln in st.get("pre_lines", []):
            self.lines.append("  " + self.subst(ln, k))
        args = self.subst(st["args"], k)
        fields = ",\n       ".join(self.subst(f, k) for f in st["pre_fields"])
        self.lines.append(f"  -- === step {k}: call `{callee}` ===")
        self.lines.append(
            f"  obtain ⟨c{k}, hcs{k}, hcp{k}⟩ :=\n"
            f"    {callee} {args}\n"
            f"      ⟨{self.state}, {self.tick}, {self.u_expr()}⟩\n"
            f"      ⟨{fields}⟩")
        self.lines.append(
            f"  obtain {self.subst(st['post_obtain'], k)} := hcp{k}")
        # standard aliases at the call boundary
        self.lines.append(f"  have hG{k} := {st['post_good']}")
        self.lines.append(
            f"  have hpc{k} : c{k}.σ.regs.get? Register.PC = some "
            f"{st['pc_val']} := {st['post_pc']}")
        self.lines.append(f"  have hi{k} : c{k}.tick < 2 := {st['post_tick']}")
        self.lines.append(
            f"  obtain ⟨vmi{k}, hmi{k}⟩ := hG{k}.minstret")
        self.end_pc = st["pc_val"]
        # pins across the call
        drops = set(st.get("pins_drop", []))
        kept = [p for p in self.pins if p[0] not in drops]
        prev_hp = self.pv("hp")
        if len(kept) != len(self.pins):
            projs = [proj(prev_hp, i) for i, p in enumerate(self.pins)
                     if p[0] not in drops]
            self.lines.append(
                f"  have hq{k} : PinsHold {self.state} {pin_list(kept)} :=\n"
                f"    ⟨{', '.join(projs + ['trivial'])}⟩")
            src_hp = f"hq{k}"
        else:
            src_hp = prev_hp
        wset = st["write_set"]
        wlist = "[" + ", ".join(f"Register.{r}" for r in wset) + "]"
        adapter = ", ".join(f"hn Register.{r} (by decide)" for r in wset)
        transported = (
            f"pins_of_frame (W := {wlist})\n"
            f"      (fun R hn => {st['frame_hyp']} R ⟨{adapter}⟩) "
            f"(by rfl) {src_hp}")
        adds = st.get("pins_add", [])
        new_pins = [(a["reg"], a["val"]) for a in adds] + kept
        if adds:
            hyps = [a["hyp"] for a in adds]
            self.lines.append(
                f"  have hp{k} : PinsHold c{k}.σ {pin_list(new_pins)} :=\n"
                f"    ⟨{', '.join(hyps)}, {transported}⟩")
        else:
            self.lines.append(
                f"  have hp{k} : PinsHold c{k}.σ {pin_list(new_pins)} :=\n"
                f"    {transported}")
        self.pins = new_pins
        # memory / loaded threading (raw; segment-specific after a call)
        if st.get("mem_lines"):
            for ln in st["mem_lines"]:
                self.lines.append("  " + self.subst(ln, k))
            self.mem_expr = self.subst(st["mem_expr"], k)
        else:
            self.mem_expr = None       # no hmemE after the call
        if st.get("loaded_lines"):
            for ln in st["loaded_lines"]:
                self.lines.append("  " + self.subst(ln, k))
        else:
            raise SpecError(f"call step {k}: 'loaded_lines' required "
                            f"(hload{k} : <pred> c{k}.σ.mem)")
        if self.frame:
            if not st.get("frame_lines"):
                raise SpecError(f"call step {k}: 'frame_lines' required when "
                                f"a ghost frame is configured (hframe{k})")
            for ln in st["frame_lines"]:
                self.lines.append("  " + self.subst(ln, k))
        # advance
        self.chain = f"({self.chain}).trans hcs{k}"
        self.state, self.tick = f"c{k}.σ", f"c{k}.tick"
        self.u_base, self.u_plus = f"c{k}.steps", 0
        self.k = k

    # -- segst boundaries ----------------------------------------------------

    def _segst_payload(self, mem_rhs: str) -> str:
        """The SegSt payload `P : MState → Prop`: loaded ∧ mem-eq [∧ frame]."""
        parts = [f"{self.spec['loaded_pred']} σ.mem", f"σ.mem = {mem_rhs}"]
        if self.frame:
            parts.append(f"(∀ R : Register, {self.frame['pred']} R → "
                         f"σ.regs.get? R = {self.frame['rhs']})")
        return "fun σ => " + " ∧ ".join(parts)

    def _setup_segst(self):
        """Synthesize pre/pre_bind for `\"boundary\": \"segst\"` — the Pre is a
        `SegSt` instance and its destructuring is mechanical."""
        spec = self.spec
        if any(st["class"] == "call" for st in spec["steps"]):
            raise SpecError("boundary=segst: straight-line segments only "
                            "(no call steps — memory/loaded threading after a "
                            "call is segment-specific)")
        if "entry" not in spec:
            raise SpecError("boundary=segst: 'entry' (the pre PC) is required")
        mem_param = spec.get("mem_param", "m0")
        payload_pat = "⟨hloaded, hmemeq" + \
            (", hframe" if self.frame else "") + "⟩"
        spec["pre_bind"] = {
            "obtain": f"⟨hgood, hpc, hp0, ⟨vmi, hmi⟩, htick, {payload_pat}⟩",
            "good": "hgood", "pc": "hpc", "minstret_var": "vmi",
            "minstret": "hmi", "tick": "htick", "loaded": "hloaded",
            "mem0": mem_param, "memeq": "hmemeq",
        }
        if self.frame:
            self.frame["init"] = "hframe"
        spec["pre"] = (f"SegSt {bv64(hexint(spec['entry']))} "
                       f"{pin_list(self.pins)}\n      "
                       f"({self._segst_payload(mem_param)})")

    # -- whole file ----------------------------------------------------------

    def emit(self) -> str:
        spec = self.spec
        if self.segst:
            self._setup_segst()
        pb = spec["pre_bind"]
        header = file_header(spec)
        body: list[str] = []
        for d in spec.get("decls", []):
            body.append(d)
            body.append("")
        # theorem head
        params = list(spec["params"])
        if spec.get("post_abstract"):
            params.append("(Post : Config → Prop)")
            post = "Post"
        else:
            post = spec.get("post")   # segst: computed after the step run
        # run the steps first so hclose knows the final bundle / mem / pc
        self.lines = []
        self.lines.append("  intro c hPre")
        if "post_proof" not in spec and not self.segst:
            self.lines.append("  have hPre0 := hPre")
        self.lines.append(f"  obtain {pb['obtain']} := hPre")
        if not self.segst:
            self.lines.append(
                f"  have hp0 : PinsHold c.σ {pin_list(self.pins)} :=\n"
                f"    ⟨{', '.join(self.pin_hyps + ['trivial'])}⟩")
        for ln in spec.get("prelude", []):
            self.lines.append("  " + ln)
        had_call = False
        for st in spec["steps"]:
            if st["class"] == "call":
                self.emit_call_step(st)
                had_call = True
            else:
                self.emit_site_step(st)
        N = self.k
        cfg = f"⟨{self.state}, {self.tick}, {self.u_expr()}⟩"
        self.lines.append(
            f"  have hsteps{N} : Steps c {cfg} :=\n    {self.chain}")
        hclose_param = None
        if self.segst:
            # SegSt post: pins list / PC / memory computed by the threading;
            # the assembly is fully mechanical — zero holes.
            if self.mem_expr is None or "c.σ" in self.mem_expr:
                raise SpecError(
                    "boundary=segst: the accumulated memory expression must "
                    "be parameter-level (got "
                    f"{self.mem_expr!r}); lift store values to parameters")
            post = (f"SegSt ({self.end_pc}) {pin_list(self.pins)}\n      "
                    f"({self._segst_payload(self.mem_expr)})")
            payload = f"⟨hload{N}, hmemE{N}" + \
                (f", hframe{N}" if self.frame else "") + "⟩"
            self.lines.append(
                f"  exact ⟨{cfg}, hsteps{N},\n"
                f"    ⟨hG{N}, hpc{N}, hp{N}, ⟨vmi{N}, hmi{N}⟩, hi{N}, "
                f"{payload}⟩⟩")
        elif "post_proof" in spec:
            for ln in spec["post_proof"]:
                self.lines.append("  " + self.subst(ln, N))
        else:
            # hclose hypothesis parameter: everything mechanical is proven,
            # the segment-specific postcondition assembly is abstracted.
            clauses = [
                "GoodState σ' →",
                f"σ'.regs.get? Register.PC = some {self.end_pc} →",
                f"PinsHold σ' {pin_list(self.pins)} →",
                "(∃ v, σ'.regs.get? Register.minstret = some v) →",
                "i' < 2 →",
            ]
            args = [self.state, self.tick, self.u_expr(),
                    self.pv("hG"), self.pv("hpc"), self.pv("hp"),
                    f"⟨vmi{N}, hmi{N}⟩" if N else "sorry", self.pv("hi")]
            if self.mem_expr is not None and "c.σ" not in self.mem_expr:
                clauses.append(f"σ'.mem = {self.mem_expr} →")
                args.append(f"hmemE{N}")
            clauses.append(f"{spec['loaded_pred']} σ'.mem →")
            args.append(f"hload{N}")
            if self.frame:
                clauses.append(
                    f"(∀ R : Register, {self.frame['pred']} R → "
                    f"σ'.regs.get? R = {self.frame['rhs']}) →")
                args.append(self.pv("hframe"))
            for ex in spec.get("hclose_extra", []):
                clauses.append(f"({ex['type']}) →")
                args.append(ex["arg"])
            cl = "\n      ".join(clauses)
            hclose_param = (
                f"    (hclose : ∀ (c : Config), ({spec['pre']}) c →\n"
                f"      ∀ (σ' : MState) (i' u' : Nat),\n"
                f"      {cl}\n"
                f"      ({post}) ⟨σ', i', u'⟩)")
            self.lines.append(
                f"  exact ⟨{cfg}, hsteps{N},\n"
                f"    hclose c hPre0 {' '.join(args[:3])}\n"
                f"      {' '.join(args[3:])}⟩")
        head = [f"/-- {spec.get('doc', 'Generated segment theorem.')} -/",
                f"theorem {spec['theorem']}"]
        for p in params:
            head.append(f"    {p}")
        if hclose_param:
            head.append(hclose_param)
        head.append(f"    : Triple ({spec['pre']}) ({post}) := by")
        body.append("\n".join(head))
        body.extend(self.lines)
        ns = spec.get("namespace", "Vsa.Sim")
        return header + "\n" + "\n".join(body) + f"\n\nend {ns}\n"


# ---------------------------------------------------------------------------
# prologue front-end: frame table -> core spec (+ inline Pre/Post structures)

def regnum(reg: str) -> int:
    return int(reg[1:])


def build_prologue(fs: dict) -> dict:
    K = fs["frame_size"]
    imm = 0x1000 - K
    sext_lemma = fs.get("sext_lemma", SEXT_K[K])
    sp = fs.get("sp_reg", "x2")
    thm = fs["theorem"]
    pre_name = fs.get("pre_name", thm.title().replace("_", "") + "Pre")
    post_name = fs.get("post_name", thm.title().replace("_", "") + "Post")
    saves = fs["saves"]
    extras = fs.get("extra_steps", [])
    pred = fs["loaded_pred"]
    spdec = f"(vsp + sign_extend (m := 64) (0x{imm:03x}#12))"

    save_vals = {s["reg"]: f"v{regnum(s['reg'])}" for s in saves}
    save_params = " ".join(save_vals[s["reg"]] for s in saves)
    extra_pins = fs.get("extra_pins", [])
    params = [f"(vsp {save_params} : BitVec 64)"] + fs.get("extra_params", []) \
        + ["(m0 : Std.ExtHashMap Nat (BitVec 8))"]
    pnames = f"vsp {save_params} " + " ".join(fs.get("extra_param_names", [])) \
        + " m0"
    pnames = " ".join(pnames.split())

    # ---- Pre structure
    pre_fields = [
        ("good", "GoodState c.σ"),
        ("loaded", f"{pred} c.σ.mem"),
        ("pc", f"c.σ.regs.get? Register.PC = some "
               f"((0x{hexint(fs['entry']):08x}#64) : BitVec 64)"),
        ("sp", f"c.σ.regs.get? Register.{sp} = some vsp"),
    ]
    for s in saves:
        pre_fields.append((f"r_{s['reg']}",
                           f"c.σ.regs.get? Register.{s['reg']} = some "
                           f"{save_vals[s['reg']]}"))
    for p in extra_pins:
        pre_fields.append((f"r_{p['reg']}",
                           f"c.σ.regs.get? Register.{p['reg']} = some "
                           f"{p['val']}"))
    pre_fields += [
        ("minstret", "∃ v, c.σ.regs.get? Register.minstret = some v"),
        ("tick", "c.tick < 2"),
        ("sp_lo", f"0x80000000 + {K} ≤ vsp.toNat"),
        ("sp_hi", "vsp.toNat ≤ 0x100000000"),
        ("sp_win", f"tohostAddr + 16 + {K} ≤ vsp.toNat"),
        ("sp_align", "vsp.toNat % 8 = 0"),
        ("memeq", "c.σ.mem = m0"),
    ]
    pre_fields += [(f["name"], f["type"]) for f in fs.get("pre_extra", [])]

    # ---- steps
    steps = []
    spd = fs["sp_dec"]
    steps.append({
        "addr": spd["addr"], "site": spd["site"], "class": "alu",
        "rd": sp, "rd_val": spdec,
        "call": f"$vmi $v:{sp} $hG $hpc $hmi $pin:{sp} $hmem rfl $hi",
    })
    mem_expr_parts = []
    body_steps = sorted(
        [dict(s, _kind="save") for s in saves] +
        [dict(e, _kind="extra") for e in extras],
        key=lambda s: hexint(s["addr"]))
    later_offs = [s["off"] for s in body_steps if s["_kind"] == "save"]
    prelude = [
        "have htoh : tohostAddr = 0x8001ad00 := rfl",
        "have hvlt := vsp.isLt",
        f"have hspN : {spdec}.toNat = vsp.toNat - {K} :=",
        f"  ptr_sub_toNat vsp _ {K} {sext_lemma} (by omega)",
    ]
    offs = sorted({s["off"] for s in saves})
    for off in offs:
        prelude += [
            f"have hkey{off} : ({spdec} + sign_extend (m := 64) "
            f"(0x{off:03x}#12)).toNat = vsp.toNat - {K - off} := by",
            f"  rw [ptr_addoff {spdec} (0x{off:03x}#12) {off} (by decide) "
            f"(by rw [hspN]; omega), hspN]",
            "  omega",
        ]
    prelude += fs.get("extra_prelude", [])

    for s in body_steps:
        if s["_kind"] == "extra":
            steps.append({kk: v for kk, v in s.items() if kk != "_kind"})
            continue
        off = s["off"]
        reg = s["reg"]
        v = save_vals[reg]
        side = f"(by rw [hkey{off}]; omega)"
        steps.append({
            "addr": s["addr"], "site": s["site"], "class": "sd",
            "key": f"vsp.toNat - {K - off}", "key_rw": f"hkey{off}",
            "src_val": v,
            "call": (f"$vmi $v:{sp} $v:{reg} $hG $hpc $hmi $pin:{sp} "
                     f"$pin:{reg} $hmem rfl {side} {side} {side} {side} $hi"),
            "loaded_via": fs["loaded_store_via"],
        })
        mem_expr_parts.append((f"vsp.toNat - {K - off}", f"sdData_val {v}"))

    # simulate final bundle order to lay out the Post structure
    pins = [{"reg": sp, "val": "vsp", "hyp": "hsp0"}]
    for s in saves:
        pins.append({"reg": s["reg"], "val": save_vals[s["reg"]],
                     "hyp": f"hr_{s['reg']}"})
    for p in extra_pins:
        pins.append({"reg": p["reg"], "val": p["val"],
                     "hyp": f"hr_{p['reg']}"})
    order = [(p["reg"], p["val"]) for p in pins]

    def write_reg(reg, val):
        nonlocal order
        order = [(reg, val)] + [p for p in order if p[0] != reg]

    for st in steps:
        if st.get("rd") and st.get("rd_val"):
            write_reg(st["rd"], st["rd_val"])

    # accumulated final memory expression
    mem = "m0"
    for key, data in mem_expr_parts:
        mem = f"writeMap8 ({mem}) ({key}) ({data})"
    end_addr = max(hexint(s["addr"]) for s in body_steps) + 4

    # ---- Post structure
    post_fields = [
        ("good", "GoodState c.σ"),
        ("loaded", f"{pred} c.σ.mem"),
        ("pc", f"c.σ.regs.get? Register.PC = some "
               f"((0x{end_addr:08x}#64) : BitVec 64)"),
    ]
    for reg, val in order:
        post_fields.append((f"reg_{reg}",
                            f"c.σ.regs.get? Register.{reg} = some {val}"))
    for s in saves:
        post_fields.append(
            (f"slot_{s['reg']}",
             f"SlotHolds {spdec} 0x{s['off']:03x} {save_vals[s['reg']]} "
             f"c.σ.mem"))
    post_fields += [
        ("mem", f"c.σ.mem = {mem}"),
        ("minstret", "∃ v, c.σ.regs.get? Register.minstret = some v"),
        ("tick", "c.tick < 2"),
    ]

    def struct(name, fields):
        out = [f"/-- Generated (gen_segment.py --mode prologue). -/",
               f"structure {name}"]
        for p in params:
            out.append(f"    {p}")
        out.append("    (c : Config) : Prop where")
        for fn, ft in fields:
            out.append(f"  {fn} : {ft}")
        return "\n".join(out)

    # ---- Pre destructuring
    hyps = []
    for fn, _ in pre_fields:
        hyps.append({"good": "hgood", "loaded": "hload_pre", "pc": "hpc_pre",
                     "sp": "hsp0", "minstret": "⟨vmi0, hmi0⟩",
                     "tick": "htick0", "memeq": "hmemeq0"}.get(fn, "h" + fn))
    obtain = "⟨" + ", ".join(hyps) + "⟩"

    # ---- post proof
    N = len(steps)
    post_proof = []
    save_steps = [(i + 2, s) for i, s in enumerate(body_steps)
                  if s["_kind"] == "save"]  # step index of each save
    for j, (_, s) in enumerate(save_steps):
        off = s["off"]
        v = save_vals[s["reg"]]
        n_later = len(save_steps) - 1 - j
        term = f"slot_save _ _ _ _ _ _ hkey{off} rfl"
        for _ in range(n_later):
            term = (f"slot_survives_writeMap8 _ _ _ _ _ _ "
                    f"(by rw [hkey{off}]; omega)\n      ({term})")
        post_proof += [
            f"have hslot{off} : SlotHolds {spdec} 0x{off:03x} {v} "
            f"σ{N}.mem := by",
            f"  rw [hmemE{N}]",
            f"  exact {term}",
        ]
    pin_projs = [proj(f"hp{N}", i) for i in range(len(order))]
    fields_proof = ([f"hG{N}", f"hload{N}", f"hpc{N}"] + pin_projs +
                    [f"hslot{s['off']}" for s in saves] +
                    [f"hmemE{N}", f"⟨vmi{N}, hmi{N}⟩", f"hi{N}"])
    post_proof += [
        f"refine ⟨⟨σ{N}, i{N}, c.steps{' + 1' * N}⟩, hsteps{N}, ?_⟩",
        f"exact ⟨{', '.join(fields_proof)}⟩",
    ]

    return {
        "theorem": thm,
        "doc": fs.get("doc", f"Generated prologue segment "
                             f"(frame {K}, {len(saves)} spills)."),
        "namespace": fs.get("namespace", "Vsa.Sim"),
        "imports": fs["imports"],
        "decls": [struct(pre_name, pre_fields), struct(post_name, post_fields)],
        "params": params,
        "pre": f"{pre_name} {pnames}",
        "post": f"{post_name} {pnames}",
        "loaded_pred": pred,
        "pre_bind": {
            "obtain": obtain, "good": "hgood", "pc": "hpc_pre",
            "minstret_var": "vmi0", "minstret": "hmi0", "tick": "htick0",
            "loaded": "hload_pre", "mem0": "m0", "memeq": "hmemeq0",
        },
        "pins": pins,
        "prelude": prelude,
        "steps": steps,
        "post_proof": post_proof,
    }


# ---------------------------------------------------------------------------
# epilogue front-end

def build_epilogue(fs: dict) -> dict:
    K = fs["frame_size"]
    sp = fs.get("sp_reg", "x2")
    thm = fs["theorem"]
    pred = fs["loaded_pred"]
    pre_name = fs.get("pre_name", thm.title().replace("_", "") + "Pre")
    post_name = fs.get("post_name", thm.title().replace("_", "") + "Post")
    reloads = fs["reloads"]
    ra_var = next(r["var"] for r in reloads if r["reg"] == "x1")
    vals = {r["reg"]: r["var"] for r in reloads}
    vparams = " ".join(vals[r["reg"]] for r in reloads)
    params = [f"(vspd {vparams} : BitVec 64)"] + fs.get("extra_params", []) + \
        ["(m0 : Std.ExtHashMap Nat (BitVec 8))"]
    pnames = " ".join((f"vspd {vparams} " +
                       " ".join(fs.get("extra_param_names", [])) +
                       " m0").split())
    inc_imm = fs["sp_inc"].get("imm", f"0x{K:03x}")
    sp_restored = f"(vspd + sign_extend (m := 64) ({inc_imm}#12))"

    pre_fields = [
        ("good", "GoodState c.σ"),
        ("loaded", f"{pred} c.σ.mem"),
        ("pc", f"c.σ.regs.get? Register.PC = some "
               f"((0x{hexint(fs['entry']):08x}#64) : BitVec 64)"),
        ("sp", f"c.σ.regs.get? Register.{sp} = some vspd"),
        ("minstret", "∃ v, c.σ.regs.get? Register.minstret = some v"),
        ("tick", "c.tick < 2"),
        ("sp_lo", "0x80000000 ≤ vspd.toNat"),
        ("sp_hi", f"vspd.toNat + {K} ≤ 0x100000000"),
        ("sp_win", "tohostAddr + 16 ≤ vspd.toNat"),
        ("sp_align", "vspd.toNat % 8 = 0"),
        (f"ra_align", f"{ra_var}.toNat % 4 = 0"),
        ("memeq", "c.σ.mem = m0"),
    ]
    for r in reloads:
        pre_fields.append(
            (f"slot_{r['reg']}",
             f"SlotHolds vspd 0x{r['off']:03x} {r['var']} m0"))
    pre_fields += [(f["name"], f["type"]) for f in fs.get("pre_extra", [])]

    prelude = [
        "have htoh : tohostAddr = 0x8001ad00 := rfl",
        "have hvlt := vspd.isLt",
    ]
    for r in reloads:
        off = r["off"]
        prelude += [
            f"have hkey{off} : (vspd + sign_extend (m := 64) "
            f"(0x{off:03x}#12)).toNat = vspd.toNat + {off} :=",
            f"  ptr_addoff vspd (0x{off:03x}#12) {off} (by decide) (by omega)",
        ]
    prelude += fs.get("extra_prelude", [])

    steps = []
    for kk, r in enumerate(reloads, 1):
        off, reg, v = r["off"], r["reg"], r["var"]
        bs = " ".join(f"((sdData_val {v}).extractLsb' {8 * j} 8)"
                      for j in range(8))
        hbs = " ".join(f"hb{kk}_{j}" for j in range(8))
        side = f"(by rw [hkey{off}]; omega)"
        sl_src = f"hslot_{reg}" if kk == 1 else f"hslot_{reg}"
        pre_lines = [
            (f"have hsl$k : SlotHolds vspd 0x{off:03x} {v} $sigma.mem := by"),
            (f"  rw [$memeq]; exact {sl_src}"),
            (f"obtain ⟨{', '.join(f'hb{kk}_{j}' for j in range(8))}⟩ :="),
            (f"  slot_reload_bytes vspd 0x{off:03x} {v} $sigma.mem hsl$k"),
        ]
        rd_val_raw = ("(sign_extend (m := 64) (((((((("
                      f"(sdData_val {v}).extractLsb' 56 8).append "
                      f"((sdData_val {v}).extractLsb' 48 8)).append "
                      f"((sdData_val {v}).extractLsb' 40 8)).append "
                      f"((sdData_val {v}).extractLsb' 32 8)).append "
                      f"((sdData_val {v}).extractLsb' 24 8)).append "
                      f"((sdData_val {v}).extractLsb' 16 8)).append "
                      f"((sdData_val {v}).extractLsb' 8 8)).append "
                      f"((sdData_val {v}).extractLsb' 0 8) "
                      ": BitVec (8 * 8)))")
        del rd_val_raw  # rd_val after `slot_reassemble` rewrite is just v
        steps.append({
            "addr": r["addr"], "site": r["site"], "class": "alu",
            "rd": reg, "rd_val": v, "rw": f"slot_reassemble {v}",
            "pre_lines": pre_lines,
            "call": (f"$vmi $v:{sp} {bs} $hG $hpc $hmi $pin:{sp} $hmem rfl "
                     f"{side} {side} (Or.inr {side}) {side} {hbs} $hi"),
        })
    inc = fs["sp_inc"]
    steps.append({
        "addr": inc["addr"], "site": inc["site"], "class": "alu",
        "rd": sp, "rd_val": sp_restored,
        "call": f"$vmi $v:{sp} $hG $hpc $hmi $pin:{sp} $hmem rfl $hi",
    })
    ret = fs["ret"]
    steps.append({
        "addr": ret["addr"], "site": ret["site"], "class": "jr",
        "pc_val": ra_var,
        "pc_rw": f"ret_tgt {ra_var} hra_align",
        "call": (f"$vmi $v:x1 $hG $hpc $hmi $pin:x1 $hmem rfl "
                 f"(by rw [ret_tgt {ra_var} hra_align]; exact hra_align) $hi"),
    })

    # final bundle order
    order = [(sp, "vspd")]
    for r in reloads:
        order = [(r["reg"], r["var"])] + order
    order = [(sp, sp_restored)] + [p for p in order if p[0] != sp]

    post_fields = [
        ("good", "GoodState c.σ"),
        ("loaded", f"{pred} c.σ.mem"),
        ("pc", f"c.σ.regs.get? Register.PC = some {ra_var}"),
    ]
    for reg, val in order:
        post_fields.append((f"reg_{reg}",
                            f"c.σ.regs.get? Register.{reg} = some {val}"))
    post_fields += [
        ("mem", "c.σ.mem = m0"),
        ("minstret", "∃ v, c.σ.regs.get? Register.minstret = some v"),
        ("tick", "c.tick < 2"),
    ]

    def struct(name, fields):
        out = [f"/-- Generated (gen_segment.py --mode epilogue). -/",
               f"structure {name}"]
        for p in params:
            out.append(f"    {p}")
        out.append("    (c : Config) : Prop where")
        for fn, ft in fields:
            out.append(f"  {fn} : {ft}")
        return "\n".join(out)

    hyps = []
    for fn, _ in pre_fields:
        hyps.append({"good": "hgood", "loaded": "hload_pre", "pc": "hpc_pre",
                     "sp": "hsp0", "minstret": "⟨vmi0, hmi0⟩",
                     "tick": "htick0", "memeq": "hmemeq0"}.get(fn, "h" + fn))
    obtain = "⟨" + ", ".join(hyps) + "⟩"

    N = len(steps)
    pin_projs = [proj(f"hp{N}", i) for i in range(len(order))]
    post_proof = [
        f"refine ⟨⟨σ{N}, i{N}, c.steps{' + 1' * N}⟩, hsteps{N}, ?_⟩",
        f"exact ⟨hG{N}, hload{N}, hpc{N}, {', '.join(pin_projs)}, "
        f"hmemE{N}, ⟨vmi{N}, hmi{N}⟩, hi{N}⟩",
    ]

    return {
        "theorem": thm,
        "doc": fs.get("doc", f"Generated epilogue segment (frame {K})."),
        "namespace": fs.get("namespace", "Vsa.Sim"),
        "imports": fs["imports"],
        "decls": [struct(pre_name, pre_fields), struct(post_name, post_fields)],
        "params": params,
        "pre": f"{pre_name} {pnames}",
        "post": f"{post_name} {pnames}",
        "loaded_pred": pred,
        "pre_bind": {
            "obtain": obtain, "good": "hgood", "pc": "hpc_pre",
            "minstret_var": "vmi0", "minstret": "hmi0", "tick": "htick0",
            "loaded": "hload_pre", "mem0": "m0", "memeq": "hmemeq0",
        },
        "pins": [{"reg": sp, "val": "vspd", "hyp": "hsp0"}],
        "prelude": prelude,
        "steps": steps,
        "post_proof": post_proof,
    }


# ---------------------------------------------------------------------------
# loop mode: whole Triple.loop instantiation (Spec18/StrcpySpec loop layer)

def emit_loop(spec: dict) -> str:
    for req in ("params", "args", "names", "head", "done", "body_lemma",
                "back_lemma", "done_lemma", "bound", "mu_reg", "mu_field",
                "done_mu_field", "mu_expr", "mu_done_expr", "mu_head_proof",
                "mu_done_proof"):
        if req not in spec:
            raise SpecError(f"loop spec: missing field '{req}'")
    nm = spec["names"]
    for req in ("at_head", "loop_inv", "loop_mu", "loopmu_head", "loop_body",
                "loop_to_done"):
        if req not in nm:
            raise SpecError(f"loop spec: missing names.{req}")
    args = spec["args"]
    bound = spec["bound"]
    done = spec["done"]
    binders = "\n".join(f"    {p}" for p in spec["params"])

    def head(iv: str) -> str:
        return spec["head"].replace("$i", iv)

    def mu(iv: str) -> str:
        return spec["mu_expr"].replace("$i", iv)

    body_app = spec["body_lemma"].replace("$i", "i")
    back_app = spec["back_lemma"].replace("$i", "i").replace("$hlt", "hlt")
    done_app = spec["done_lemma"].replace("$i", "i").replace("$heq", "hdone")
    mu_head_proof = "\n".join("  " + ln for ln in spec["mu_head_proof"])
    mu_done_proof = "\n".join("      " + ln for ln in spec["mu_done_proof"])
    body_prelude = "".join("  " + ln + "\n"
                           for ln in spec.get("body_prelude", []))

    decls: list[str] = []
    decls.append(f"""/-- Generated loop head (= the loop guard `B`): at iteration `i < {bound}`
of `{spec['head']}`. -/
def {nm['at_head']}
{binders}
    (c : Config) : Prop :=
  ∃ i, i < {bound} ∧ ({head('i')}) c""")

    decls.append(f"""/-- Generated loop invariant `I`: at the head, or done. -/
def {nm['loop_inv']}
{binders}
    (c : Config) : Prop :=
  {nm['at_head']} {args} c ∨ ({done}) c""")

    decls.append(f"""/-- Generated loop measure over register `{spec['mu_reg']}`. -/
def {nm['loop_mu']} (c : Config) : Nat :=
  2^64 - ((c.σ.regs.get? Register.{spec['mu_reg']}).getD (0#64)).toNat""")

    decls.append(f"""/-- At head iteration `i`, `{nm['loop_mu']} = {spec['mu_expr']}`. -/
theorem {nm['loopmu_head']}
{binders}
    (i : Nat) (c : Config)
    (hSt : ({head('i')}) c) : {nm['loop_mu']} c = {mu('i')} := by
  simp only [{nm['loop_mu']}, hSt.{spec['mu_field']}, Option.getD_some]
{mu_head_proof}""")

    decls.append(f"""/-- **Loop body** (generated): one iteration (`{spec['body_lemma'].split()[0]}` then the
back-edge/done branch) re-establishes `{nm['loop_inv']}` strictly decreasing
`{nm['loop_mu']}`. -/
theorem {nm['loop_body']}
{binders}
    (k : Nat) :
    Triple (fun c => {nm['loop_inv']} {args} c ∧ {nm['at_head']} {args} c ∧ {nm['loop_mu']} c = k)
           (fun c => {nm['loop_inv']} {args} c ∧ {nm['loop_mu']} c < k) := by
  intro c hc
  obtain ⟨_, ⟨i, hilt, hSt⟩, hmu⟩ := hc
  have hmu_eq : {nm['loop_mu']} c = {mu('i')} :=
    {nm['loopmu_head']} {args} i c hSt
  rw [hmu_eq] at hmu
{body_prelude}  obtain ⟨c1, hs1, hSt1c⟩ := {body_app} c hSt
  by_cases hdone : i + 1 = {bound}
  · -- exit: fall through to the done state
    obtain ⟨c2, hs2, hD⟩ := {done_app} c1 hSt1c
    refine ⟨c2, hs1.trans hs2, Or.inr hD, ?_⟩
    have hmu2 : {nm['loop_mu']} c2 = {spec['mu_done_expr']} := by
      simp only [{nm['loop_mu']}, hD.{spec['done_mu_field']}, Option.getD_some]
{mu_done_proof}
    rw [hmu2, ← hmu]; omega
  · -- back-edge: loop to head (i+1)
    have hlt : i + 1 < {bound} := by omega
    obtain ⟨c2, hs2, hSt2⟩ := {back_app} c1 hSt1c
    refine ⟨c2, hs1.trans hs2, Or.inl ⟨i + 1, hlt, hSt2⟩, ?_⟩
    have hmu2 : {nm['loop_mu']} c2 = {mu('(i + 1)')} :=
      {nm['loopmu_head']} {args} (i + 1) c2 hSt2
    rw [hmu2, ← hmu]; omega""")

    decls.append(f"""/-- The loop runs to the done state (generated `Triple.loop` instantiation). -/
theorem {nm['loop_to_done']}
{binders}
    : Triple ({nm['loop_inv']} {args}) ({done}) := by
  have hloop := Triple.loop (I := {nm['loop_inv']} {args})
    (B := {nm['at_head']} {args}) {nm['loop_mu']} ({nm['loop_body']} {args})
  refine hloop.seq ?_
  intro c hc
  obtain ⟨hI, hnB⟩ := hc
  rcases hI with hHead | hDone
  · exact absurd hHead hnB
  · exact ⟨c, .refl c, hDone⟩""")

    ns = spec.get("namespace", "Vsa.Sim")
    return file_header(spec) + "\n" + "\n\n".join(decls) + f"\n\nend {ns}\n"


# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(
        description=__doc__,
        formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("spec", type=Path, help="segment-spec JSON")
    ap.add_argument("-o", "--output", type=Path, required=True)
    ap.add_argument("--mode", required=True,
                    choices=["straight", "prologue", "epilogue", "call", "loop"])
    ap.add_argument("--emit-spec", type=Path, default=None,
                    help="also dump the expanded core spec (front-end modes)")
    args = ap.parse_args()

    spec_text = args.spec.read_text()
    if "TODO" in spec_text:
        todo_lines = [f"  line {i}: {ln.strip()}"
                      for i, ln in enumerate(spec_text.splitlines(), 1)
                      if "TODO" in ln]
        print("error: the spec contains TODO placeholders (a "
              "disasm_to_segment.py draft?) — fill them first:\n"
              + "\n".join(todo_lines[:20])
              + ("\n  ..." if len(todo_lines) > 20 else ""),
              file=sys.stderr)
        return 1
    fs = json.loads(spec_text)
    if args.mode == "loop":
        try:
            out = emit_loop(fs)
        except SpecError as e:
            print(f"error: {e}", file=sys.stderr)
            return 1
        args.output.write_text(out)
        print(f"wrote {args.output} (loop layer "
              f"{fs['names']['at_head']} … {fs['names']['loop_to_done']})")
        return 0
    if args.mode == "prologue":
        spec = build_prologue(fs)
    elif args.mode == "epilogue":
        spec = build_epilogue(fs)
    else:
        spec = fs
        if args.mode == "call" and not any(
                s["class"] == "call" for s in spec["steps"]):
            print("error: --mode call requires a step of class 'call'",
                  file=sys.stderr)
            return 1
    if args.emit_spec:
        args.emit_spec.write_text(json.dumps(spec, indent=2, ensure_ascii=False))
    try:
        out = SegmentEmitter(spec).emit()
    except SpecError as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    args.output.write_text(out)
    nsteps = len(spec["steps"])
    closing = ("segst (auto-assembled)" if spec.get("boundary") == "segst"
               else "post_proof" if "post_proof" in spec else "hclose")
    print(f"wrote {args.output} ({spec['theorem']}, {nsteps} steps, "
          f"{closing} closing)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
