#!/usr/bin/env python3
"""Generate the byte-word / non-RVC facts block for env_get / env_set sites.

Emits, for each distinct instruction word, the `w_<word>_eg` and `nr_<word>_eg`
lemmas (byte reassembly = word; non-RVC bit pattern) that the `stepObs_*`
wrappers consume.  These are pure `decide` facts.  Site lemmas themselves are
hand-written against the templates (they differ per instruction class).
"""

# distinct words appearing in env_get / env_set (union)
words = [
    "0c050263", "fc010113", "01313c23", "01413823", "01513423", "02113c23",
    "02813823", "02913423", "03213023", "00050a13", "00058993", "00060a93",
    "000a2903", "09205063", "008a3483", "00000413", "0100006f", "00140413",
    "00848493", "07240463", "0004b503", "00098593", "238040ef", "16c040ef",
    "fe0514e3", "010a3783", "00141713", "00870733", "00371713", "00e787b3",
    "0007b703", "00100513", "00eab023", "0087b703", "00eab423", "0107b783",
    "00fab823", "03813083", "03013403", "02813483", "02013903", "01813983",
    "01013a03", "00813a83", "04010113", "00008067", "018a3a03", "f60a1ce3",
    "00000513", "fd1ff06f", "000ab583", "008ab603", "010ab683", "00b7b023",
    "00c7b423", "00d7b823",
]

def bytes_of(w):
    n = int(w, 16)
    return [(n >> (8 * k)) & 0xFF for k in range(4)]  # b0 b1 b2 b3

lines = []
for w in words:
    b0, b1, b2, b3 = bytes_of(w)
    app = f"((({b3:#04x}#8).append ({b2:#04x}#8)).append ({b1:#04x}#8)).append ({b0:#04x}#8)"
    lines.append(
        f"theorem w_{w}_eg : {app} = (0x{w}#32 : BitVec 32) := by\n"
        f"  apply BitVec.eq_of_toNat_eq; decide")
    lines.append(
        f"theorem nr_{w}_eg : Sail.BitVec.extractLsb ({app}) 1 0 = (0b11#2 : BitVec 2) := by\n"
        f"  apply BitVec.eq_of_toNat_eq; decide")

print("\n".join(lines))
