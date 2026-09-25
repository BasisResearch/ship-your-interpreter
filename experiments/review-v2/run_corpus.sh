#!/bin/bash
S=${REVIEW_V2_WORK:-/tmp/review-v2-work}
EMU=${EMU:-$(dirname $0)/../../riscv-lean/lean_emulator/.lake/build/bin/lean_riscv_emulator}
run1() { n=$(basename $1 .elf); s=$(date +%s); $EMU $1 --trace-pcs $S/emu/empty.pcs --max-steps 60000000 > $S/emu/$n.out 2> $S/emu/$n.err; echo "$n rc=$? secs=$(( $(date +%s) - s ))" >> $S/emu/results.txt; }
export -f run1; export S EMU
: > $S/emu/results.txt
ls ${VSA_BOOT_WORK:-/Users/kirancodes/vsa-b3-work}/elfs/*.elf | xargs -P 8 -I{} bash -c 'run1 {}'
echo ALLDONE >> $S/emu/results.txt
