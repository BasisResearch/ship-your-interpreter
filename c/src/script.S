/* Embeds the While script named by SCRIPT_PATH (a quoted string set from
 * the Makefile) into the image. HTIF builds have no filesystem to load a
 * script from, so main() runs this blob instead. */
    .section .rodata
    .globl _script_start
_script_start:
    .incbin SCRIPT_PATH
    .byte 0
