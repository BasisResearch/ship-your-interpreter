    .section .rodata
    .globl _script_start
_script_start:
    .incbin SCRIPT_PATH
    .byte 0
