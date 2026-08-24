/* Minimal startup for bare-metal RISC-V under qemu-system-riscv64
 * (-machine virt -bios none). Sets up gp/sp, clears .bss, and calls
 * main with argc=0 -- main fetches the real command line over
 * semihosting (see main.c / semihost.c). */
    .section .text.init
    .globl _start
_start:
.option push
.option norelax
    la      gp, __global_pointer$
.option pop
    la      sp, __stack_top
    /* clear .bss (linker script guarantees 8-byte alignment) */
    la      t0, __bss_start
    la      t1, __bss_end
1:  bgeu    t0, t1, 2f
    sd      zero, 0(t0)
    addi    t0, t0, 8
    j       1b
2:
    li      a0, 0
    li      a1, 0
    call    main
    tail    exit
