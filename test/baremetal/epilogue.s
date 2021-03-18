# This file should be .include d at the end of a test. If execution falls 
# through to here, then we exit with success. fail is provided for branching 
# to on test failure and tohost section allows communication wiht host.

success:
# Write 1 to tohost, meaning exit with code 0
    li t0, 1
    sw t0, tohost, t1
# Spin until termination.
1:  j 1b

.align 2
fail:
# Write 3 to tohost, meaning exit with code 1  (lsb=1 means exit, upper bits=exit code).
    li t0, 3
    sw t0, tohost, t1
# Spin until terminatation
1:  j 1b

.section ".tohost", "aw", @progbits
.align 6
.globl tohost
tohost:
    .dword 0
.align 6
.globl fromhost
fromhost: 
    .dword 0
