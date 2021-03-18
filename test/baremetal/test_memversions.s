# Basic test of CHERI memory versioning instructions

.data
.align 4
testdata:
.fill 16

.text
.globl _start
_start:
    # configure mtvec so that any exception results in immediate failure
    la t0, fail
    csrw mtvec, t0

    # Fetch the default cap in csp
    cspecialrw  csp, ddc, cnull

    # Default cap has version zero
    CGetVersion t0, csp
    bnez t0, fail

    # Set version on ct1 to 1, then get it and check it stuck
    li t0, 1
    CSetVersion ct1, csp, t0
    CGetVersion t2, ct1
    bne t0, t2, fail

    # Attempt load version of unversioned granule
    la t0, testdata
    CSetOffset ct1, csp, t0
    CLoadVersion t0, (ct1)
    # expect default memory version of 0
    bnez t0, fail

    # Set version of testdata to 2
    li t0, 2
    CStoreVersion t0, (ct1)
    CLoadVersion  t3, (ct1)
    # Check loaded version matches stored
    bne t0, t3, fail

    # Attempt store and load to versioned memory via unversioned cap
    # permitted because ct1 is unversioned
    li t0, 5
    sw.cap t0, (ct1)
    lw.cap t3, (ct1)
    # check loaded stored thing
    bne t0, t3, fail

    # Attempt to store / load to versioned memory via versioned cap
    # set version of cr2 to match memory
    li t0, 2
    CSetVersion ct2, ct1, t0
    # permitted because ct2 has correct version
    sw.cap t0, (ct2)
    lw.cap t3, (ct2)
    bne t0, t3, fail

    # decrement version of testdata to 1
    CAmoCDecVersion t0, (ct1), ct2
    li t3, 1
    # expect 1 (success)
    bne t0, t3, fail

    # attempt to decrement with incorrect version
    CAmoCDecVersion t0, (ct1), ct2
    li t3, 0
    # expect 0 (failure)
    bne t0, t3, fail

    # decrement version testdata to 0
    li t3, 1
    CSetVersion ct2, ct1, t3
    CAmoCDecVersion t0, (ct1), ct2
    li t3, -1
    # expect -1 (success but reached zero)
    bne t0, t3, fail

.include "epilogue.s"