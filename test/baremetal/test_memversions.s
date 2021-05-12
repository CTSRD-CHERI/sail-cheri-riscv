# Basic test of CHERI memory versioning instructions

.include "prelude.s"

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

    # Set version on cs1 to 1, then get it and check it stuck
    li t0, 1
    CSetVersion cs1, csp, t0
    CGetVersion t2, cs1
    bne t0, t2, fail

    # Attempt to set version on cs1 again, should throw an exception
    expect_cheri_exception "csetversion ct2, cs1, t0", CapEx_VersionViolation, REG_S1

    # Attempt load version of unversioned granule
    la t0, testdata
    CSetOffset cs1, csp, t0
    CLoadVersion t0, (cs1)
    # expect default memory version of 0
    bnez t0, fail

    # Set version of testdata to 2
    li t0, 2
    CStoreVersion t0, (cs1)
    CLoadVersion  t3, (cs1)
    # Check loaded version matches stored
    bne t0, t3, fail

    # Attempt store and load to versioned memory via unversioned cap
    # permitted because cs1 is unversioned
    li t0, 5
    sw.cap t0, (cs1)
    lw.cap t3, (cs1)
    # check loaded stored thing
    bne t0, t3, fail

    # Attempt to store / load to versioned memory via versioned cap
    # set version of cr2 to match memory
    li t0, 2
    CSetVersion ct2, cs1, t0
    # permitted because ct2 has correct version
    sw.cap t0, (ct2)
    lw.cap t3, (ct2)
    bne t0, t3, fail

    # Attempt to store / load to versioned memory via versioned cap
    # with incorrect version (should throw exception)
    li t0, 3
    CSetVersion cs2, cs1, t0
    # not-permitted because cs1 has incorrect version
    expect_exception "sw.cap t0, (cs2)", 0x1d
    # load again via the unversioned cap to check that memory is unchanged
    lw.cap t1, (cs1)
    li t0, 2
    bne t0, t1, fail

    # Similarly load with incorrect version should raise exception
    li s3, 1
    expect_exception "lw.cap s3, (cs2)", 0x1d
    # check that load did not affect register
    li t0, 1
    bne s3, t0, fail

    # decrement version of testdata to 1
    CAmoCDecVersion t0, (cs1), ct2
    li t3, 1
    # expect 1 (success)
    bne t0, t3, fail

    # attempt to decrement with incorrect version
    CAmoCDecVersion t0, (cs1), ct2
    li t3, 0
    # expect 0 (failure)
    bne t0, t3, fail

    # decrement version testdata to 0
    li t3, 1
    CSetVersion ct2, cs1, t3
    CAmoCDecVersion t0, (cs1), ct2
    li t3, -1
    # expect -1 (success but reached zero)
    bne t0, t3, fail

.include "epilogue.s"