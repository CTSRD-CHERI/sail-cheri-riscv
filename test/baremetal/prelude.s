
# Symbolic register names
.set REG_ZERO, 0
.set REG_RA,   1
.set REG_SP,   2
.set REG_GP,   3
.set REG_TP,   4
.set REG_T0,   5
.set REG_T1,   6
.set REG_T2,   7
.set REG_FP,   8
.set REG_S1,   9
.set REG_A0,  10
.set REG_A1,  11
.set REG_A2,  12
.set REG_A3,  13
.set REG_A4,  14
.set REG_A5,  15
.set REG_A6,  16
.set REG_A7,  17
.set REG_S2,  18
.set REG_S3,  19
.set REG_S4,  20
.set REG_S5,  21
.set REG_S6,  22
.set REG_S7,  23
.set REG_S8,  24
.set REG_S9,  25
.set REG_S10, 26
.set REG_S11, 27
.set REG_T3,  28
.set REG_T4,  29
.set REG_T5,  30
.set REG_T6,  31

# CHERI exception numbering
.set CapEx_None                          , 0b00000
.set CapEx_LengthViolation               , 0b00001
.set CapEx_TagViolation                  , 0b00010
.set CapEx_SealViolation                 , 0b00011
.set CapEx_TypeViolation                 , 0b00100
.set CapEx_CallTrap                      , 0b00101
.set CapEx_ReturnTrap                    , 0b00110
.set CapEx_TSSUnderFlow                  , 0b00111
.set CapEx_UserDefViolation              , 0b01000
.set CapEx_InexactBounds                 , 0b01010
.set CapEx_UnalignedBase                 , 0b01011
.set CapEx_GlobalViolation               , 0b10000
.set CapEx_PermitExecuteViolation        , 0b10001
.set CapEx_PermitLoadViolation           , 0b10010
.set CapEx_PermitStoreViolation          , 0b10011
.set CapEx_PermitLoadCapViolation        , 0b10100
.set CapEx_PermitStoreCapViolation       , 0b10101
.set CapEx_PermitStoreLocalCapViolation  , 0b10110
.set CapEx_PermitSealViolation           , 0b10111
.set CapEx_AccessSystemRegsViolation     , 0b11000
.set CapEx_PermitCInvokeViolation        , 0b11001
.set CapEx_AccessCInvokeIDCViolation     , 0b11010
.set CapEx_PermitUnsealViolation         , 0b11011
.set CapEx_PermitSetCIDViolation         , 0b11100
.set CapEx_VersionViolation              , 0b11101

.macro expect_exception insn:req, cause:req, t0=t0, t1=t1
la t0, 2f
    csrw mtvec, \t0
    li \t0, 1
    1:
    \insn
    # should not reach here
    j fail
    2: # exception should land here
    # restore mtvec
    la \t0, fail
    csrw mtvec, \t0
    # check for correct mepc
    la   \t0, 1b
    csrr \t1, mepc
    bne  \t0, \t1, fail
    # check for correct cause
    csrr \t0, mcause
    li   \t1, \cause
    bne  \t0, \t1, fail
.endm

.macro expect_cheri_exception insn:req, ccause:req, reg:req, t0=t0, t1=t1
    expect_exception "\insn", 0x1c, \t0, \t1
    # check for correct capcause
    csrr \t0, mtval
    li   \t1, (\reg << 5) | (\ccause)
    bne  \t0, \t1, fail
.endm