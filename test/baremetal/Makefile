
# Attempt to get rid of built in rules
MAKEFLAGS += --no-builtin-rules

# Tell make not to delete intermediate files
.SECONDARY:

.PHONY: default
default: run

SDK=${HOME}/cheri/output/sdk
LD=${SDK}/bin/ld
AS=${SDK}/bin/llvm-mc
CLANG=${SDK}/bin/clang
SAIL_EMULATOR=../../c_emulator/cheri_riscv_sim_RV64

TEST_ASMS:=$(wildcard test_*.s)
TEST_OBJS:=$(TEST_ASMS:.s=.o)
TEST_ELFS:=$(TEST_ASMS:.s=.elf)
TEST_OUTS:=$(TEST_ASMS:.s=.out)

%.o: %.s epilogue.s
	${AS} -triple=riscv64 -mattr=+xcheri,xcherimemversion -filetype=obj -o $@ $<

%.elf: %.o baremetal.ld
	${LD} -T baremetal.ld -o $@ $<

${SAIL_EMULATOR}:
	$(MAKE) -C ../.. csim

%.out: %.elf ${SAIL_EMULATOR}
	${SAIL_EMULATOR} $< >$@ 2>&1

.PHONY: run
run: ${TEST_OUTS}
	@echo -n 'Passes: '
	@grep -l SUCCESS ${TEST_OUTS} || echo none
	@echo -n 'Failures: '
	@grep -l FAILURE ${TEST_OUTS} || echo none
	@echo -n 'Missing result: '
	@grep -L 'SUCCESS\|FAILURE' ${TEST_OUTS} && echo none

.PHONY: clean
clean:
	rm -f ${TEST_OBJS} ${TEST_ELFS} ${TEST_OUTS}