
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
QEMU_EMULATOR=${HOME}/cheri/build/qemu-build/qemu-system-riscv64cheri

TEST_ASMS:=$(wildcard test_*.s)
TEST_OBJS:=$(TEST_ASMS:.s=.o)
TEST_ELFS:=$(TEST_ASMS:.s=.elf)
TEST_SAIL_OUTS:=$(TEST_ASMS:.s=.sail_out)
TEST_QEMU_OUTS:=$(TEST_ASMS:.s=.qemu_out)

%.o: %.s epilogue.s
	${AS} -triple=riscv64 -mattr=+xcheri,xcherimemversion -filetype=obj -o $@ $<

%.elf: %.o baremetal.ld
	${LD} -T baremetal.ld -o $@ $<

${SAIL_EMULATOR}:
	$(MAKE) -C ../.. csim

%.sail_out: %.elf ${SAIL_EMULATOR}
	${SAIL_EMULATOR} $< >$@ 2>&1

%.qemu_out: %.elf ${QEMU_EMULATOR}
	(${QEMU_EMULATOR} -machine spike -d instr -bios $< >$@ 2>&1 \
	&& echo SUCCESS >> $@) \
	|| echo FAILURE >> $@


.PHONY: run_sail
run_sail: ${TEST_SAIL_OUTS}
	@echo "Sail Results:"
	@echo -n 'Passes: '
	@grep -l SUCCESS ${TEST_SAIL_OUTS} || echo none
	@echo -n 'Failures: '
	@grep -l FAILURE ${TEST_SAIL_OUTS} || echo none
	@echo -n 'Missing result: '
	@grep -L 'SUCCESS\|FAILURE' ${TEST_SAIL_OUTS} && echo none

.PHONY: run_qemu
run_qemu: ${TEST_QEMU_OUTS}
	@echo "Qemu Results:"
	@echo -n 'Passes: '
	@grep -l SUCCESS ${TEST_QEMU_OUTS} || echo none
	@echo -n 'Failures: '
	@grep -l FAILURE ${TEST_QEMU_OUTS} || echo none
	@echo -n 'Missing result: '
	@grep -L 'SUCCESS\|FAILURE' ${TEST_QEMU_OUTS} && echo none

.PHONY: run
run: run_sail run_qemu

.PHONY: clean
clean:
	rm -f ${TEST_OBJS} ${TEST_ELFS} ${TEST_SAIL_OUTS} ${TEST_QEMU_OUTS}