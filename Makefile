# Simplified makefile for CHERI.
# Default architecture to build for all and non-namespaced targets
ARCH ?= RV64

ifeq ($(ARCH),32)
  override ARCH := RV32
else ifeq ($(ARCH),64)
  override ARCH := RV64
endif

SAIL_RISCV_DIR=sail-riscv
SAIL_RISCV_MODEL_DIR=$(SAIL_RISCV_DIR)/model
SAIL_CHERI_MODEL_DIR=src

SAIL_RV32_XLEN := $(SAIL_RISCV_MODEL_DIR)/riscv_xlen32.sail
CHERI_CAP_RV32_IMPL := cheri_prelude_64.sail

SAIL_RV64_XLEN := $(SAIL_RISCV_MODEL_DIR)/riscv_xlen64.sail
CHERI_CAP_RV64_IMPL := cheri_prelude_128.sail

SAIL_XLEN = $(SAIL_$(ARCH)_XLEN) $(SAIL_RISCV_MODEL_DIR)/riscv_xlen.sail
SAIL_FLEN = $(SAIL_RISCV_MODEL_DIR)/riscv_flen_D.sail $(SAIL_RISCV_MODEL_DIR)/riscv_flen.sail
SAIL_VLEN = $(SAIL_RISCV_MODEL_DIR)/riscv_vlen.sail
CHERI_CAP_IMPL = $(CHERI_CAP_$(ARCH)_IMPL)


# Instruction sources, depending on target
SAIL_CHECK_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_addr_checks_common.sail \
                  $(SAIL_CHERI_MODEL_DIR)/cheri_addr_checks.sail

SAIL_DEFAULT_INST = $(SAIL_RISCV_MODEL_DIR)/riscv_insts_base.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_aext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zca.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_mext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_hints.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zicsr.sail \
                    ${SAIL_CHERI_MODEL_DIR}/cheri_csr_op.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zifencei.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_fext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zcf.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_dext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zcd.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zba.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zbb.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zbc.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zbs.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_svinval.sail \
                    $(SAIL_CHERI_MODEL_DIR)/cheri_insts_begin.sail \
                    $(SAIL_CHERI_MODEL_DIR)/cheri_insts.sail \
                    $(SAIL_CHERI_MODEL_DIR)/cheri_insts_cext.sail \
                    $(SAIL_CHERI_MODEL_DIR)/cheri_insts_zba.sail \
                    $(SAIL_CHERI_MODEL_DIR)/cheri_insts_end.sail
SAIL_SEQ_INST  = $(SAIL_DEFAULT_INST) $(SAIL_RISCV_MODEL_DIR)/riscv_jalr_seq.sail
SAIL_RMEM_INST = $(SAIL_DEFAULT_INST) $(SAIL_RISCV_MODEL_DIR)/riscv_jalr_rmem.sail $(SAIL_RISCV_MODEL_DIR)/riscv_insts_rmem.sail

# TODO: riscv_csr_end.sail here temporarily until the scattered definitions
# are moved from riscv_insts_zicsr.sail to more appropriate places.
SAIL_SEQ_INST_SRCS  = $(SAIL_RISCV_MODEL_DIR)/riscv_insts_begin.sail $(SAIL_SEQ_INST)  $(SAIL_RISCV_MODEL_DIR)/riscv_insts_end.sail $(SAIL_RISCV_MODEL_DIR)/riscv_csr_end.sail
SAIL_RMEM_INST_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_insts_begin.sail $(SAIL_RMEM_INST) $(SAIL_RISCV_MODEL_DIR)/riscv_insts_end.sail $(SAIL_RISCV_MODEL_DIR)/riscv_csr_end.sail

# System and platform sources
SAIL_SYS_SRCS += ${SAIL_CHERI_MODEL_DIR}/cheri_sys_regs_access.sail
SAIL_SYS_SRCS += ${SAIL_RISCV_MODEL_DIR}/riscv_sys_regs_access_common.sail
SAIL_SYS_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_sys_exceptions.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_sync_exception.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_zihpm.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_smcntrpmf.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_sscofpmf.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_zkr_control.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_zicntr_control.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_softfloat_interface.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_fdext_regs.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_fdext_control.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_pma.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_svpbmt.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_sys_control.sail

SAIL_VM_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_vmem_ptw.sail
SAIL_VM_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_pte_types.sail
SAIL_VM_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_vmem_pte_types_ext.sail
SAIL_VM_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_vmem_pte_validity_ext.sail
SAIL_VM_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_pte.sail
SAIL_VM_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_vmem_pte_ext.sail
SAIL_VM_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_tlb.sail
SAIL_VM_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_vmem.sail
SAIL_VM_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_access.sail

# Non-instruction sources
PRELUDE = $(SAIL_RISCV_MODEL_DIR)/prelude.sail \
          $(SAIL_RISCV_MODEL_DIR)/riscv_errors.sail \
          ${SAIL_RISCV_MODEL_DIR}/range_util.sail \
          $(SAIL_XLEN) \
          $(SAIL_FLEN) \
          $(SAIL_VLEN) \
          $(SAIL_CHERI_MODEL_DIR)/cheri_prelude.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_types.sail \
          $(SAIL_CHERI_MODEL_DIR)/$(CHERI_CAP_IMPL) \
          $(SAIL_RISCV_MODEL_DIR)/prelude_mem_addrtype.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_mem_metadata.sail \
          $(SAIL_RISCV_MODEL_DIR)/prelude_mem.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_cap_common.sail

SAIL_REGS_SRCS = $(SAIL_CHERI_MODEL_DIR)/cheri_reg_type.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_freg_type.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_vmem_types.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_regs.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_sstc.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_sys_regs_types.sail \
                 ${SAIL_CHERI_MODEL_DIR}/cheri_sys_regs_envcfg.sail \
                 ${SAIL_CHERI_MODEL_DIR}/cheri_sys_regs_seccfg.sail \
                 ${SAIL_CHERI_MODEL_DIR}/cheri_sys_regs_xstatus.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_sys_regs.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_pmp_regs.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_pmp_control.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_sys_regs.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_regs.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_pc_access.sail

SAIL_REGS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_vreg_type.sail \
                  $(SAIL_RISCV_MODEL_DIR)/riscv_vext_regs.sail

SAIL_ARCH_SRCS = $(PRELUDE) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_types_common.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_riscv_types.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_extensions.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_types.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_csr_begin.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_convert_invalid_addr.sail \
                 $(SAIL_REGS_SRCS) \
                 $(SAIL_SYS_SRCS) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_platform.sail \
                 $(SAIL_CHECK_SRCS) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_mem.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_mem.sail \
                 $(SAIL_VM_SRCS)

SAIL_ARCH_RVFI_SRCS = \
                 $(PRELUDE) \
                 $(SAIL_RISCV_MODEL_DIR)/rvfi_dii.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_types_common.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_riscv_types.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_extensions.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_types.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_csr_begin.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_convert_invalid_addr.sail \
                 $(SAIL_REGS_SRCS) \
                 $(SAIL_SYS_SRCS) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_platform.sail \
                 $(SAIL_CHECK_SRCS) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_mem.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_mem.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_csr_ext.sail \
                 $(SAIL_VM_SRCS)

SAIL_STEP_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_step_common.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_step_ext.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_decode_ext.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_fetch.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_step.sail

RVFI_STEP_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_step_common.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_step_ext.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_step_rvfi.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_decode_ext.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_fetch_rvfi.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_step.sail

# Control inclusion of 64-bit only riscv_analysis
SAIL_RV32_OTHER_SRCS     = $(SAIL_STEP_SRCS)
SAIL_RV32_OTHER_COQ_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_termination_common.sail \
                           $(SAIL_RISCV_MODEL_DIR)/riscv_termination_rv32.sail

SAIL_RV64_OTHER_SRCS     = $(SAIL_STEP_SRCS)
SAIL_RV64_OTHER_COQ_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_termination_common.sail \
                           $(SAIL_RISCV_MODEL_DIR)/riscv_termination_rv64.sail

SAIL_OTHER_SRCS     = $(SAIL_$(ARCH)_OTHER_SRCS)
SAIL_OTHER_COQ_SRCS = $(SAIL_$(ARCH)_OTHER_COQ_SRCS)


PRELUDE_SRCS   = $(PRELUDE)
SAIL_SRCS      = $(SAIL_ARCH_SRCS) $(SAIL_SEQ_INST_SRCS)  $(SAIL_OTHER_SRCS)
SAIL_RMEM_SRCS = $(SAIL_ARCH_SRCS) $(SAIL_RMEM_INST_SRCS) $(SAIL_OTHER_SRCS)
SAIL_RVFI_SRCS = $(SAIL_ARCH_RVFI_SRCS) $(SAIL_SEQ_INST_SRCS) $(RVFI_STEP_SRCS)
SAIL_COQ_SRCS  = $(SAIL_ARCH_SRCS) $(SAIL_SEQ_INST_SRCS) $(SAIL_OTHER_COQ_SRCS)

SAIL_FLAGS += --require-version 0.18
SAIL_FLAGS += --strict-var
SAIL_FLAGS += -dno_cast
SAIL_DOC_FLAGS ?= -doc_embed plain

# Sail command to use.
SAIL := sail

# <sail install dir>/share/sail
SAIL_DIR := $(shell $(SAIL) --dir)
SAIL_LIB_DIR := $(SAIL_DIR)/lib
SAIL_SRC_DIR := $(SAIL_DIR)/src

LEM_DIR := $(SAIL_DIR)/../lem
export LEM_DIR

C_WARNINGS ?=
#-Wall -Wextra -Wno-unused-label -Wno-unused-parameter -Wno-unused-but-set-variable -Wno-unused-function
C_INCS = $(addprefix $(SAIL_RISCV_DIR)/c_emulator/,riscv_prelude.h riscv_platform_impl.h riscv_platform.h riscv_softfloat.h)
C_SRCS = $(addprefix $(SAIL_RISCV_DIR)/c_emulator/,riscv_prelude.cpp riscv_platform_impl.cpp riscv_platform.cpp riscv_softfloat.c riscv_sim.cpp) handwritten_support/c_emulator_fix.c

SOFTFLOAT_DIR    = $(SAIL_RISCV_DIR)/dependencies/softfloat/berkeley-softfloat-3
SOFTFLOAT_INCDIR = $(SOFTFLOAT_DIR)/source/include
SOFTFLOAT_LIBDIR = $(SOFTFLOAT_DIR)/build/Linux-RISCV-GCC
SOFTFLOAT_FLAGS  = -I $(SOFTFLOAT_INCDIR)
SOFTFLOAT_LIBS   = $(SOFTFLOAT_LIBDIR)/softfloat.a
SOFTFLOAT_SPECIALIZE_TYPE = RISCV

GMP_FLAGS = $(shell pkg-config --cflags gmp)
# N.B. GMP does not have pkg-config metadata on Ubuntu 18.04 so default to -lgmp
GMP_LIBS := $(shell pkg-config --libs gmp || echo -lgmp)

ZLIB_FLAGS = $(shell pkg-config --cflags zlib)
ZLIB_LIBS = $(shell pkg-config --libs zlib)

C_FLAGS = -I $(SAIL_LIB_DIR) -I $(SAIL_RISCV_DIR)/c_emulator $(GMP_FLAGS) $(ZLIB_FLAGS) $(SOFTFLOAT_FLAGS)
C_LIBS  = $(GMP_LIBS) $(ZLIB_LIBS) $(SOFTFLOAT_LIBS)

ifneq (,$(SAILCOV))
ALL_BRANCHES = generated_definitions/c/all_branches
C_FLAGS += -DSAILCOV
SAIL_FLAGS += -c_coverage $(ALL_BRANCHES) -c_include sail_coverage.h
C_LIBS += $(SAIL_LIB_DIR)/coverage/libsail_coverage.a -lpthread -ldl
endif

# The C simulator can be built to be linked against Spike for tandem-verification.
# This needs the C bindings to Spike from https://github.com/SRI-CSL/l3riscv
# TV_SPIKE_DIR in the environment should point to the top-level dir of the L3
# RISC-V, containing the built C bindings to Spike.
# RISCV should be defined if TV_SPIKE_DIR is.
ifneq (,$(TV_SPIKE_DIR))
C_FLAGS += -I $(TV_SPIKE_DIR)/src/cpp -DENABLE_SPIKE
C_LIBS  += -L $(TV_SPIKE_DIR) -ltv_spike -Wl,-rpath=$(TV_SPIKE_DIR)
C_LIBS  += -L $(RISCV)/lib -lfesvr -lriscv -Wl,-rpath=$(RISCV)/lib
endif

# SAIL_FLAGS = -dtc_verbose 4

ifneq (,$(COVERAGE))
C_FLAGS += --coverage -O1
SAIL_FLAGS += -Oconstant_fold
else
C_FLAGS += -O2
endif


RISCV_EXTRAS_LEM_FILES = riscv_extras.lem mem_metadata.lem riscv_extras_fdext.lem
RISCV_EXTRAS_LEM = $(addprefix $(SAIL_RISCV_DIR)/handwritten_support/,$(RISCV_EXTRAS_LEM_FILES))

all: c_emulator/cheri_riscv_sim_$(ARCH) riscv_isa riscv_coq riscv_hol riscv_rmem
.PHONY: all

csim: c_emulator/cheri_riscv_sim_$(ARCH)
.PHONY: csim

check: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	$(SAIL) $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

interpret: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail
	$(SAIL) -i $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

sail_doc/riscv_$(ARCH).json: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail
	$(SAIL) -doc -doc_bundle riscv_$(ARCH).json -o sail_doc $(SAIL_FLAGS) $(SAIL_DOC_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

cgen: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail
	$(SAIL) -cgen $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

gcovr:
	gcovr -r . --html --html-detail -o index.html

generated_definitions/c/riscv.c: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	mkdir -p generated_definitions/c
	$(SAIL) $(SAIL_FLAGS) -O -Oconstant_fold -memo_z3 -c -c_include riscv_prelude.h -c_include riscv_platform.h $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail -o $(basename $@)

generated_definitions/c/riscv_model_%.c: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	mkdir -p generated_definitions/c
	$(SAIL) $(preserve_fns) $(SAIL_FLAGS) -O -Oconstant_fold -memo_z3 -c -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail -o $(basename $@)

$(SOFTFLOAT_LIBS):
	$(MAKE) SPECIALIZE_TYPE=$(SOFTFLOAT_SPECIALIZE_TYPE) -C $(SOFTFLOAT_LIBDIR)

c_emulator/cheri_riscv_sim_RV64: generated_definitions/c/riscv_model_%.c $(C_INCS) $(C_SRCS) $(SOFTFLOAT_LIBS) Makefile
	mkdir -p c_emulator
	gcc -g $(C_WARNINGS) $(C_FLAGS) $< $(C_SRCS) $(SAIL_LIB_DIR)/*.c $(C_LIBS) -o $@

# Note: We have to add -c_preserve since the functions might be optimized out otherwise
rvfi_preserve_fns=-c_preserve rvfi_set_instr_packet \
  -c_preserve rvfi_get_cmd \
  -c_preserve rvfi_get_insn \
  -c_preserve rvfi_get_v2_trace_size \
  -c_preserve rvfi_get_v2_support_packet \
  -c_preserve rvfi_get_exec_packet_v1 \
  -c_preserve rvfi_get_exec_packet_v2 \
  -c_preserve rvfi_get_mem_data \
  -c_preserve rvfi_get_int_data \
  -c_preserve rvfi_zero_exec_packet \
  -c_preserve rvfi_halt_exec_packet \
  -c_preserve print_instr_packet \
  -c_preserve print_rvfi_exec

preserve_fns=--c-preserve init_model \
             --c-preserve step \
             --c-preserve tick_clock \
             --c-preserve tick_platform

generated_definitions/c/riscv_rvfi_model_%.c: $(SAIL_RVFI_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	mkdir -p generated_definitions/c
	$(SAIL) $(preserve_fns) $(rvfi_preserve_fns) $(SAIL_FLAGS) -O -Oconstant_fold -memo_z3 -c -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main $(SAIL_RVFI_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail -o $(basename $@)

c_emulator/cheri_riscv_rvfi_%: generated_definitions/c/riscv_rvfi_model_%.c $(C_INCS) $(C_SRCS) $(SOFTFLOAT_LIBS) Makefile
	mkdir -p c_emulator
	gcc -g $(C_WARNINGS) $(C_FLAGS) $< -DRVFI_DII $(C_SRCS) $(SAIL_LIB_DIR)/*.c $(C_LIBS) -o $@

latex: $(SAIL_SRCS) Makefile
	$(SAIL) -latex -latex_prefix sailRISCV -o sail_latex_riscv $(SAIL_SRCS)

generated_definitions/isabelle/$(ARCH)/ROOT: handwritten_support/ROOT
	mkdir -p generated_definitions/isabelle/$(ARCH)
	cp handwritten_support/ROOT generated_definitions/isabelle/$(ARCH)/

generated_definitions/lem/riscv_duopod.lem: $(PRELUDE_SRCS) $(SAIL_RISCV_MODEL_DIR)/riscv_duopod.sail
	mkdir -p generated_definitions/lem
	$(SAIL) $(SAIL_FLAGS) -lem -lem_output_dir generated_definitions/lem -isa_output_dir generated_definitions/isabelle -lem_mwords -lem_lib Riscv_extras -o riscv_duopod $^
generated_definitions/isabelle/Riscv_duopod.thy: generated_definitions/isabelle/$(ARCH)/ROOT generated_definitions/lem/riscv_duopod.lem $(RISCV_EXTRAS_LEM)
	lem -isa -outdir generated_definitions/isabelle -lib Sail=$(SAIL_SRC_DIR)/lem_interp -lib Sail=$(SAIL_SRC_DIR)/gen_lib \
		$(RISCV_EXTRAS_LEM) \
		generated_definitions/lem/riscv_duopod_types.lem \
		generated_definitions/lem/riscv_duopod.lem

riscv_duopod: generated_definitions/ocaml/riscv_duopod_ocaml generated_definitions/isabelle/Riscv_duopod.thy

riscv_isa: generated_definitions/isabelle/$(ARCH)/Riscv.thy
riscv_isa_build: riscv_isa
ifeq ($(wildcard $(LEM_DIR)/isabelle-lib),)
	$(error Lem directory not found. Please set the LEM_DIR environment variable)
endif
ifeq ($(wildcard $(SAIL_LIB_DIR)/isabelle),)
	$(error lib directory of Sail not found. Please set the SAIL_LIB_DIR environment variable)
endif
	isabelle build -b -d $(LEM_DIR)/isabelle-lib -d $(SAIL_LIB_DIR)/isabelle -d generated_definitions/isabelle/$(ARCH) Sail-CHERI-RISC-V

.PHONY: riscv_isa riscv_isa_build

generated_definitions/lem/$(ARCH)/riscv.lem: $(SAIL_SRCS) Makefile handwritten_support/dummy_assembly_mappings.sail
	mkdir -p generated_definitions/lem/$(ARCH) generated_definitions/isabelle/$(ARCH)
	$(SAIL) $(SAIL_FLAGS) -lem -lem_output_dir generated_definitions/lem/$(ARCH) -isa_output_dir generated_definitions/isabelle/$(ARCH) -o riscv -lem_mwords -lem_lib Riscv_extras -lem_lib Riscv_extras_fdext -lem_lib Cheri_extras -mono_rewrites $(SAIL_LIB_DIR)/mono_rewrites.sail $(SAIL_SRCS) -splice handwritten_support/dummy_assembly_mappings.sail
	echo "declare {isabelle} rename field sync_exception_ext = sync_exception_ext_exception" >> generated_definitions/lem/$(ARCH)/riscv_types.lem

generated_definitions/isabelle/$(ARCH)/Riscv.thy: generated_definitions/isabelle/$(ARCH)/ROOT generated_definitions/lem/$(ARCH)/riscv.lem $(RISCV_EXTRAS_LEM) handwritten_support/cheri_extras.lem Makefile
	lem -isa -outdir generated_definitions/isabelle/$(ARCH) -lib Sail=$(SAIL_SRC_DIR)/lem_interp -lib Sail=$(SAIL_SRC_DIR)/gen_lib \
		$(RISCV_EXTRAS_LEM) \
		handwritten_support/cheri_extras.lem \
		generated_definitions/lem/$(ARCH)/riscv_types.lem \
		generated_definitions/lem/$(ARCH)/riscv.lem
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' generated_definitions/isabelle/$(ARCH)/Riscv_types.thy
	sed -i "s/record( 'asidlen, 'valen, 'palen, 'ptelen) TLB_Entry/record (overloaded) ( 'asidlen, 'valen, 'palen, 'ptelen) TLB_Entry/" generated_definitions/isabelle/$(ARCH)/Riscv_types.thy

generated_definitions/hol4/$(ARCH)/Holmakefile: $(SAIL_RISCV_DIR)/handwritten_support/Holmakefile
	mkdir -p generated_definitions/hol4/$(ARCH)
	cp $(SAIL_RISCV_DIR)/handwritten_support/Holmakefile generated_definitions/hol4/$(ARCH)

generated_definitions/hol4/$(ARCH)/riscvScript.sml: generated_definitions/hol4/$(ARCH)/Holmakefile generated_definitions/lem/$(ARCH)/riscv.lem $(RISCV_EXTRAS_LEM) handwritten_support/cheri_extras.lem
	lem -hol -outdir generated_definitions/hol4/$(ARCH) -lib $(SAIL_LIB_DIR)/hol -i $(SAIL_LIB_DIR)/hol/sail2_prompt_monad.lem -i $(SAIL_LIB_DIR)/hol/sail2_prompt.lem \
	    -lib $(SAIL_DIR)/src/lem_interp -lib $(SAIL_DIR)/src/gen_lib \
		$(RISCV_EXTRAS_LEM) \
		handwritten_support/cheri_extras.lem \
		generated_definitions/lem/$(ARCH)/riscv_types.lem \
		generated_definitions/lem/$(ARCH)/riscv.lem

$(addprefix generated_definitions/hol4/$(ARCH)/,riscvTheory.uo riscvTheory.ui): generated_definitions/hol4/$(ARCH)/Holmakefile generated_definitions/hol4/$(ARCH)/riscvScript.sml
ifeq ($(wildcard $(LEM_DIR)/hol-lib),)
	$(error Lem directory not found. Please set the LEM_DIR environment variable)
endif
ifeq ($(wildcard $(SAIL_LIB_DIR)/hol),)
	$(error lib directory of Sail not found. Please set the SAIL_LIB_DIR environment variable)
endif
	(cd generated_definitions/hol4/$(ARCH) && Holmake riscvTheory.uo)

riscv_hol: generated_definitions/hol4/$(ARCH)/riscvScript.sml
riscv_hol_build: generated_definitions/hol4/$(ARCH)/riscvTheory.uo
.PHONY: riscv_hol riscv_hol_build

COQ_LIBS = -R $(BBV_DIR)/theories bbv -R $(SAIL_LIB_DIR)/coq Sail -R generated_definitions/coq/$(ARCH) '' -R $(SAIL_RISCV_DIR)/handwritten_support '' -R handwritten_support ''

riscv_coq: $(addprefix generated_definitions/coq/$(ARCH)/,riscv.v riscv_types.v)
riscv_coq_build: generated_definitions/coq/$(ARCH)/riscv.vo
.PHONY: riscv_coq riscv_coq_build

$(addprefix generated_definitions/coq/$(ARCH)/,riscv.v riscv_types.v): $(SAIL_COQ_SRCS) Makefile handwritten_support/dummy_assembly_mappings.sail
	mkdir -p generated_definitions/coq/$(ARCH)
	$(SAIL) $(SAIL_FLAGS) -dcoq_undef_axioms -coq -coq_output_dir generated_definitions/coq/$(ARCH) -o riscv -coq_lib cheri_extras -coq_lib riscv_extras $(SAIL_COQ_SRCS) -splice handwritten_support/dummy_assembly_mappings.sail
$(addprefix generated_definitions/coq/$(ARCH)/,riscv_duopod.v riscv_duopod_types.v): $(PRELUDE_SRCS) $(SAIL_RISCV_MODEL_DIR)/riscv_duopod.sail
	mkdir -p generated_definitions/coq/$(ARCH)
	$(SAIL) $(SAIL_FLAGS) -dcoq_undef_axioms -coq -coq_output_dir generated_definitions/coq/$(ARCH) -o riscv_duopod -coq_lib riscv_extras $^

%.vo: %.v
ifeq ($(wildcard $(BBV_DIR)/theories),)
	$(error BBV directory not found. Please set the BBV_DIR environment variable)
endif
ifeq ($(wildcard $(SAIL_LIB_DIR)/coq),)
	$(error lib directory of Sail not found. Please set the SAIL_LIB_DIR environment variable)
endif
	coqc $(COQ_LIBS) $<

generated_definitions/coq/$(ARCH)/riscv.vo: generated_definitions/coq/$(ARCH)/riscv_types.vo $(SAIL_RISCV_DIR)/handwritten_support/riscv_extras.vo handwritten_support/cheri_extras.vo
generated_definitions/coq/$(ARCH)/riscv_duopod.vo: generated_definitions/coq/$(ARCH)/riscv_duopod_types.vo $(SAIL_RISCV_DIR)/handwritten_support/riscv_extras.vo handwritten_support/cheri_extras.vo

riscv_rmem: generated_definitions/lem-for-rmem/riscv.lem
.PHONY: riscv_rmem

generated_definitions/lem-for-rmem/riscv.lem: SAIL_FLAGS += -lem_lib Riscv_extras -lem_lib Riscv_extras_fdext
generated_definitions/lem-for-rmem/riscv.lem: $(SAIL_RMEM_SRCS)
	mkdir -p $(dir $@)
#	We do not need the isabelle .thy files, but sail always generates them
	$(SAIL) $(SAIL_FLAGS) -lem -lem_mwords -lem_output_dir $(dir $@) -isa_output_dir $(dir $@) -o $(notdir $(basename $@)) $^

isail:
	$(SAIL) $(SAIL_FLAGS) -i $(PRELUDE_SRCS)

#$(SMT) $(SMT_FLAGS) *.smt2

# we exclude prelude.sail here, most code there should move to sail lib
#LOC_FILES:=$(SAIL_SRCS) main.sail
#include $(SAIL_DIR)/etc/loc.mk

cloc:
	cloc --force-lang C,sail $(SAIL_SRCS)

rvfi: c_emulator/cheri_riscv_rvfi_$(ARCH)

clean:
	-rm -rf generated_definitions/ocaml/* generated_definitions/c/* generated_definitions/latex/* sail_riscv_latex
	-rm -rf generated_definitions/lem/* generated_definitions/isabelle/* generated_definitions/hol4/* generated_definitions/coq/*
	-rm -rf generated_definitions/lem-for-rmem/*
	-make -C $(SOFTFLOAT_LIBDIR) clean
	-rm -f $(addprefix c_emulator/cheri_riscv_sim_RV,32 64)  $(addprefix c_emulator/cheri_riscv_rvfi_RV, 32 64)
	-rm -rf ocaml_emulator/_sbuild ocaml_emulator/_build ocaml_emulator/cheri_riscv_ocaml_sim_RV32 ocaml_emulator/cheri_riscv_ocaml_sim_RV64 ocaml_emulator/tracecmp
	-rm -f *.gcno *.gcda
	-Holmake cleanAll
	-rm -f $(SAIL_RISCV_DIR)/handwritten_support/riscv_extras.vo $(SAIL_RISCV_DIR)/handwritten_support/riscv_extras.glob $(SAIL_RISCV_DIR)/handwritten_support/.riscv_extras.aux
	-rm -f sail_doc/riscv_RV32.json
	-rm -f sail_doc/riscv_RV64.json
	ocamlbuild -clean
