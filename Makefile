# Simplified makefile for CHERI.
ARCH = RV64


SAIL_RISCV_DIR=sail-riscv
SAIL_RISCV_MODEL_DIR=$(SAIL_RISCV_DIR)/model
SAIL_CHERI_MODEL_DIR=src

# Instruction sources, depending on target
SAIL_CHECK_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_addr_checks_common.sail \
                  $(SAIL_CHERI_MODEL_DIR)/cheri_addr_checks.sail
SAIL_DEFAULT_INST = $(SAIL_RISCV_MODEL_DIR)/riscv_insts_base.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_aext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_cext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_mext.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_insts_zicsr.sail \
                    $(SAIL_CHERI_MODEL_DIR)/cheri_insts.sail
SAIL_SEQ_INST  = $(SAIL_DEFAULT_INST) $(SAIL_RISCV_MODEL_DIR)/riscv_jalr_seq.sail
SAIL_RMEM_INST = $(SAIL_DEFAULT_INST) $(SAIL_RISCV_MODEL_DIR)/riscv_jalr_rmem.sail $(SAIL_RISCV_MODEL_DIR)/riscv_insts_rmem.sail

SAIL_SEQ_INST_SRCS  = $(SAIL_RISCV_MODEL_DIR)/riscv_insts_begin.sail $(SAIL_SEQ_INST)  $(SAIL_RISCV_MODEL_DIR)/riscv_insts_end.sail
SAIL_RMEM_INST_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_insts_begin.sail $(SAIL_RMEM_INST) $(SAIL_RISCV_MODEL_DIR)/riscv_insts_end.sail

# System and platform sources
SAIL_SYS_SRCS =  $(SAIL_RISCV_MODEL_DIR)/riscv_csr_map.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_next_regs.sail
SAIL_SYS_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_sys_exceptions.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_sync_exception.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_next_control.sail
SAIL_SYS_SRCS += $(SAIL_CHERI_MODEL_DIR)/cheri_csr_ext.sail
SAIL_SYS_SRCS += $(SAIL_RISCV_MODEL_DIR)/riscv_sys_control.sail
SAIL_SYS_SRCS += $(SAIL_CHECK_SRCS)

SAIL_RV32_VM_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_sv32.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_rv32.sail
SAIL_RV64_VM_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_sv39.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_sv48.sail \
                    $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_rv64.sail

SAIL_VM_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_common.sail $(SAIL_RISCV_MODEL_DIR)/riscv_vmem_tlb.sail
ifeq ($(ARCH),RV32)
SAIL_VM_SRCS += $(SAIL_RV32_VM_SRCS)
else
SAIL_VM_SRCS += $(SAIL_RV64_VM_SRCS)
endif

# Non-instruction sources
SAIL_XLEN = $(SAIL_RISCV_MODEL_DIR)/riscv_xlen64.sail
PRELUDE = $(SAIL_RISCV_MODEL_DIR)/prelude.sail \
          $(SAIL_RISCV_MODEL_DIR)/prelude_mapping.sail \
          $(SAIL_XLEN) \
          $(SAIL_CHERI_MODEL_DIR)/cheri_prelude.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_mem_metadata.sail \
          $(SAIL_RISCV_MODEL_DIR)/prelude_mem.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_types.sail \
          $(SAIL_CHERI_MODEL_DIR)/cheri_prelude_128.sail

SAIL_REGS_SRCS = $(SAIL_CHERI_MODEL_DIR)/cheri_reg_type.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_regs.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_sys_regs.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_sys_regs.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_regs.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_pc_access.sail

SAIL_ARCH_SRCS = $(PRELUDE) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_types.sail \
                 $(SAIL_REGS_SRCS) \
                 $(SAIL_SYS_SRCS) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_platform.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_mem.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_mem.sail \
                 $(SAIL_VM_SRCS)

SAIL_ARCH_RVFI_SRCS = \
                 $(PRELUDE) \
                 $(SAIL_RISCV_MODEL_DIR)/rvfi_dii.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_types.sail \
                 $(SAIL_REGS_SRCS) \
                 $(SAIL_SYS_SRCS) \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_platform.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_mem.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_mem.sail \
                 $(SAIL_VM_SRCS)

SAIL_STEP_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_step_common.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_step_ext.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_decode_ext.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_fetch.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_step.sail

RVFI_STEP_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_step_common.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_step_rvfi.sail \
                 $(SAIL_CHERI_MODEL_DIR)/cheri_decode_ext.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_fetch_rvfi.sail \
                 $(SAIL_RISCV_MODEL_DIR)/riscv_step.sail

# Control inclusion of 64-bit only riscv_analysis
ifeq ($(ARCH),RV32)
SAIL_OTHER_SRCS     = $(SAIL_STEP_SRCS)
SAIL_OTHER_COQ_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_termination_common.sail \
                      $(SAIL_RISCV_MODEL_DIR)/riscv_termination_rv32.sail
else
SAIL_OTHER_SRCS     = $(SAIL_STEP_SRCS) \
                      $(SAIL_RISCV_MODEL_DIR)/riscv_analysis.sail
SAIL_OTHER_COQ_SRCS = $(SAIL_RISCV_MODEL_DIR)/riscv_termination_common.sail \
                      $(SAIL_RISCV_MODEL_DIR)/riscv_termination_rv64.sail \
                      $(SAIL_RISCV_MODEL_DIR)/riscv_analysis.sail
endif


PRELUDE_SRCS   = $(PRELUDE)
SAIL_SRCS      = $(SAIL_ARCH_SRCS) $(SAIL_SEQ_INST_SRCS)  $(SAIL_OTHER_SRCS)
SAIL_RMEM_SRCS = $(SAIL_ARCH_SRCS) $(SAIL_RMEM_INST_SRCS) $(SAIL_OTHER_SRCS)
SAIL_RVFI_SRCS = $(SAIL_ARCH_RVFI_SRCS) $(SAIL_SEQ_INST_SRCS) $(RVFI_STEP_SRCS)
SAIL_COQ_SRCS  = $(SAIL_ARCH_SRCS) $(SAIL_SEQ_INST_SRCS) $(SAIL_OTHER_COQ_SRCS)

PLATFORM_OCAML_SRCS = $(addprefix $(SAIL_RISCV_DIR)/ocaml_emulator/,platform.ml platform_impl.ml riscv_ocaml_sim.ml _tags)

# Attempt to work with either sail from opam or built from repo in SAIL_DIR
ifneq ($(SAIL_DIR),)
# Use sail repo in SAIL_DIR
SAIL:=$(SAIL_DIR)/sail
export SAIL_DIR
else
# Use sail from opam package
SAIL_DIR=$(shell opam config var sail:share)
SAIL:=sail
endif
SAIL_LIB_DIR:=$(SAIL_DIR)/lib
export SAIL_LIB_DIR
SAIL_SRC_DIR:=$(SAIL_DIR)/src

LEM_DIR?=$(shell opam config var lem:share)
export LEM_DIR
#Coq BBV library hopefully checked out in directory above us
BBV_DIR?=../bbv

C_WARNINGS ?=
#-Wall -Wextra -Wno-unused-label -Wno-unused-parameter -Wno-unused-but-set-variable -Wno-unused-function
C_INCS = $(addprefix $(SAIL_RISCV_DIR)/c_emulator/,riscv_prelude.h riscv_platform_impl.h riscv_platform.h)
C_SRCS = $(addprefix $(SAIL_RISCV_DIR)/c_emulator/,riscv_prelude.c riscv_platform_impl.c riscv_platform.c)

C_FLAGS = -I $(SAIL_LIB_DIR) -I $(SAIL_RISCV_DIR)/c_emulator
C_LIBS  = -lgmp -lz

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

# Feature detect if we are on the latest development version of Sail
# and use an updated lem file if so. This is just until the opam
# version catches up with changes to the monad embedding.
SAIL_LATEST := $(shell $(SAIL) -emacs 1>&2 2> /dev/null; echo $$?)
ifeq ($(SAIL_LATEST),0)
RISCV_EXTRAS_LEM = riscv_extras.lem
else
RISCV_EXTRAS_LEM = 0.7.1/riscv_extras.lem
endif

all: ocaml_emulator/riscv_ocaml_sim_$(ARCH) c_emulator/riscv_sim_$(ARCH) riscv_isa riscv_coq riscv_hol riscv_rmem
.PHONY: all

check: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	$(SAIL) $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

interpret: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail
	$(SAIL) -i $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

cgen: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail
	$(SAIL) -cgen $(SAIL_FLAGS) $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail

generated_definitions/ocaml/$(ARCH)/riscv.ml: $(SAIL_SRCS) Makefile
	mkdir -p generated_definitions/ocaml/$(ARCH)
	$(SAIL) $(SAIL_FLAGS) -ocaml -ocaml-nobuild -ocaml_build_dir generated_definitions/ocaml/$(ARCH) -o riscv $(SAIL_SRCS)

ocaml_emulator/_sbuild/riscv_ocaml_sim.native: generated_definitions/ocaml/$(ARCH)/riscv.ml $(PLATFORM_OCAML_SRCS) Makefile
	mkdir -p ocaml_emulator/_sbuild
	cp $(PLATFORM_OCAML_SRCS) generated_definitions/ocaml/$(ARCH)/*.ml ocaml_emulator/_sbuild
	cd ocaml_emulator/_sbuild && ocamlbuild -use-ocamlfind riscv_ocaml_sim.native

ocaml_emulator/_sbuild/coverage.native: generated_definitions/ocaml/$(ARCH)/riscv.ml $(SAIL_RISCV_DIR)/ocaml_emulator/_tags.bisect $(PLATFORM_OCAML_SRCS) Makefile
	mkdir -p ocaml_emulator/_sbuild
	cp $(PLATFORM_OCAML_SRCS) generated_definitions/ocaml/$(ARCH)/*.ml ocaml_emulator/_sbuild
	cp $(SAIL_RISCV_DIR)/ocaml_emulator/_tags.bisect ocaml_emulator/_sbuild/_tags
	cd ocaml_emulator/_sbuild && ocamlbuild -use-ocamlfind riscv_ocaml_sim.native && cp -L riscv_ocaml_sim.native coverage.native

ocaml_emulator/riscv_ocaml_sim_$(ARCH): ocaml_emulator/_sbuild/riscv_ocaml_sim.native
	rm -f $@ && cp -L $^ $@ && rm -f $^

ocaml_emulator/coverage_$(ARCH): ocaml_emulator/_sbuild/coverage.native
	rm -f ocaml_emulator/riscv_ocaml_sim_$(ARCH) && cp -L $^ ocaml_emulator/riscv_ocaml_sim_$(ARCH) # since the test scripts runs this file
	rm -rf bisect*.out bisect ocaml_emulator/coverage_$(ARCH) $^
	./test/run_tests.sh # this will generate bisect*.out files in this directory
	mkdir ocaml_emulator/bisect && mv bisect*.out bisect/
	mkdir ocaml_emulator/coverage_$(ARCH) && bisect-ppx-report -html ocaml_emulator/coverage_$(ARCH)/ -I ocaml_emulator/_sbuild/ bisect/bisect*.out

gcovr:
	gcovr -r . --html --html-detail -o index.html

ocaml_emulator/tracecmp: ocaml_emulator/tracecmp.ml
	ocamlfind ocamlopt -annot -linkpkg -package unix $^ -o $@

generated_definitions/c/riscv.c: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	mkdir -p generated_definitions/c
	$(SAIL) $(SAIL_FLAGS) -O -memo_z3 -c -c_include riscv_prelude.h -c_include riscv_platform.h $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail -o $(basename $@)

c_emulator/riscv_c: generated_definitions/c/riscv.c $(C_INCS) $(C_SRCS) Makefile
	gcc $(C_WARNINGS) $(C_FLAGS) $< $(C_SRCS) $(SAIL_LIB_DIR)/*.c -lgmp -lz -I $(SAIL_LIB_DIR) -o $@

generated_definitions/c/riscv_model_$(ARCH).c: $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	mkdir -p generated_definitions/c
	$(SAIL) $(SAIL_FLAGS) -O -memo_z3 -c -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main $(SAIL_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail -o $(basename $@)

c_emulator/riscv_sim_$(ARCH): generated_definitions/c/riscv_model_$(ARCH).c $(SAIL_RISCV_DIR)/c_emulator/riscv_sim.c $(C_INCS) $(C_SRCS) Makefile
	mkdir -p c_emulator
	gcc -g $(C_WARNINGS) $(C_FLAGS) $< $(SAIL_RISCV_DIR)/c_emulator/riscv_sim.c $(C_SRCS) $(SAIL_LIB_DIR)/*.c $(C_LIBS) -o $@

generated_definitions/c/riscv_rvfi_model.c: $(SAIL_RVFI_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail Makefile
	mkdir -p generated_definitions/c
	$(SAIL) $(SAIL_FLAGS) -O -memo_z3 -c -c_include riscv_prelude.h -c_include riscv_platform.h -c_no_main $(SAIL_RVFI_SRCS) $(SAIL_RISCV_MODEL_DIR)/main.sail -o $(basename $@)

c_emulator/riscv_rvfi: generated_definitions/c/riscv_rvfi_model.c $(SAIL_RISCV_DIR)/c_emulator/riscv_sim.c $(C_INCS) $(C_SRCS) Makefile
	mkdir -p c_emulator
	gcc -g $(C_WARNINGS) $(C_FLAGS) $< -DRVFI_DII $(SAIL_RISCV_DIR)/c_emulator/riscv_sim.c $(C_SRCS) $(SAIL_LIB_DIR)/*.c $(C_LIBS) -o $@

latex: $(SAIL_SRCS) Makefile
	$(SAIL) -latex -latex_prefix sailRISCV -o sail_latex_riscv $(SAIL_SRCS)

generated_definitions/isabelle/$(ARCH)/ROOT: $(SAIL_RISCV_DIR)/handwritten_support/ROOT
	mkdir -p generated_definitions/isabelle/$(ARCH)
	cp $(SAIL_RISCV_DIR)/handwritten_support/ROOT generated_definitions/isabelle/$(ARCH)/

generated_definitions/lem/riscv_duopod.lem: $(PRELUDE_SRCS) $(SAIL_RISCV_MODEL_DIR)/riscv_duopod.sail
	mkdir -p generated_definitions/lem
	$(SAIL) $(SAIL_FLAGS) -lem -lem_output_dir generated_definitions/lem -isa_output_dir generated_definitions/isabelle -lem_mwords -lem_lib Riscv_extras -o riscv_duopod $^
generated_definitions/isabelle/Riscv_duopod.thy: generated_definitions/isabelle/ROOT generated_definitions/lem/riscv_duopod.lem handwritten_support/$(RISCV_EXTRAS_LEM)
	lem -isa -outdir generated_definitions/isabelle -lib Sail=$(SAIL_SRC_DIR)/lem_interp -lib Sail=$(SAIL_SRC_DIR)/gen_lib \
		handwritten_support/$(RISCV_EXTRAS_LEM) \
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
	isabelle build -b -d $(LEM_DIR)/isabelle-lib -d $(SAIL_LIB_DIR)/isabelle -d generated_definitions/isabelle/$(ARCH) Sail-RISC-V

.PHONY: riscv_isa riscv_isa_build

generated_definitions/lem/$(ARCH)/riscv.lem: $(SAIL_SRCS) Makefile
	mkdir -p generated_definitions/lem/$(ARCH) generated_definitions/isabelle/$(ARCH)
	$(SAIL) $(SAIL_FLAGS) -lem -lem_output_dir generated_definitions/lem/$(ARCH) -isa_output_dir generated_definitions/isabelle/$(ARCH) -o riscv -lem_mwords -lem_lib Riscv_extras $(SAIL_SRCS)

generated_definitions/lem/$(ARCH)/riscv_sequential.lem: $(SAIL_SRCS) Makefile
	mkdir -p generated_definitions/lem/$(ARCH) generated_definitions/isabelle/$(ARCH)
	$(SAIL_DIR)/sail -lem -lem_output_dir generated_definitions/lem/$(ARCH) -isa_output_dir generated_definitions/isabelle/$(ARCH) -lem_sequential -o riscv_sequential -lem_mwords -lem_lib Riscv_extras_sequential $(SAIL_SRCS)

generated_definitions/isabelle/$(ARCH)/Riscv.thy: generated_definitions/isabelle/$(ARCH)/ROOT generated_definitions/lem/$(ARCH)/riscv.lem handwritten_support/$(RISCV_EXTRAS_LEM) Makefile
	lem -isa -outdir generated_definitions/isabelle/$(ARCH) -lib Sail=$(SAIL_SRC_DIR)/lem_interp -lib Sail=$(SAIL_SRC_DIR)/gen_lib \
		handwritten_support/$(RISCV_EXTRAS_LEM) \
		generated_definitions/lem/$(ARCH)/riscv_types.lem \
		generated_definitions/lem/$(ARCH)/riscv.lem
	sed -i 's/datatype ast/datatype (plugins only: size) ast/' generated_definitions/isabelle/$(ARCH)/Riscv_types.thy
	sed -i "s/record( 'asidlen, 'valen, 'palen, 'ptelen) TLB_Entry/record (overloaded) ( 'asidlen, 'valen, 'palen, 'ptelen) TLB_Entry/" generated_definitions/isabelle/$(ARCH)/Riscv_types.thy

generated_definitions/hol4/$(ARCH)/Holmakefile: handwritten_support/Holmakefile
	mkdir -p generated_definitions/hol4/$(ARCH)
	cp handwritten_support/Holmakefile generated_definitions/hol4/$(ARCH)

generated_definitions/hol4/$(ARCH)/riscvScript.sml: generated_definitions/hol4/$(ARCH)/Holmakefile generated_definitions/lem/$(ARCH)/riscv.lem handwritten_support/$(RISCV_EXTRAS_LEM)
	lem -hol -outdir generated_definitions/hol4/$(ARCH) -lib $(SAIL_LIB_DIR)/hol -i $(SAIL_LIB_DIR)/hol/sail2_prompt_monad.lem -i $(SAIL_LIB_DIR)/hol/sail2_prompt.lem \
	    -lib $(SAIL_DIR)/src/lem_interp -lib $(SAIL_DIR)/src/gen_lib \
		handwritten_support/$(RISCV_EXTRAS_LEM) \
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

COQ_LIBS = -R $(BBV_DIR)/theories bbv -R $(SAIL_LIB_DIR)/coq Sail -R coq '' -R generated_definitions/coq/$(ARCH) '' -R handwritten_support ''

riscv_coq: $(addprefix generated_definitions/coq/$(ARCH)/,riscv.v riscv_types.v)
riscv_coq_build: generated_definitions/coq/$(ARCH)/riscv.vo
.PHONY: riscv_coq riscv_coq_build

$(addprefix generated_definitions/coq/$(ARCH)/,riscv.v riscv_types.v): $(SAIL_COQ_SRCS) Makefile
	mkdir -p generated_definitions/coq/$(ARCH)
	$(SAIL) $(SAIL_FLAGS) -dcoq_undef_axioms -coq -coq_output_dir generated_definitions/coq/$(ARCH) -o riscv -coq_lib riscv_extras $(SAIL_COQ_SRCS)
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

generated_definitions/coq/$(ARCH)/riscv.vo: generated_definitions/coq/$(ARCH)/riscv_types.vo handwritten_support/riscv_extras.vo
generated_definitions/coq/$(ARCH)/riscv_duopod.vo: generated_definitions/coq/$(ARCH)/riscv_duopod_types.vo handwritten_support/riscv_extras.vo

riscv_rmem: generated_definitions/lem-for-rmem/riscv.lem
.PHONY: riscv_rmem

generated_definitions/lem-for-rmem/riscv.lem: SAIL_FLAGS += -lem_lib Riscv_extras
generated_definitions/lem-for-rmem/riscv.lem: $(SAIL_RMEM_SRCS)
	mkdir -p $(dir $@)
#	We do not need the isabelle .thy files, but sail always generates them
	$(SAIL) $(SAIL_FLAGS) -lem -lem_mwords -lem_output_dir $(dir $@) -isa_output_dir $(dir $@) -o $(notdir $(basename $@)) $^


# we exclude prelude.sail here, most code there should move to sail lib
#LOC_FILES:=$(SAIL_SRCS) main.sail
#include $(SAIL_DIR)/etc/loc.mk

clean:
	-rm -rf generated_definitions/ocaml/* generated_definitions/c/* generated_definitions/latex/* sail_riscv_latex
	-rm -rf generated_definitions/lem/* generated_definitions/isabelle/* generated_definitions/hol4/* generated_definitions/coq/*
	-rm -rf generated_definitions/lem-for-rmem/*
	-rm -f c_emulator/riscv_sim_RV32 c_emulator/riscv_sim_RV64  c_emulator/riscv_rvfi
	-rm -rf ocaml_emulator/_sbuild ocaml_emulator/_build ocaml_emulator/riscv_ocaml_sim_RV32 ocaml_emulator/riscv_ocaml_sim_RV64 ocaml_emulator/tracecmp
	-rm -f *.gcno *.gcda
	-Holmake cleanAll
	-rm -f handwritten_support/riscv_extras.vo handwritten_support/riscv_extras.glob handwritten_support/.riscv_extras.aux
	ocamlbuild -clean
