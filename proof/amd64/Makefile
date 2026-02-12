
# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF := ./../config/tests.config 

# --------------------------------------------------------------------

JASMIN2EC ?= ./../../jasmin2ec --arch x86 --array-model=old

# SRCDIR = ./../../src/amd64
OUTDIR = extracted

all: Jazz_keccak.ec Jazz_keccak_ASIZE.ec
checkec_correctness_avx2:
	easycrypt runtest $(ECCONF) keccak_correctness_avx2

checkec_correctness_ref:
	easycrypt runtest $(ECCONF) keccak_correctness_ref

checkec_safety_avx2:
	easycrypt runtest $(ECCONF) keccak_safety_avx2

checkec_safety_ref:
	easycrypt runtest $(ECCONF) keccak_safety_ref


# Jazz_ref.ec : $(SRCDIR)/ref/toEC.jazz
# 	$(JASMIN2EC) -o $(OUTDIR)/$@ $^

Jazz_keccak.ec : $(OUTDIR)/toEC_keccak1600.jazz
	$(JASMIN2EC) -o $(OUTDIR)/$@ $^

#rmglobals --after unroll  
#jasmin2ec: option '--after': invalid value 'unused', expected one of
#           'typing', 'cstexp', 'arraycopy', 'addarrinit', 'lowerspill',
#           'inline', 'rmfunc', 'unroll', 'splitting', 'renaming', 'rmphi',
#           'renamingd', 'rmarrinit', 'makeref', 'arrexp', 'rmglobals',
#           'loadconst', 'lowering', 'propagate', 'slhlowering' or 'loweraddr'
#Jazz_avx2_inlined.ec : $(SRCDIR)/avx2/toEC_inlined.jazz
#	$(JASMINC2EC) --after makeref -f _keccakf1600_4x_pround -o $(OUTDIR)/$@ $^
#
#inlined pround proc generated (and hand-edited) by:
#jasminc -pmakeref keccakf1600_pround_avx2x4.jinc > keccakf1600_pround_inlined_avx2x4.jinc

# Jazz_ref_ASIZE.ec : $(SRCDIR)/ref/toEC_ASIZE.jazz
# 	$(JASMIN2EC) -o $(OUTDIR)/$@ $^

Jazz_keccak_ASIZE.ec : $(OUTDIR)/toEC_keccak1600_ASIZE.jazz
	$(JASMIN2EC) -o $(OUTDIR)/$@ $^

#Jazz_avx2x4_ASIZE.ec : $(SRCDIR)/avx2/toEC_ASIZE.jazz
#	$(JASMINC2EC) -o $(OUTDIR)/$@ $^

