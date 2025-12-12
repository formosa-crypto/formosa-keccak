PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64

JASMINC ?= jasmin2ec
JFLAGS ?= --arch x86 --array-model=old -I Keccak=$(SRCDIR)


.DEFAULT_GOAL := all



all: Keccak1600_Jazz.ec Keccak1600_Jazz_ASIZE.ec

Keccak1600_Jazz.ec : toEC_keccak1600.jazz
	$(JASMINC) $(JFLAGS) -o $@ $^

#rmglobals --after unroll  
#jasmin2ec: option '--after': invalid value 'unused', expected one of
#           'typing', 'cstexp', 'arraycopy', 'addarrinit', 'lowerspill',
#           'inline', 'rmfunc', 'unroll', 'splitting', 'renaming', 'rmphi',
#           'renamingd', 'rmarrinit', 'makeref', 'arrexp', 'rmglobals',
#           'loadconst', 'lowering', 'propagate', 'slhlowering' or 'loweraddr'
#Jazz_avx2_inlined.ec : $(SRCDIR)/avx2/toEC_inlined.jazz
#	$(JASMINCC) --after makeref -f _keccakf1600_4x_pround -o $(OUTDIR)/$@ $^
#
#inlined pround proc generated (and hand-edited) by:
#jasminc -pmakeref keccakf1600_pround_avx2x4.jinc > keccakf1600_pround_inlined_avx2x4.jinc

Keccak1600_Jazz_ASIZE.ec : toEC_keccak1600_ASIZE.jazz
	$(JASMINC) $(JFLAGS) -o $@ $^

clean:
	rm -f $(PROGS) WArray*.ec Array*.ec *~
