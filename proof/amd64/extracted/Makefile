PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64

JASMINC ?= jasmin2ec
JFLAGS ?= --arch x86 --array-model=old -I Keccak=$(SRCDIR)


.DEFAULT_GOAL := all

PROGS = Jazz_ref.ec Jazz_avx2.ec Jazz_ref_ASIZE.ec Jazz_avx2_ASIZE.ec


all: $(PROGS)


Jazz_ref.ec : toEC_ref.jazz
	$(JASMINC) $(JFLAGS) -o $@ $^

Jazz_avx2.ec : toEC_avx2.jazz
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

Jazz_ref_ASIZE.ec : toEC_ref_ASIZE.jazz
	$(JASMINC) $(JFLAGS) -o $@ $^

Jazz_avx2_ASIZE.ec : toEC_avx2_ASIZE.jazz
	$(JASMINC) $(JFLAGS) -o $@ $^

#Jazz_avx2x4_ASIZE.ec : $(SRCDIR)/avx2/toEC_ASIZE.jazz
#	$(JASMINC) -o $(OUTDIR)/$@ $^


clean:
	rm -f $(PROGS) WArray*.ec Array*.ec *~
