PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64

JASMIN2EC ?= jasmin2ec
JFLAGS ?= --arch x86 --array-model=old -I Keccak=$(SRCDIR)


.DEFAULT_GOAL := all

PROGS = Keccak1600_Jazz.ec Keccak1600_Jazz_ASIZE.ec

all: $(PROGS)

Keccak1600_Jazz.ec : toEC_keccak1600.jazz
	$(JASMIN2EC) $(JFLAGS) -o $@ $^

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
	$(JASMIN2EC) $(JFLAGS) -o $@ $^

check: $(PROGS)
	for i in *_checkXtr.ec; do easycrypt compile -no-eco $i; done
	
clean:
	rm -f $(PROGS) WArray*.ec Array*.ec *~
