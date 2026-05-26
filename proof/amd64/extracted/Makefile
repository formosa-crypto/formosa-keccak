PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64

JASMIN2EC ?= jasmin2ec
JASMINCT ?= jasmin-ct
JFLAGS ?= --arch x86 -I Keccak=$(SRCDIR)
JECFLAGS ?= --array-model=old 

.DEFAULT_GOAL := all

PROGS = Keccak1600_Jazz.ec Keccak1600_Jazz_ASIZE.ec

all: $(PROGS)

Keccak1600_Jazz.ec : toEC_keccak1600.jazz
	$(JASMIN2EC) $(JFLAGS) $(JECFLAGS) -o $@ $^

Keccak1600_Jazz_ASIZE.ec : toEC_keccak1600_ASIZE.jazz
	$(JASMIN2EC) $(JFLAGS) $(JECFLAGS) -o $@ $^

re_extract: clean all

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


check: $(PROGS)
	for i in *_checkXtr.ec; do easycrypt compile -no-eco $$i || exit 1; done

ct: ct_ref ct_avx2 ct_avx2x4

ct-ref: keccak1600_ref_ct keccak1600_ref_ASIZE_ct
ct-avx2: keccak1600_avx2_ct keccak1600_avx2_ASIZE_ct
ct-avx2x4: keccak1600_avx2x4_ct keccak1600_avx2x4_ASIZE_ct

%_ct: toEC_%.jazz
	$(JASMINCT) $(JFLAGS) --infer $^

clean:
	rm -f $(PROGS) WArray*.ec Array*.ec *~
