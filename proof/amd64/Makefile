
JASMINC2EC ?= jasmin2ec --arch x86 --array-old

SRCDIR = ../../src/amd64
OUTDIR = extracted

all: Jazz_ref.ec Jazz_avx2.ec Jazz_ref_ASIZE.ec Jazz_avx2_ASIZE.ec

Jazz_ref.ec : $(SRCDIR)/ref/toEC.jazz
	$(JASMINC2EC) -o $(OUTDIR)/$@ $^

Jazz_avx2.ec : $(SRCDIR)/avx2/toEC.jazz
	$(JASMINC2EC) -o $(OUTDIR)/$@ $^

Jazz_ref_ASIZE.ec : $(SRCDIR)/ref/toEC_ASIZE.jazz
	$(JASMINC2EC) -o $(OUTDIR)/$@ $^

Jazz_avx2_ASIZE.ec : $(SRCDIR)/avx2/toEC_ASIZE.jazz
	$(JASMINC2EC) -o $(OUTDIR)/$@ $^


