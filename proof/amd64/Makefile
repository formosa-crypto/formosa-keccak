
JASMINC2EC ?= jasmin2ec --arch x86

SRCDIR = ../../src/amd64
OUTDIR = ../extracted

all: Jazz_ref.ec Jazz_avx2.ec

Jazz_ref.ec : $(SRCDIR)/ref/toEC.jazz
	$(JASMINC2EC) -o $(OUTDIR)/$@ $^

Jazz_avx2.ec : $(SRCDIR)/avx2/toEC.jazz
	$(JASMINC2EC) -o $(OUTDIR)/$@ $^


