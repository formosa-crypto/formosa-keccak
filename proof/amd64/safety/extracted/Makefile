include ../../../../Makefile.conf

# Safety models: barray array model with the safety instrumentation of
# jasmin2ec -m safety (needs the "safety-assert2" branch of Jasmin, see
# shell.nix). Same strategy as the correctness extraction:
#  - Keccak1600_Jazz_safety.ec: memory variants (and everything that does not
#    depend on the array size), extracted directly;
#  - Keccak1600_Jazz_ASIZE_safety.ec: array variants, extracted under the
#    dummy size _ASIZE = 999. It is abstracted over the size by ../gen (module
#    MM of the abstract theories in the proof files); the *_checkXtr.ec files
#    check that MM is the abstraction of this extraction.
JECFLAGS = $(JECFLAGS_BARRAY) -m safety

.DEFAULT_GOAL := all

DEPS = $(shell find $(TOPDIR)src/amd64 -name '*.jinc')
PROGS = Keccak1600_Jazz_safety.ec Keccak1600_Jazz_ASIZE_safety.ec

all: $(PROGS)

.PHONY: re_extract_mem re_extract_array re_extract checkXtr clean

# Besides each model, jasmin2ec writes a proof skeleton (*.skel: one lemma per
# function); ../gen takes the lemma statements from it. Not committed.
re_extract_mem: Keccak1600_Jazz_safety.ec
Keccak1600_Jazz_safety.ec : toEC_keccak1600.jazz $(DEPS)
	$(JASMIN2EC) $(JECFLAGS) $(JPATH) -o $@ --output-proof $(@:.ec=.skel) $<

re_extract_array: Keccak1600_Jazz_ASIZE_safety.ec
Keccak1600_Jazz_ASIZE_safety.ec : toEC_keccak1600_ASIZE.jazz toEC_keccak1600.jazz $(DEPS)
	$(JASMIN2EC) $(JECFLAGS) $(JPATH) -o $@ --output-proof $(@:.ec=.skel) $<

re_extract: clean all

checkXtr: $(PROGS)
	for i in *_checkXtr.ec; do easycrypt compile -no-eco $$i || exit 1; done

clean:
	rm -f $(PROGS) *.skel Array*.ec WArray*.ec BArray*.ec SBArray*.ec *~
