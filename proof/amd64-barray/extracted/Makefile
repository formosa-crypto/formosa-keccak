include ../../../Makefile.conf

# barray array model (see Makefile.conf)
JECFLAGS = $(JECFLAGS_BARRAY)

.DEFAULT_GOAL := all

PROGS = Keccak1600_Jazz.ec Keccak1600_Jazz_ASIZE.ec

all: $(PROGS)

.PHONY: re_extract_mem re_extract_array re_extract checkXtr clean

re_extract_mem: Keccak1600_Jazz.ec
Keccak1600_Jazz.ec : toEC_keccak1600.jazz
	$(JASMIN2EC) $(JECFLAGS) $(JPATH) -o $@ $^

re_extract_array: Keccak1600_Jazz_ASIZE.ec
Keccak1600_Jazz_ASIZE.ec : toEC_keccak1600_ASIZE.jazz
	$(JASMIN2EC) $(JECFLAGS) $(JPATH) -o $@ $^

re_extract: clean all

checkXtr: $(PROGS)
	for i in *_checkXtr.ec; do easycrypt compile -no-eco $$i || exit 1; done

clean:
	rm -f $(PROGS) Array*.ec WArray*.ec BArray*.ec SBArray*.ec *~
