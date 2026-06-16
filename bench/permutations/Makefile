include ../../Makefile.conf

.DEFAULT_GOAL := all

PROGS = bench_avx2x4_f

all: $(PROGS)

bench_avx2x4_f: test_avx2x4_f.s fips202.s keccak1600-x86_64.S sha3_keccak_f1600.S keccak_f1600_x4_avx2_asm.S bench_avx2x4_f.c
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) $(JPATH) -o $@ $<

clean:
	rm -f test_*.s

realclean: clean
	rm -rf $(PROGS)
