include ../../Makefile.conf

.DEFAULT_GOAL := all

PROGS = bench_keccakF

all: $(PROGS)

bench_keccakF: bench_keccakF.c bench_keccakF.s fips202.s keccak1600-x86_64.S sha3_keccak_f1600.S keccak_f1600_x4_avx2_asm.S
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) $(JPATH) -o $@ $<

fips202.s: fips202.c
	$(CC) -S -O3 -march=native -mtune=native $<
clean:
	rm -f bench_keccakF.s fips202.s

realclean: clean
	rm -rf $(PROGS)
