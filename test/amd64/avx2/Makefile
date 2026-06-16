include ../../../Makefile.conf

.DEFAULT_GOAL := all

PROGS = test_avx2 test_mavx2 test_avx2x4 test_avx2x4_f

all: $(PROGS)

test_avx2: test_avx2.c test_avx2.s ../ref/test_ref.s
	$(CC) -o $@ $^

test_mavx2: test_mavx2.c test_mavx2.s ../ref/test_mref.s
	$(CC) -o $@ $^

test_avx2x4: test_avx2x4.c test_avx2x4.s ../ref/test_ref.s
	$(CC) -o $@ $^

test_avx2x4_f: test_avx2x4_f.c test_avx2x4_f.s
	$(CC) -o $@ $^

bench_avx2x4_f: test_avx2x4_f.s keccak1600-x86_64.S sha3_keccak_f1600.S keccak_f1600_x4_avx2_asm.S bench_avx2x4_f.c
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) $(JPATH) -o $@ $<

clean:
	rm -f test_*.s

realclean: clean
	rm -rf $(PROGS)
