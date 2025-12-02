.PHONY: jasmin_old_avx2.a clean distclean

CFLAGS ?= -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE -mavx2

all: jasmin_old_avx2.a

jasmin_old_avx2.a: bench_old_avx2.s
	$(CC) $(CFLAGS) -c bench_old_avx2.s
	$(AR) -r $@ bench_old_avx2.o

bench_old_avx2.s: bench_old_avx2.jazz
	$(JASMINC) -nowarning -lea $< -o $@

clean:
	rm -f *.o *.a

distclean: clean
	rm -f *.s
