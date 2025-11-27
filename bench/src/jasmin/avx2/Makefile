.PHONY: jasmin_avx2.a clean distclean

all: jasmin_avx2.a

jasmin_avx2.a: bench_avx2.s
	$(CC) $(CFLAGS) -c bench_avx2.s
	$(AR) -r $@ bench_avx2.o

bench_avx2.s: bench_avx2.jazz
	$(JASMINC) -nowarning -lea $< -o $@

clean:
	rm -f *.o *.a

distclean: clean
	rm -f *.s
