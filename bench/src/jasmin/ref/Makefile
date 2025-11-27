.PHONY: jasmin_ref.a clean distclean

all: jasmin_ref.a

jasmin_ref.a: bench_ref.s
	$(CC) $(CFLAGS) -c bench_ref.s
	$(AR) -r $@ bench_ref.o

bench_ref.s: bench_ref.jazz
	$(JASMINC) -nowarning -lea $< -o $@

clean:
	rm -f *.o *.a

distclean: clean
	rm -f *.s
