.PHONY: jasmin_old_ref.a clean distclean

all: jasmin_old_ref.a

jasmin_old_ref.a: bench_old_ref.s
	$(CC) $(CFLAGS) -c bench_old_ref.s
	$(AR) -r $@ bench_old_ref.o

bench_old_ref.s: bench_old_ref.jazz
	$(JASMINC) -nowarning -lea $< -o $@

clean:
	rm -f *.o *.a

distclean: clean
	rm -f *.s
