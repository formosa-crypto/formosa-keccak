include ../../../../Makefile.conf

JFLAGS += -nowarning -lea

all: jasmin_ref.a

.PHONY: jasmin_ref.a clean distclean
jasmin_ref.a: bench_ref.s
	$(CC) $(CFLAGS) -c bench_ref.s
	$(AR) -r $@ bench_ref.o

bench_ref.s: bench_ref.jazz
	$(JASMINC) $(JFLAGS) $(JPATH) $< -o $@

clean:
	rm -f *.o *.a

distclean: clean
	rm -f *.s
