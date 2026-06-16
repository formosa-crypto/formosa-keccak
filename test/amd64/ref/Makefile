include ../../../Makefile.conf

.DEFAULT_GOAL := all

PROGS = test_ref test_mref test_kf

all: $(PROGS)

test_ref: test_ref.c test_ref.s
	$(CC) -o $@ $^

test_mref: test_mref.c test_mref.s
	$(CC) -o $@ $^

test_kf: test_kf.c test_kf.s
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) $(JPATH) -o $@ $<

clean:
	rm -f test_*.s

realclean: clean
	rm -rf $(PROGS)
