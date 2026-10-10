include ../../../Makefile.conf

.DEFAULT_GOAL := all

PROGS = test_ref test_mref

all: $(PROGS)

test_ref: test_ref.c test_ref.s
	$(CC) -o $@ $^

test_mref: test_mref.c test_mref.s
	$(CC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) $(JPATH) -o $@ $<

.PHONY: run
run: $(PROGS)
	@r=0; for p in $(PROGS); do ./$$p || { echo "FAILED: $$p"; r=1; }; done; exit $$r

clean:
	rm -f test_*.s

realclean: clean
	rm -rf $(PROGS)
