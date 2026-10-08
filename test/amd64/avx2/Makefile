include ../../../Makefile.conf

.DEFAULT_GOAL := all

PROGS = test_avx2 test_mavx2 test_avx2x4

all: $(PROGS)

test_avx2: test_avx2.c test_avx2.s ../ref/test_ref.s
	$(CC) -o $@ $^

test_mavx2: test_mavx2.c test_mavx2.s ../ref/test_mref.s
	$(CC) -o $@ $^

test_avx2x4: test_avx2x4.c test_avx2x4.s ../ref/test_ref.s
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
