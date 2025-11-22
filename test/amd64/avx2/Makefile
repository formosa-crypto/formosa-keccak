UNAME = $(shell uname)
ifeq ($(UNAME_S),Linux)
endif
ifeq ($(UNAME_S),Darwin)
endif

UNAME_P := $(shell uname -p)
ifeq ($(UNAME_P),x86_64)
 GCC ?= gcc
endif
ifneq ($(filter %86,$(UNAME_P)),)
 GCC ?= gcc
endif
ifneq ($(filter arm%,$(UNAME_P)),)
 GCC ?= arch -x86_64 gcc
endif

PWD = $(shell pwd)
SRCDIR = $(PWD)/../../../src/amd64

JASMINC ?= jasminc -I Keccak=$(SRCDIR)


.DEFAULT_GOAL := all

PROGS = test_avx2 test_mavx2 test_avx2x4

all: $(PROGS)

test_avx2: test_avx2.c test_avx2.s ../ref/test_ref.s
	$(GCC) -o $@ $^

test_mavx2: test_mavx2.c test_mavx2.s ../ref/test_mref.s
	$(GCC) -o $@ $^

test_avx2x4: test_avx2x4.c test_avx2x4.s ../ref/test_ref.s
	$(GCC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) -o $@ $<

clean:
	rm -f test_*.s

realclean: clean
	rm -rf $(PROGS)
