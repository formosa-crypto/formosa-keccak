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

PROGS = test_ref test_mref

all: $(PROGS)

test_ref: test_ref.c test_ref.s
	$(GCC) -o $@ $^

test_mref: test_mref.c test_mref.s
	$(GCC) -o $@ $^

%.s: %.jazz
	$(JASMINC) $(JFLAGS) -o $@ $<

clean:
	rm -f test_*.s

realclean: clean
	rm -rf $(PROGS)
