# -*- Makefile -*-

# --------------------------------------------------------------------
-include ../../../../Makefile.conf

CKP    := ../../../submodules/XKCP/lib/high/Keccak
CC     ?= /usr/bin/gcc
CFLAGS   := -Wall -Wextra -O3 -fomit-frame-pointer \
             -I$(CKP) \
			 -I$(CKP)/FIPS202 \
			 -I../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/SnP \
             -I../../../submodules/XKCP/lib/common \
             -I../../../submodules/XKCP/bin/x86-64/libXKCP.so.headers \
			 -I ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2
LDFLAGS := -L../../../submodules/XKCP/bin/x86-64 -lXKCP
JFLAGS := ${JADDFLAGS}
OS     := $(shell uname -s)

# --------------------------------------------------------------------
.PHONY: all ec_keccak_array ec_keccak_mem clean ct ec ct_keccak_array ct_keccak_mem

# --------------------------------------------------------------------

all: ec_keccak_array ec_keccak_mem

test: run-test

JINC = keccak1600_fixedsizes_ASIZE.jinc keccak1600.jinc ../common/subreadwrite_ASIZE.jinc

SOURCES  := $(CKP)/FIPS202/SimpleFIPS202.c\
			 $(CKP)/KeccakSponge.c \
			 ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s
			 
test/test_sha3: test/test_sha3.c $(SOURCES) sha3.s
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ $(SOURCES) sha3.s $<

run-test: test/test_sha3
	@LD_LIBRARY_PATH=../../../submodules/XKCP/bin/x86-64 ./test/test_sha3

sha3.s: keccak1600_ref_test.jazz $(JINC)
	$(JASMINC) -o $@ $(JFLAGS) keccak1600_ref_test.jazz 

ct: ct_keccak_array ct_keccak_mem

ct_keccak_array:
	$(JASMINCT) --infer toEC_ASIZE.jazz

ct_keccak_mem:
	$(JASMINCT) --infer toEC.jazz


ec: ec_keccak_array ec_keccak_mem

ec_keccak_array: 
	$(JASMIN2EC) ./toEC_ASIZE.jazz --array-model=old -o keccak_amd64_ref.ec \
				-f __addstate_array_ref \
				-f __absorb_array_ref \
				-f __dumpstate_array_ref \
				-f __squeeze_array_ref

ec_keccak_mem:
	$(JASMIN2EC) ./toEC.jazz --array-model=old -o keccak_amd64_mem_ref.ec \
				-f __addstate_imem_ref \
 				-f __absorb_imem_ref \
 				-f __dumpstate_imem_ref \
 				-f __squeeze_imem_ref


clean:
	rm -f *.ec
