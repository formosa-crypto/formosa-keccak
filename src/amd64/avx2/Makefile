# -*- Makefile -*-

# --------------------------------------------------------------------
-include ../../../../Makefile.conf

CKP    := ../../../submodules/XKCP/lib/high/Keccak
CC     ?= /usr/bin/gcc
EXTRACTED ?= ../../../proof/amd64/extracted
CFLAGS   := -Wall -Wextra -O3 -fomit-frame-pointer -mavx2 \
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
.PHONY: all ec_keccak_array_avx2 ec_keccak_array_avx2x4 ec_keccak_mem_avx2 ec_keccak_array_avx2x4 clean

# --------------------------------------------------------------------

all: ec_keccak_array_avx2 ec_keccak_array_avx2x4 ec_keccak_mem_avx2 ec_keccak_mem_avx2x4


test: run-test

JINC = keccak1600_fixedsizes_ASIZE.jinc keccak1600.jinc ../common/subreadwrite_ASIZE.jinc

SOURCES  := $(CKP)/FIPS202/SimpleFIPS202.c\
			 $(CKP)/KeccakSponge.c \
			 ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s



test/test_sha3: test/test_sha3.c $(SOURCES) sha3.a
	$(CC) $(CFLAGS) $(LDFLAGS) -o $@ test/test_sha3.c $(SOURCES) sha3.a

sha3.a: sha3.s
	$(CC) $(CFLAGS) -c sha3.s
	$(AR) -r $@ sha3.o

run-test: test/test_sha3
	@LD_LIBRARY_PATH=../../../submodules/XKCP/bin/x86-64 ./test/test_sha3

sha3.s: keccak1600_avx2_test.jazz $(JINC)
	$(JASMINC) -o $@ $(JFLAGS) keccak1600_avx2_test.jazz 

ct: ct_keccak_array ct_keccak_mem


ct_keccak_array:
	$(JASMINCT) --infer $(EXTRACTED)/toEC_keccak1600_ASIZE_avx2.jazz

ct_keccak_mem:
	$(JASMINCT) --infer $(EXTRACTED)/toEC_keccak1600_avx2.jazz

ec: ec_keccak_array_avx2 ec_keccak_array_avx2x4 ec_keccak_mem_avx2 ec_keccak_mem_avx2x4

ec_keccak_array_avx2:
	$(JASMIN2EC) $(EXTRACTED)/toEC_keccak1600_ASIZE_avx2.jazz --array-model=old -o keccak_amd64_avx2.ec \
				-f __addstate_avx2 \
				-f __absorb_avx2 \
				-f __dumpstate_avx2 \
				-f __squeeze_avx2

ec_keccak_array_avx2x4:
	$(JASMIN2EC) $(EXTRACTED)/toEC_keccak1600_ASIZE_avx2.jazz --array-model=old -o keccak_amd64_avx2x4.ec \
				-f  __addstate_bcast_avx2x4 \
				-f  __absorb_bcast_avx2x4 \
				-f  __addstate_avx2x4 \
				-f  __absorb_avx2x4 \
				-f  __dumpstate_avx2x4 \
				-f  __squeeze_avx2x4

ec_keccak_mem_avx2:
	$(JASMIN2EC) $(EXTRACTED)/toEC_keccak1600_avx2.jazz --array-model=old -o keccak_amd64_mem_avx2.ec \
				-f __addstate_avx2 \
				-f __absorb_avx2 \
				-f __dumpstate_avx2 \
				-f __squeeze_avx2

ec_keccak_mem_avx2x4:
	$(JASMIN2EC) $(EXTRACTED)/toEC_keccak1600_avx2.jazz --array-model=old -o keccak_amd64_mem_avx2x4.ec \
				-f  __addstate_m_bcast_avx2x4 \
				-f  __absorb_m_bcast_avx2x4 \
				-f  __addstate_m_avx2x4 \
				-f  __absorb_m_avx2x4 \
				-f  __dumpstate_m_avx2x4 \
				-f  __squeeze_m_avx2x4

clean:
	rm -f *.ec
