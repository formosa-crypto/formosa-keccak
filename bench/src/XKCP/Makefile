# =========================================================
# Makefile to build 256sha_xkcp.a (wrapper around libXKCP)
# =========================================================

CKP      := ../../../submodules/XKCP/lib/high/Keccak

HEADERS  := api.h sha3.h \
             $(CKP)/FIPS202/SimpleFIPS202.h \
             $(CKP)/KeccakSponge.h \
			 ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/SnP/KeccakP-1600-SnP.h \
			 ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.h

SOURCES  := sha3.c \
             $(CKP)/FIPS202/SimpleFIPS202.c\
			 $(CKP)/KeccakSponge.c \
			 ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s


OBJECTS  := sha3.o \
             $(CKP)/FIPS202/SimpleFIPS202.o\
			 $(CKP)/KeccakSponge.o \
			 ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.o


CC       ?= gcc
CFLAGS   := -Wall -Wextra -O3 -fomit-frame-pointer \
             -I$(CKP) \
			 -I$(CKP)/FIPS202 \
			 -I../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2/SnP \
             -I../../../submodules/XKCP/lib/common \
             -I../../../submodules/XKCP/bin/x86-64/libXKCP.so.headers \
			 -I ../../../submodules/XKCP/lib/low/KeccakP-1600/AVX2



.PHONY: all clean

all: 256sha_xkcp.a

%.o: %.c $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $< 

%.o: %.s $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

256sha_xkcp.a: $(OBJECTS)
	$(AR) -r $@ $(OBJECTS)

clean:
	$(RM) $(OBJECTS)
	$(RM) 256sha_xkcp.a
