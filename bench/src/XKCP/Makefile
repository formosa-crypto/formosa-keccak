include ../../../Makefile.conf
# =========================================================
# Makefile to build 256sha_xkcp.a (wrapper around libXKCP)
# =========================================================

CKP      := $(TOPDIR)submodules/XKCP/lib/high/Keccak

HEADERS  := api.h \
            $(CKP)/FIPS202/SimpleFIPS202.h \
            $(CKP)/KeccakSponge.h \
			      $(TOPDIR)submodules/XKCP/lib/low/KeccakP-1600/AVX2/SnP/KeccakP-1600-SnP.h \
			      $(TOPDIR)submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.h

SOURCES  := sha3.c \
            $(CKP)/FIPS202/SimpleFIPS202.c\
			      $(CKP)/KeccakSponge.c \
			      $(TOPDIR)submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s


OBJECTS  := sha3.o \
            $(CKP)/FIPS202/SimpleFIPS202.o\
			      $(CKP)/KeccakSponge.o \
            # $(TOPDIR)submodules/XKCP/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.o


CFLAGS   += -Wall -Wextra -O3 -fomit-frame-pointer -mavx2 \
            -I$(CKP) \
			      -I$(CKP)/FIPS202 \
			      -I$(TOPDIR)submodules/XKCP/lib/low/KeccakP-1600/AVX2/SnP \
            -I$(TOPDIR)submodules/XKCP/lib/common \
            -I$(TOPDIR)submodules/XKCP/bin/x86-64/libXKCP.so.headers \
			      -I$(TOPDIR)submodules/XKCP/lib/low/KeccakP-1600/AVX2



.PHONY: all clean

all: $(TOPDIR)submodules/XKCP/bin/x86-64/libXKCP.so bench_xkcp.a

$(TOPDIR)submodules/XKCP/bin/x86-64/libXKCP.so:
	make -C $(TOPDIR)submodules/XKCP x86-64/libXKCP.so

%.o: %.c $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $< 

%.o: %.s $(HEADERS)
	$(CC) $(CFLAGS) -c -o $@ $<

bench_xkcp.a: $(OBJECTS)
	$(AR) -r $@ $(OBJECTS) $(TOPDIR)submodules/XKCP/bin/x86-64/libXKCP.so

clean:
	$(RM) $(OBJECTS)
	$(RM) bench_xkcp.a
