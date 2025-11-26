# --------------------------------------------------------------------
CC ?= clang-14
CFLAGS ?= -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE

BIN ?= bin

TARGETS ?= \
	$(BIN)/bench_XKCP \
	$(BIN)/bench_jasmin_avx2 \
	$(BIN)/bench_jasmin_ref


$(BIN)/bench_XKCP: XKCP | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/XKCP/ -I./common/ -DJADE_NAMESPACE=XKCP -DJADE_NAMESPACE_LC=XKCP ./common/crypto_sha.c ./src/XKCP/256sha_xkcp.a 

$(BIN)/bench_jasmin_avx2: jasmin_avx2 | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/jasmin/avx2 -I./common/ -DJADE_NAMESPACE=jasmin_avx2 -DJADE_NAMESPACE_LC=jasmin_avx2 ./common/crypto_sha.c ./src/jasmin/avx2/jasmin_avx2.a 

$(BIN)/bench_jasmin_ref: jasmin_ref | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/jasmin/ref -I./common/ -DJADE_NAMESPACE=jasmin_ref -DJADE_NAMESPACE_LC=jasmin_ref ./common/crypto_sha.c ./src/jasmin/ref/jasmin_ref.a 

$(BIN): ; @mkdir -p $@

XKCP: 
	make -C ./src/XKCP/

jasmin_avx2:
	make -C ./src/jasmin/avx2

jasmin_ref:
	make -C ./src/jasmin/ref

libs-clean:
	make -C ./src/XKCP/ clean
	make -C ./src/jasmin/avx2 clean
	make -C ./src/jasmin/ref clean

run: $(TARGETS)
	for d in $(TARGETS); do (./$$d > $$d.out); done