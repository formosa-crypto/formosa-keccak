# --------------------------------------------------------------------
CC ?= clang-14
CFLAGS ?= -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE -mavx2 -march=native

BIN ?= bin

TARGETS ?= \
	$(BIN)/bench_XKCP \
	$(BIN)/bench_jasmin_avx2 \
	$(BIN)/bench_jasmin_ref \
	$(BIN)/bench_jasmin_old_avx2 \
	$(BIN)/bench_jasmin_old_ref


$(BIN)/bench_XKCP: XKCP | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/XKCP/ -I./common/ -DJADE_NAMESPACE=XKCP -DJADE_NAMESPACE_LC=XKCP ./common/crypto_sha.c ./src/XKCP/bench_xkcp.a 

$(BIN)/bench_jasmin_avx2: jasmin_avx2 | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/jasmin/avx2 -I./common/ -DJADE_NAMESPACE=jasmin_avx2 -DJADE_NAMESPACE_LC=jasmin_avx2 ./common/crypto_sha.c ./src/jasmin/avx2/jasmin_avx2.a 

$(BIN)/bench_jasmin_ref: jasmin_ref | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/jasmin/ref -I./common/ -DJADE_NAMESPACE=jasmin_ref -DJADE_NAMESPACE_LC=jasmin_ref ./common/crypto_sha.c ./src/jasmin/ref/jasmin_ref.a 

$(BIN)/bench_jasmin_old_avx2: jasmin_old_avx2 | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/jasmin/old_avx2 -I./common/ -DJADE_NAMESPACE=jasmin_old_avx2 -DJADE_NAMESPACE_LC=jasmin_old_avx2 ./common/crypto_sha.c ./src/jasmin/old_avx2/jasmin_old_avx2.a 

$(BIN)/bench_jasmin_old_ref: jasmin_old_ref | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./src/jasmin/old_ref -I./common/ -DJADE_NAMESPACE=jasmin_old_ref -DJADE_NAMESPACE_LC=jasmin_old_ref ./common/crypto_sha.c ./src/jasmin/old_ref/jasmin_old_ref.a 


$(BIN): ; @mkdir -p $@

XKCP: 
	make -C ./src/XKCP/

jasmin_avx2:
	make -C ./src/jasmin/avx2

jasmin_ref:
	make -C ./src/jasmin/ref

jasmin_old_avx2:
	make -C ./src/jasmin/old_avx2

jasmin_old_ref:
	make -C ./src/jasmin/old_ref

libs-clean:
	make -C ./src/XKCP/ clean
	make -C ./src/jasmin/avx2 clean
	make -C ./src/jasmin/ref clean
	make -C ./src/jasmin/old_avx2 clean
	make -C ./src/jasmin/old_ref clean

run: $(TARGETS)
	for d in $(TARGETS); do (./$$d > $$d.out); done