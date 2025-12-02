CC ?= clang-14
CFLAGS ?= -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE -mavx2


BIN ?= bin
TARGETS ?= \
 $(BIN)/bench_avx2x4 \
 $(BIN)/bench_old_avx2x4


.PHONY: all run clean


run: $(TARGETS)
	for d in $(TARGETS); do (./$$d > $$d.out); done

$(BIN)/bench_avx2x4: bench_avx2x4.c jasmin_test.a | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./../common/ $< jasmin_test.a 

$(BIN)/bench_old_avx2x4: bench_avx2x4.c jasmin_old_test.a | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./../common/ $< jasmin_old_test.a


$(BIN): ; @mkdir -p $@


jasmin_test.a: jasmin_test.s
	$(CC) $(CFLAGS) -c jasmin_test.s
	$(AR) -r $@ jasmin_test.o

jasmin_test.s: ../../../test/amd64/avx2/test_avx2x4.jazz 
	$(JASMINC) -I Keccak:../../../src/amd64 -nowarning -lea $< -o $@

jasmin_old_test.a: jasmin_old_test.s
	$(CC) $(CFLAGS) -c jasmin_old_test.s
	$(AR) -r $@ jasmin_old_test.o

jasmin_old_test.s: ../../../test/amd64/avx2/test_avx2x4_old.jazz 
	$(JASMINC) -nowarning -lea $< -o $@
