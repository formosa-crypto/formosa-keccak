CC ?= clang-14
CFLAGS ?= -O3 -fomit-frame-pointer -fwrapv -fPIC -fPIE -mavx2


BIN ?= bin
TARGET = $(BIN)/bench_permut

.PHONY: all run clean


all: $(TARGET)

$(TARGET): bench_permut.c jasmin_new_avx2.a jasmin_old_avx2.a | $(BIN)
	$(CC) $(CFLAGS) -o $@ -I./../common/ new_permut.s old_permut.s $<

run: $(TARGET)
	./$(TARGET)

$(BIN): ; @mkdir -p $@


jasmin_new_avx2.a: new_permut.s
	$(CC) $(CFLAGS) -c new_permut.s
	$(AR) -r $@ new_permut.o

new_permut.s: new.jazz 
	$(JASMINC) -nowarning -lea $< -o $@

jasmin_old_avx2.a: old_permut.s
	$(CC) $(CFLAGS) -c old_permut.s
	$(AR) -r $@ old_permut.o

old_permut.s: old.jazz
	$(JASMINC) -nowarning -lea $< -o $@