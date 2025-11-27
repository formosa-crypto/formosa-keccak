.PHONY: jasmin_ref.a clean distclean

CFLAGS   := -Wall -Wextra -O3 -fomit-frame-pointer -mavx2 -march=native 

all: jasmin_ref.a

jasmin_ref.a: sha3_256.s
	$(CC) $(CFLAGS) -c sha3_256.s
	$(AR) -r $@ sha3_256.o

sha3_256.s: sha3_256.jazz
	$(JASMINC) -nowarning -lea $< -o $@

clean:
	rm -f *.o *.a

distclean: clean
	rm -f *.s
