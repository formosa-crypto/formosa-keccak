# -*- Makefile -*-
include Makefile.conf

# --------------------------------------------------------------------
ECCONF := config/tests.config 
CHECKS ?= keccak

# --------------------------------------------------------------------
.PHONY: default check checkec checkxtr jasmin jasmin-old jasmin-barray clean_eco

default: check

check: jasmin checkec

jasmin: jasmin-old jasmin-barray

jasmin-old:
	make -C proof/amd64/extracted re_extract

jasmin-barray:
	make -C proof/amd64-barray/extracted re_extract

checkec:
	easycrypt runtest $(ECCONF) $(CHECKS)

clean_eco:
	find proof -name '*.eco' -exec rm '{}' ';'

