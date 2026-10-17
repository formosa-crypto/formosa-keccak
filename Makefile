# -*- Makefile -*-
include Makefile.conf

# --------------------------------------------------------------------
ECCONF := config/tests.config 
CHECKS ?= keccak

# --------------------------------------------------------------------
.PHONY: default check checkec checkxtr jasmin jasmin-old jasmin-barray jasmin-safety clean_eco

default: check

check: jasmin checkec

jasmin: jasmin-old jasmin-barray jasmin-safety

jasmin-old:
	make -C proof/amd64/extracted re_extract

jasmin-barray:
	make -C proof/amd64-barray/extracted re_extract

# safety model (jasmin2ec -m safety): needs the safety-assert2 branch of Jasmin
jasmin-safety:
	make -C proof/amd64/safety/extracted re_extract

checkec:
	easycrypt runtest $(ECCONF) $(CHECKS)

clean_eco:
	find proof -name '*.eco' -exec rm '{}' ';'

