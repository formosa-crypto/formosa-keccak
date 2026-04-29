# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF := config/tests.config 
CHECKS ?= keccak

# --------------------------------------------------------------------
.PHONY: default check checkec checkxtr jasmin assembly clean_eco

default: check

check: jasmin checkxtr checkec

jasmin:
	make -C proof/amd64/extracted

checkxtr:
	make -C proof/amd64/extracted check

checkec:
	easycrypt runtest $(ECCONF) $(CHECKS)

clean_eco:
	find proof -name '*.eco' -exec rm '{}' ';'
