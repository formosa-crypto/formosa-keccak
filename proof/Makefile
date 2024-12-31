# -*- Makefile -*-

# --------------------------------------------------------------------
ECCONF := config/tests.config 
JOBS   ?= 4
CHECKS ?= amd64

# --------------------------------------------------------------------
.PHONY: default check clean_eco

default: check

check:
	easycrypt runtest -jobs $(JOBS) $(ECCONF) $(CHECKS)

clean_eco:
	find . -name '*.eco' -exec rm '{}' ';'
