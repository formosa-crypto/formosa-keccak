EASYCRYPT = easycrypt
EC_PARAMS =  -I ../common

.PHONY: clean typecheck

typecheck:
	 $(EASYCRYPT) $(EC_PARAMS) FIPS202_Keccakf1600.ec
	 $(EASYCRYPT) $(EC_PARAMS) FIPS202_SHA3.ec

#	 $(EASYCRYPT) $(EC_PARAMS) ../common/EclibExtra.ec
#	 $(EASYCRYPT) $(EC_PARAMS) ../common/JWordList.ec
#	 $(EASYCRYPT) $(EC_PARAMS) properties/Keccakf1600_Spec.ec
#	 $(EASYCRYPT) $(EC_PARAMS) properties/Keccak1600_Spec.ec
#	 $(EASYCRYPT) $(EC_PARAMS) properties/Example.ec

clean:
	-rm *.eco
