EASYCRYPT = easycrypt
EC_PARAMS =  -I ../../common -I ../

.PHONY: clean check

check:
	 $(EASYCRYPT) $(EC_PARAMS) Keccakf1600_Spec.ec
	 $(EASYCRYPT) $(EC_PARAMS) Keccak1600_Spec.ec
	 $(EASYCRYPT) $(EC_PARAMS) Example.ec

clean:
	-rm *.eco
