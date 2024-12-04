JASMINC = jasminc -arch arm-m4
JAZZ2EC = jasmin2ec --arch arm-m4
SED_REJAZZ = sed -f to_jazzexpand.sed
SED_ECPP = sed -f ec_postprocess.sed

all: keccakf1600_pqm4_inlined.ec

keccakf1600_pqm4.jazz.expanded: keccakf1600_pqm4.jazz
	$(JASMINC) -parrexp $< > $@ 

keccakf1600_pqm4_xpnd.jazz: keccakf1600_pqm4.jazz.expanded
	$(SED_REJAZZ) $< > $@

keccakf1600_pqm4_extracted.ec: keccakf1600_pqm4_xpnd.jazz
	$(JAZZ2EC) $< -f KeccakF1600_StatePermute -f _stateTopqm4 -f _pqm4Tostate -o $@

keccakf1600_pqm4_inlined.ec: keccakf1600_pqm4_extracted.ec
	$(SED_ECPP) $< > $@

clean:
	rm -f keccakf1600_pqm4.jazz.expanded keccakf1600_pqm4_xpnd.jazz keccakf1600_pqm4_extracted.ec keccakf1600_pqm4_inlined.ec Array*.ec WArray*.ec

direct: keccakf1600_pqm4.jinc
	$(JAZZ2EC) keccakf1600_pqm4.jinc -f _KeccakF1600_StatePermute -f _stateTopqm4 -f _pqm4Tostate -o keccakf1600_pqm4.ec


