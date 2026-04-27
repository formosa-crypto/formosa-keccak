from Keccak require "common/subreadwrite_imem.jinc"
from Keccak require "avx2/keccak1600.jinc"
from Keccak require "avx2/keccak1600x4.jinc"
param int _RATE8=136;
param int _ASIZE=32;
from Keccak require "avx2/keccak1600_fixedsizes_ASIZE.jinc"
from Keccak require "avx2/keccak1600x4_fixedsizes_ASIZE.jinc"