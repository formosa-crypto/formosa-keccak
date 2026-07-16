from Jasmin require import JWord JWord_array.

require import ArrayWords25W64.

clone export ArrayAccessCast as ArrayAccessCastW64_25W64  with op sizeWS <- 8,
                                                               op sizeWB <- 8,
                                                               op sizeB <- 25,
                                                               theory WordS <- W64,
                                                               theory WordB <- W64,
                                                               theory ArrayWordsB <= ArrayWords25W64.
