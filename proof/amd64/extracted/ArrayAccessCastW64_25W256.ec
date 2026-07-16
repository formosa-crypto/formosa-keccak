from Jasmin require import JWord JWord_array.

require import ArrayWords25W256.

clone export ArrayAccessCast as ArrayAccessCastW64_25W256  with op sizeWS <- 8,
                                                                op sizeWB <- 32,
                                                                op sizeB <- 25,
                                                                theory WordS <- W64,
                                                                theory WordB <- W256,
                                                                theory ArrayWordsB <= ArrayWords25W256.
