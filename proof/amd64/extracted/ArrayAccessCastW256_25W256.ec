from Jasmin require import JWord JWord_array.

require import ArrayWords25W256.

clone export ArrayAccessCast as ArrayAccessCastW256_25W256  with op sizeWS <- 32,
                                                                 op sizeWB <- 32,
                                                                 op sizeB <- 25,
                                                                 theory WordS <- W256,
                                                                 theory WordB <- W256,
                                                                 theory ArrayWordsB <= ArrayWords25W256.
