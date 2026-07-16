from Jasmin require import JWord JWord_array.

require import ArrayWords26W64.

clone export ArrayAccessCast as ArrayAccessCastW256_26W64  with op sizeWS <- 32,
                                                                op sizeWB <- 8,
                                                                op sizeB <- 26,
                                                                theory WordS <- W256,
                                                                theory WordB <- W64,
                                                                theory ArrayWordsB <= ArrayWords26W64.
