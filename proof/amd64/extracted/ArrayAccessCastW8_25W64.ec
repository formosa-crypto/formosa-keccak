from Jasmin require import JWord JWord_array.

require import ArrayWords25W64.

clone export ArrayAccessCast as ArrayAccessCastW8_25W64  with op sizeWS <- 1,
                                                              op sizeWB <- 8,
                                                              op sizeB <- 25,
                                                              theory WordS <- W8,
                                                              theory WordB <- W64,
                                                              theory ArrayWordsB <= ArrayWords25W64.
