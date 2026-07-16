from Jasmin require import JWord JWord_array.

require import ArrayWords26W64.

clone export ArrayAccessCast as ArrayAccessCastW8_26W64  with op sizeWS <- 1,
                                                              op sizeWB <- 8,
                                                              op sizeB <- 26,
                                                              theory WordS <- W8,
                                                              theory WordB <- W64,
                                                              theory ArrayWordsB <= ArrayWords26W64.
