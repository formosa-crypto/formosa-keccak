from Jasmin require import JWord JWord_array.

require import ArrayWords26W64.

clone export ArrayAccessCast as ArrayAccessCastW32_26W64  with op sizeWS <- 4,
                                                               op sizeWB <- 8,
                                                               op sizeB <- 26,
                                                               theory WordS <- W32,
                                                               theory WordB <- W64,
                                                               theory ArrayWordsB <= ArrayWords26W64.
