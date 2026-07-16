from Jasmin require import JWord JWord_array.

require import ArrayWords101W64.

clone export ArrayAccessCast as ArrayAccessCastW8_101W64  with op sizeWS <- 1,
                                                               op sizeWB <- 8,
                                                               op sizeB <- 101,
                                                               theory WordS <- W8,
                                                               theory WordB <- W64,
                                                               theory ArrayWordsB <= ArrayWords101W64.
