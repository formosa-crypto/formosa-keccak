from Jasmin require import JWord JWord_array.

require import ArrayWords101W64.

clone export ArrayAccessCast as ArrayAccessCastW32_101W64  with op sizeWS <- 4,
                                                                op sizeWB <- 8,
                                                                op sizeB <- 101,
                                                                theory WordS <- W32,
                                                                theory WordB <- W64,
                                                                theory ArrayWordsB <= ArrayWords101W64.
