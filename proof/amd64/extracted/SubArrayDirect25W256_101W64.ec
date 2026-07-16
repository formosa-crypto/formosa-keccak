from Jasmin require import JWord JWord_array.

require import ArrayWords25W256 ArrayWords101W64.

clone export SubArrayCast as SubArrayDirect25W256_101W64  with op sizeWS <- 32,
                                                               op sizeWB <- 8,
                                                               op sizeS <- 25,
                                                               op sizeB <- 101,
                                                               theory WordS <- W256,
                                                               theory WordB <- W64,
                                                               theory ArrayWordsS <= ArrayWords25W256,
                                                               theory ArrayWordsB <= ArrayWords101W64.
