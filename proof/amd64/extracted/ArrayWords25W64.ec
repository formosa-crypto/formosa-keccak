from Jasmin require import JWord JWord_array.

require import Array25 WArray200.

clone export ArrayWords as ArrayWords25W64  with op sizeW <- 8,
                                                 op sizeA <- 25,
                                                 theory Word <= W64,
                                                 theory ArrayN <= Array25,
                                                 theory WArrayN <= WArray200.
