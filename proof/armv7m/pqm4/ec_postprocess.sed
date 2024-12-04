/module M = /i\
require import Bindings.\n
s/Array8.init/init_8_32/g
s/`|>>|`/\\ror/g
s/BIC/(\\BIC)/g
0,/\(smD_[[:digit:]]\+\) <- smD_[[:digit:]]\+;$/{s//\1 <- init_5_32 (fun _=>W32.zero);/} 
s/.* <- witness;$//g
