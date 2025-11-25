require import AllCore IntDiv CoreMap List Distr.

from Jasmin require import JModel_x86.

import SLH64.

from Jasmin require import Jcheck JSafety.

require import
Array5 Array6 Array7 Array24 Array25 Array200 Array224 WArray192 BArray192 BArray200
BArray224 BArray800 BArray160.

abbrev  kECCAK_RHOTATES_RIGHT =
(BArray192.of_list256
[(W256.of_int 144373339913893657577751063007562604548177214458152943091773);
(W256.of_int 232252764209307188274174373867837442080505530800860351692863);
(W256.of_int 156927543384667019098616994515559168111335794127330162507795);
(W256.of_int 351517697181654122777866749001917765472957616589092975280182);
(W256.of_int 276192476357013953622045746931053922384479139705868246843454);
(W256.of_int 313855086769334038206421612937983674734430261968315659321364)]).

abbrev  kECCAK_RHOTATES_LEFT =
(BArray192.of_list256
[(W256.of_int 257361171150853911329517531560668107745210100483895842570243);
(W256.of_int 169481746855440380633094220700393270212881784141188433969153);
(W256.of_int 244806967680080549808651600052671544182051520814718623154221);
(W256.of_int 50216813883093446129401845566312946820429698352955810381834);
(W256.of_int 125542034707733615285222847637176789908908175236180538818562);
(W256.of_int 87879424295413530700846981630247037558957052973733126340652)]).

abbrev  kECCAK1600_RC =
(BArray192.of_list64
[(W64.of_int 1); (W64.of_int 32898); (W64.of_int (-9223372036854742902));
(W64.of_int (-9223372034707259392)); (W64.of_int 32907);
(W64.of_int 2147483649); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854743031)); (W64.of_int 138); (W64.of_int 136);
(W64.of_int 2147516425); (W64.of_int 2147483658); (W64.of_int 2147516555);
(W64.of_int (-9223372036854775669)); (W64.of_int (-9223372036854742903));
(W64.of_int (-9223372036854743037)); (W64.of_int (-9223372036854743038));
(W64.of_int (-9223372036854775680)); (W64.of_int 32778);
(W64.of_int (-9223372034707292150)); (W64.of_int (-9223372034707259263));
(W64.of_int (-9223372036854742912)); (W64.of_int 2147483649);
(W64.of_int (-9223372034707259384))]).

abbrev [-printing] rOL8 =
(W256.of_int
13620818001941277694121380808605999856886653716761013959207994299728839901191
).

abbrev [-printing] rOL56 =
(W256.of_int
10910488462195273559651782724632284871561478246514020268633800075540923875841
).

module M = {
  var tmp__trace : trace
  proc keccakf1600_index (x:int, y:int) : int * trace = {
    var r:int;
    var trace_keccakf1600_index:trace;
    trace_keccakf1600_index <- [];
    r <- ((x %% 5) + (5 * (y %% 5)));
    return (r, trace_keccakf1600_index);
  }
  proc keccakf1600_rho_offsets (i:int) : int * trace = {
    var r:int;
    var x:int;
    var y:int;
    var t:int;
    var z:int;
    var trace_keccakf1600_rho_offsets:trace;
    trace_keccakf1600_rho_offsets <- [];
    r <- 0;
    x <- 1;
    y <- 0;
    t <- 0;
    while ((t < 24)) {
      if ((i = (x + (5 * y)))) {
        r <- ((((t + 1) * (t + 2)) %/ 2) %% 64);
      } else {
        
      }
      z <- (((2 * x) + (3 * y)) %% 5);
      x <- y;
      y <- z;
      t <- (t + 1);
    }
    return (r, trace_keccakf1600_rho_offsets);
  }
  proc keccakf1600_rhotates (x:int, y:int) : int * trace = {
    var r:int;
    var i:int;
    var param:int;
    var result:int;
    var param_0:int;
    var param_1:int;
    var result_0:int;
    var trace_keccakf1600_rhotates:trace;
    trace_keccakf1600_rhotates <- [];
    param_1 <- x;
    param_0 <- y;
    (result_0, tmp__trace) <@ keccakf1600_index (param_1, param_0);
    trace_keccakf1600_rhotates <- (trace_keccakf1600_rhotates ++ tmp__trace);
    i <- result_0;
    param <- i;
    (result, tmp__trace) <@ keccakf1600_rho_offsets (param);
    trace_keccakf1600_rhotates <- (trace_keccakf1600_rhotates ++ tmp__trace);
    r <- result;
    return (r, trace_keccakf1600_rhotates);
  }
  proc __keccakf1600_pround_avx2 (state:BArray224.t, b_state:BArray224.t) : 
  BArray224.t * BArray224.t * trace = {
    var c00:W256.t;
    var c14:W256.t;
    var t2:W256.t;
    var t4:W256.t;
    var t0:W256.t;
    var t1:W256.t;
    var d14:W256.t;
    var d00:W256.t;
    var t3:W256.t;
    var t5:W256.t;
    var t6:W256.t;
    var t7:W256.t;
    var t8:W256.t;
    var trace___keccakf1600_pround_avx2:trace;
    trace___keccakf1600_pround_avx2 <- [];
    trace___keccakf1600_pround_avx2 <-
    (trace___keccakf1600_pround_avx2 ++ [(Assert, (is_init b_state 0 224))]);
    c00 <- (VPSHUFD_256 (BArray224.get256 state 2) (W8.of_int 78));
    c14 <- ((BArray224.get256 state 5) `^` (BArray224.get256 state 3));
    t2 <- ((BArray224.get256 state 4) `^` (BArray224.get256 state 6));
    c14 <- (c14 `^` (BArray224.get256 state 1));
    c14 <- (c14 `^` t2);
    t4 <- (VPERMQ c14 (W8.of_int 147));
    c00 <- (c00 `^` (BArray224.get256 state 2));
    t0 <- (VPERMQ c00 (W8.of_int 78));
    t1 <- (c14 \vshr64u256 (W128.of_int 63));
    t2 <- (c14 \vadd64u256 c14);
    t1 <- (t1 `|` t2);
    d14 <- (VPERMQ t1 (W8.of_int 57));
    d00 <- (t1 `^` t4);
    d00 <- (VPERMQ d00 (W8.of_int 0));
    c00 <- (c00 `^` (BArray224.get256 state 0));
    c00 <- (c00 `^` t0);
    t0 <- (c00 \vshr64u256 (W128.of_int 63));
    t1 <- (c00 \vadd64u256 c00);
    t1 <- (t1 `|` t0);
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `^` d00));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` d00));
    d14 <- (VPBLEND_8u32 d14 t1 (W8.of_int 192));
    t4 <- (VPBLEND_8u32 t4 c00 (W8.of_int 3));
    d14 <- (d14 `^` t4);
    t3 <-
    (VPSLLV_4u64 (BArray224.get256 state 2)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 0));
    state <-
    (BArray224.set256 state 2
    (VPSRLV_4u64 (BArray224.get256 state 2)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 0)));
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `|` t3));
    state <- (BArray224.set256 state 3 ((BArray224.get256 state 3) `^` d14));
    t4 <-
    (VPSLLV_4u64 (BArray224.get256 state 3)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 2));
    state <-
    (BArray224.set256 state 3
    (VPSRLV_4u64 (BArray224.get256 state 3)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 2)));
    state <- (BArray224.set256 state 3 ((BArray224.get256 state 3) `|` t4));
    state <- (BArray224.set256 state 4 ((BArray224.get256 state 4) `^` d14));
    t5 <-
    (VPSLLV_4u64 (BArray224.get256 state 4)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 3));
    state <-
    (BArray224.set256 state 4
    (VPSRLV_4u64 (BArray224.get256 state 4)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 3)));
    state <- (BArray224.set256 state 4 ((BArray224.get256 state 4) `|` t5));
    state <- (BArray224.set256 state 5 ((BArray224.get256 state 5) `^` d14));
    t6 <-
    (VPSLLV_4u64 (BArray224.get256 state 5)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 4));
    state <-
    (BArray224.set256 state 5
    (VPSRLV_4u64 (BArray224.get256 state 5)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 4)));
    state <- (BArray224.set256 state 5 ((BArray224.get256 state 5) `|` t6));
    state <- (BArray224.set256 state 6 ((BArray224.get256 state 6) `^` d14));
    t3 <- (VPERMQ (BArray224.get256 state 2) (W8.of_int 141));
    t4 <- (VPERMQ (BArray224.get256 state 3) (W8.of_int 141));
    t7 <-
    (VPSLLV_4u64 (BArray224.get256 state 6)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 5));
    t1 <-
    (VPSRLV_4u64 (BArray224.get256 state 6)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 5));
    t1 <- (t1 `|` t7);
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` d14));
    t5 <- (VPERMQ (BArray224.get256 state 4) (W8.of_int 27));
    t6 <- (VPERMQ (BArray224.get256 state 5) (W8.of_int 114));
    t8 <-
    (VPSLLV_4u64 (BArray224.get256 state 1)
    (BArray192.get256 kECCAK_RHOTATES_LEFT 1));
    t2 <-
    (VPSRLV_4u64 (BArray224.get256 state 1)
    (BArray192.get256 kECCAK_RHOTATES_RIGHT 1));
    t2 <- (t2 `|` t8);
    t7 <- (VPSRLDQ_256 t1 (W8.of_int 8));
    t0 <- ((invw t1) `&` t7);
    state <- (BArray224.set256 state 3 (VPBLEND_8u32 t2 t6 (W8.of_int 12)));
    t8 <- (VPBLEND_8u32 t4 t2 (W8.of_int 12));
    state <- (BArray224.set256 state 5 (VPBLEND_8u32 t3 t4 (W8.of_int 12)));
    t7 <- (VPBLEND_8u32 t2 t3 (W8.of_int 12));
    state <-
    (BArray224.set256 state 3
    (VPBLEND_8u32 (BArray224.get256 state 3) t4 (W8.of_int 48)));
    t8 <- (VPBLEND_8u32 t8 t5 (W8.of_int 48));
    state <-
    (BArray224.set256 state 5
    (VPBLEND_8u32 (BArray224.get256 state 5) t2 (W8.of_int 48)));
    t7 <- (VPBLEND_8u32 t7 t6 (W8.of_int 48));
    state <-
    (BArray224.set256 state 3
    (VPBLEND_8u32 (BArray224.get256 state 3) t5 (W8.of_int 192)));
    t8 <- (VPBLEND_8u32 t8 t6 (W8.of_int 192));
    state <-
    (BArray224.set256 state 5
    (VPBLEND_8u32 (BArray224.get256 state 5) t6 (W8.of_int 192)));
    t7 <- (VPBLEND_8u32 t7 t4 (W8.of_int 192));
    state <-
    (BArray224.set256 state 3 ((invw (BArray224.get256 state 3)) `&` t8));
    state <-
    (BArray224.set256 state 5 ((invw (BArray224.get256 state 5)) `&` t7));
    state <- (BArray224.set256 state 6 (VPBLEND_8u32 t5 t2 (W8.of_int 12)));
    t8 <- (VPBLEND_8u32 t3 t5 (W8.of_int 12));
    state <- (BArray224.set256 state 3 ((BArray224.get256 state 3) `^` t3));
    state <-
    (BArray224.set256 state 6
    (VPBLEND_8u32 (BArray224.get256 state 6) t3 (W8.of_int 48)));
    t8 <- (VPBLEND_8u32 t8 t4 (W8.of_int 48));
    state <- (BArray224.set256 state 5 ((BArray224.get256 state 5) `^` t5));
    state <-
    (BArray224.set256 state 6
    (VPBLEND_8u32 (BArray224.get256 state 6) t4 (W8.of_int 192)));
    t8 <- (VPBLEND_8u32 t8 t2 (W8.of_int 192));
    state <-
    (BArray224.set256 state 6 ((invw (BArray224.get256 state 6)) `&` t8));
    state <- (BArray224.set256 state 6 ((BArray224.get256 state 6) `^` t6));
    state <- (BArray224.set256 state 4 (VPERMQ t1 (W8.of_int 30)));
    t8 <-
    (VPBLEND_8u32 (BArray224.get256 state 4) (BArray224.get256 state 0)
    (W8.of_int 48));
    state <- (BArray224.set256 state 1 (VPERMQ t1 (W8.of_int 57)));
    state <-
    (BArray224.set256 state 1
    (VPBLEND_8u32 (BArray224.get256 state 1) (BArray224.get256 state 0)
    (W8.of_int 192)));
    state <-
    (BArray224.set256 state 1 ((invw (BArray224.get256 state 1)) `&` t8));
    state <- (BArray224.set256 state 2 (VPBLEND_8u32 t4 t5 (W8.of_int 12)));
    t7 <- (VPBLEND_8u32 t6 t4 (W8.of_int 12));
    state <-
    (BArray224.set256 state 2
    (VPBLEND_8u32 (BArray224.get256 state 2) t6 (W8.of_int 48)));
    t7 <- (VPBLEND_8u32 t7 t3 (W8.of_int 48));
    state <-
    (BArray224.set256 state 2
    (VPBLEND_8u32 (BArray224.get256 state 2) t3 (W8.of_int 192)));
    t7 <- (VPBLEND_8u32 t7 t5 (W8.of_int 192));
    state <-
    (BArray224.set256 state 2 ((invw (BArray224.get256 state 2)) `&` t7));
    state <- (BArray224.set256 state 2 ((BArray224.get256 state 2) `^` t2));
    t0 <- (VPERMQ t0 (W8.of_int 0));
    state <-
    (BArray224.set256 state 3
    (VPERMQ (BArray224.get256 state 3) (W8.of_int 27)));
    state <-
    (BArray224.set256 state 5
    (VPERMQ (BArray224.get256 state 5) (W8.of_int 141)));
    state <-
    (BArray224.set256 state 6
    (VPERMQ (BArray224.get256 state 6) (W8.of_int 114)));
    state <- (BArray224.set256 state 4 (VPBLEND_8u32 t6 t3 (W8.of_int 12)));
    t7 <- (VPBLEND_8u32 t5 t6 (W8.of_int 12));
    state <-
    (BArray224.set256 state 4
    (VPBLEND_8u32 (BArray224.get256 state 4) t5 (W8.of_int 48)));
    t7 <- (VPBLEND_8u32 t7 t2 (W8.of_int 48));
    state <-
    (BArray224.set256 state 4
    (VPBLEND_8u32 (BArray224.get256 state 4) t2 (W8.of_int 192)));
    t7 <- (VPBLEND_8u32 t7 t3 (W8.of_int 192));
    state <-
    (BArray224.set256 state 4 ((invw (BArray224.get256 state 4)) `&` t7));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` t0));
    state <- (BArray224.set256 state 1 ((BArray224.get256 state 1) `^` t1));
    state <- (BArray224.set256 state 4 ((BArray224.get256 state 4) `^` t4));
    b_state <- (BArray224.init_arr (W8.of_int 255) 224);
    return (state, b_state, trace___keccakf1600_pround_avx2);
  }
  proc _keccakf1600_avx2 (state:BArray224.t, b_state:BArray224.t) : BArray224.t *
                                                                    BArray224.t *
                                                                    trace = {
    var round_constants:BArray192.t;
    var rc:W256.t;
    var r:int;
    var param:BArray224.t;
    var result:BArray224.t;
    var b_result:BArray224.t;
    var trace__keccakf1600_avx2:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    round_constants <- witness;
    trace__keccakf1600_avx2 <- [];
    trace__keccakf1600_avx2 <-
    (trace__keccakf1600_avx2 ++ [(Assert, (is_init b_state 0 224))]);
    round_constants <- kECCAK1600_RC;
    r <- 0;
    param <- state;
    (result, b_result, tmp__trace) <@ __keccakf1600_pround_avx2 (param,
    (BArray224.init_arr (W8.of_int 255) 224));
    trace__keccakf1600_avx2 <- (trace__keccakf1600_avx2 ++ tmp__trace);
    trace__keccakf1600_avx2 <-
    (trace__keccakf1600_avx2 ++ [(Assert, (is_init b_result 0 224))]);
    state <- result;
    trace__keccakf1600_avx2 <-
    (trace__keccakf1600_avx2 ++
    [(Assert, ((0 <= (r * 8)) /\ (((r * 8) + 8) <= 192)))]);
    rc <- (VPBROADCAST_4u64 (BArray192.get64 round_constants r));
    state <- (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` rc));
    trace__keccakf1600_avx2 <-
    (trace__keccakf1600_avx2 ++
    [(Assert, ((0 <= (r + 1)) /\ ((r + 1) <= 18446744073709551615)))]);
    r <- (r + 1);
    while ((r < 24)) {
      param <- state;
      (result, b_result, tmp__trace) <@ __keccakf1600_pround_avx2 (param,
      (BArray224.init_arr (W8.of_int 255) 224));
      trace__keccakf1600_avx2 <- (trace__keccakf1600_avx2 ++ tmp__trace);
      trace__keccakf1600_avx2 <-
      (trace__keccakf1600_avx2 ++ [(Assert, (is_init b_result 0 224))]);
      state <- result;
      trace__keccakf1600_avx2 <-
      (trace__keccakf1600_avx2 ++
      [(Assert, ((0 <= (r * 8)) /\ (((r * 8) + 8) <= 192)))]);
      rc <- (VPBROADCAST_4u64 (BArray192.get64 round_constants r));
      state <-
      (BArray224.set256 state 0 ((BArray224.get256 state 0) `^` rc));
      trace__keccakf1600_avx2 <-
      (trace__keccakf1600_avx2 ++
      [(Assert, ((0 <= (r + 1)) /\ ((r + 1) <= 18446744073709551615)))]);
      r <- (r + 1);
    }
    b_state <- (BArray224.init_arr (W8.of_int 255) 224);
    return (state, b_state, trace__keccakf1600_avx2);
  }
  proc __stavx2_pack (st:BArray200.t, b_st:BArray200.t) : BArray224.t *
                                                          BArray224.t * trace = {
    var state:BArray224.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    var r:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var b_state:BArray224.t;
    var trace___stavx2_pack:trace;
    b_state <- witness;
    state <- witness;
    trace___stavx2_pack <- [];
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_st 0 200))]);
    b_state <- (BArray224.init_arr (W8.of_int 0) 224);
    b_state <-
    (BArray224.set256d b_state 0
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <-
    (BArray224.set256 state 0 (VPBROADCAST_4u64 (BArray200.get64d st 0)));
    b_state <-
    (BArray224.set256d b_state 32
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <- (BArray224.set256 state 1 (BArray200.get256d st 8));
    t128_0 <- (VMOV_64 (BArray200.get64 st 5));
    b_state <-
    (BArray224.set256d b_state 96
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <- (BArray224.set256 state 3 (BArray200.get256d st 48));
    t128_1 <- (VMOV_64 (BArray200.get64 st 10));
    b_state <-
    (BArray224.set256d b_state 128
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <- (BArray224.set256 state 4 (BArray200.get256d st 88));
    r <- (BArray200.get64 st 15);
    t128_0 <- (VPINSR_2u64 t128_0 r (W8.of_int 1));
    b_state <-
    (BArray224.set256d b_state 160
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <- (BArray224.set256 state 5 (BArray200.get256d st 128));
    r <- (BArray200.get64 st 20);
    t128_1 <- (VPINSR_2u64 t128_1 r (W8.of_int 1));
    b_state <-
    (BArray224.set256d b_state 64
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <-
    (BArray224.set256 state 2
    (W256.of_int
    (((W128.to_uint t128_1) %% (2 ^ 128)) +
    ((2 ^ 128) * (W128.to_uint t128_0)))));
    b_state <-
    (BArray224.set256d b_state 192
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <- (BArray224.set256 state 6 (BArray200.get256d st 168));
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 96 32))]);
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 160 32))]);
    t256_0 <-
    (VPBLEND_8u32 (BArray224.get256 state 3) (BArray224.get256 state 5)
    (W8.of_int 195));
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 192 32))]);
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 128 32))]);
    t256_1 <-
    (VPBLEND_8u32 (BArray224.get256 state 6) (BArray224.get256 state 4)
    (W8.of_int 195));
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 128 32))]);
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 96 32))]);
    t256_2 <-
    (VPBLEND_8u32 (BArray224.get256 state 4) (BArray224.get256 state 3)
    (W8.of_int 195));
    b_state <-
    (BArray224.set256d b_state 96
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <-
    (BArray224.set256 state 3 (VPBLEND_8u32 t256_0 t256_1 (W8.of_int 240)));
    b_state <-
    (BArray224.set256d b_state 128
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <-
    (BArray224.set256 state 4 (VPBLEND_8u32 t256_1 t256_0 (W8.of_int 240)));
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 160 32))]);
    trace___stavx2_pack <-
    (trace___stavx2_pack ++ [(Assert, (is_init b_state 192 32))]);
    t256_0 <-
    (VPBLEND_8u32 (BArray224.get256 state 5) (BArray224.get256 state 6)
    (W8.of_int 195));
    b_state <-
    (BArray224.set256d b_state 160
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <-
    (BArray224.set256 state 5 (VPBLEND_8u32 t256_0 t256_2 (W8.of_int 240)));
    b_state <-
    (BArray224.set256d b_state 192
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    state <-
    (BArray224.set256 state 6 (VPBLEND_8u32 t256_2 t256_0 (W8.of_int 240)));
    return (state, b_state, trace___stavx2_pack);
  }
  proc __stavx2_unpack (st:BArray200.t, b_st:BArray200.t, state:BArray224.t,
                        b_state:BArray224.t) : BArray200.t * BArray200.t *
                                               trace = {
    var t128_0:W128.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t128_1:W128.t;
    var t256_4:W256.t;
    var trace___stavx2_unpack:trace;
    trace___stavx2_unpack <- [];
    trace___stavx2_unpack <-
    (trace___stavx2_unpack ++ [(Assert, (is_init b_state 0 224))]);
    t128_0 <- (truncateu128 (BArray224.get256 state 0));
    b_st <- (BArray200.set64d b_st 0 (W64.of_int 18446744073709551615));
    st <- (BArray200.set64 st 0 (VMOVLPD t128_0));
    b_st <-
    (BArray200.set256d b_st 8
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray200.set256d st 8 (BArray224.get256 state 1));
    t256_0 <-
    (VPBLEND_8u32 (BArray224.get256 state 3) (BArray224.get256 state 4)
    (W8.of_int 240));
    t256_1 <-
    (VPBLEND_8u32 (BArray224.get256 state 4) (BArray224.get256 state 3)
    (W8.of_int 240));
    t256_2 <-
    (VPBLEND_8u32 (BArray224.get256 state 5) (BArray224.get256 state 6)
    (W8.of_int 240));
    t256_3 <-
    (VPBLEND_8u32 (BArray224.get256 state 6) (BArray224.get256 state 5)
    (W8.of_int 240));
    t128_1 <- (VEXTRACTI128 (BArray224.get256 state 2) (W8.of_int 1));
    b_st <- (BArray200.set64d b_st 40 (W64.of_int 18446744073709551615));
    st <- (BArray200.set64 st 5 (VMOVLPD t128_1));
    t256_4 <- (VPBLEND_8u32 t256_0 t256_3 (W8.of_int 195));
    b_st <-
    (BArray200.set256d b_st 48
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray200.set256d st 48 t256_4);
    t128_0 <- (truncateu128 (BArray224.get256 state 2));
    b_st <- (BArray200.set64d b_st 80 (W64.of_int 18446744073709551615));
    st <- (BArray200.set64 st 10 (VMOVLPD t128_0));
    t256_4 <- (VPBLEND_8u32 t256_3 t256_1 (W8.of_int 195));
    b_st <-
    (BArray200.set256d b_st 88
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray200.set256d st 88 t256_4);
    b_st <- (BArray200.set64d b_st 120 (W64.of_int 18446744073709551615));
    st <- (BArray200.set64 st 15 (VMOVHPD t128_1));
    t256_4 <- (VPBLEND_8u32 t256_2 t256_0 (W8.of_int 195));
    b_st <-
    (BArray200.set256d b_st 128
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray200.set256d st 128 t256_4);
    b_st <- (BArray200.set64d b_st 160 (W64.of_int 18446744073709551615));
    st <- (BArray200.set64 st 20 (VMOVHPD t128_0));
    t256_4 <- (VPBLEND_8u32 t256_1 t256_2 (W8.of_int 195));
    b_st <-
    (BArray200.set256d b_st 168
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray200.set256d st 168 t256_4);
    return (st, b_st, trace___stavx2_unpack);
  }

 proc keccakf1600_4x_theta_sum (a:BArray800.t, b_a:BArray800.t) : BArray160.t *
                                                                   BArray160.t *
                                                                   trace = {
    var c:BArray160.t;
    var x:int;
    var y:int;
    var b_c:BArray160.t;
    var trace_keccakf1600_4x_theta_sum:trace;
    b_c <- witness;
    c <- witness;
    trace_keccakf1600_4x_theta_sum <- [];
    trace_keccakf1600_4x_theta_sum <-
    (trace_keccakf1600_4x_theta_sum ++ [(Assert, (is_init b_a 0 800))]);
    b_c <- (BArray160.init_arr (W8.of_int 0) 160);
    x <- 0;
    while ((x < 5)) {
      trace_keccakf1600_4x_theta_sum <-
      (trace_keccakf1600_4x_theta_sum ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_theta_sum <-
      (trace_keccakf1600_4x_theta_sum ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 800)))]);
      b_c <-
      (BArray160.set256d b_c (x * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      c <- (BArray160.set256 c x (BArray800.get256 a x));
      x <- (x + 1);
    }
    y <- 1;
    while ((y < 5)) {
      x <- 0;
      while ((x < 5)) {
        trace_keccakf1600_4x_theta_sum <-
        (trace_keccakf1600_4x_theta_sum ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_theta_sum <-
        (trace_keccakf1600_4x_theta_sum ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_theta_sum <-
        (trace_keccakf1600_4x_theta_sum ++
        [(Assert, (is_init b_c (x * 32) 32))]);
        trace_keccakf1600_4x_theta_sum <-
        (trace_keccakf1600_4x_theta_sum ++
        [(Assert,
         ((0 <= ((x + (y * 5)) * 32)) /\
         ((((x + (y * 5)) * 32) + 32) <= 800)))]);
        b_c <-
        (BArray160.set256d b_c (x * 32)
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        c <-
        (BArray160.set256 c x
        ((BArray160.get256 c x) `^` (BArray800.get256 a (x + (y * 5)))));
        x <- (x + 1);
      }
      y <- (y + 1);
    }
    return (c, b_c, trace_keccakf1600_4x_theta_sum);
  }
  proc keccakf1600_4x_rol (a:BArray160.t, b_a:BArray160.t, x:int, r:int,
                           r8:W256.t, r56:W256.t) : BArray160.t *
                                                    BArray160.t * trace = {
    var t:W256.t;
    var trace_keccakf1600_4x_rol:trace;
    trace_keccakf1600_4x_rol <- [];
    trace_keccakf1600_4x_rol <-
    (trace_keccakf1600_4x_rol ++
    [(Assert, (((is_init b_a (x * 32) 32) /\ (0 <= x)) /\ (x < 5)))]);
    if ((r = 8)) {
      trace_keccakf1600_4x_rol <-
      (trace_keccakf1600_4x_rol ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_rol <-
      (trace_keccakf1600_4x_rol ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_rol <-
      (trace_keccakf1600_4x_rol ++ [(Assert, (is_init b_a (x * 32) 32))]);
      b_a <-
      (BArray160.set256d b_a (x * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      a <- (BArray160.set256 a x (VPSHUFB_256 (BArray160.get256 a x) r8));
    } else {
      if ((r = 56)) {
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++ [(Assert, (is_init b_a (x * 32) 32))]);
        b_a <-
        (BArray160.set256d b_a (x * 32)
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        a <- (BArray160.set256 a x (VPSHUFB_256 (BArray160.get256 a x) r56));
      } else {
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++ [(Assert, (is_init b_a (x * 32) 32))]);
        t <- (VPSLL_4u64 (BArray160.get256 a x) (W128.of_int r));
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++ [(Assert, (is_init b_a (x * 32) 32))]);
        b_a <-
        (BArray160.set256d b_a (x * 32)
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        a <-
        (BArray160.set256 a x
        (VPSRL_4u64 (BArray160.get256 a x) (W128.of_int (64 - r))));
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++
        [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
        trace_keccakf1600_4x_rol <-
        (trace_keccakf1600_4x_rol ++ [(Assert, (is_init b_a (x * 32) 32))]);
        b_a <-
        (BArray160.set256d b_a (x * 32)
        (W256.of_int
        115792089237316195423570985008687907853269984665640564039457584007913129639935
        ));
        a <- (BArray160.set256 a x ((BArray160.get256 a x) `|` t));
      }
    }
    return (a, b_a, trace_keccakf1600_4x_rol);
  }
  proc keccakf1600_4x_theta_rol (c:BArray160.t, b_c:BArray160.t, r8:W256.t,
                                 r56:W256.t) : BArray160.t * BArray160.t *
                                               trace = {
    var d:BArray160.t;
    var x:int;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:int;
    var param_2:int;
    var param_3:BArray160.t;
    var result:BArray160.t;
    var b_d:BArray160.t;
    var b_result:BArray160.t;
    var b_param:BArray160.t;
    var trace_keccakf1600_4x_theta_rol:trace;
    b_d <- witness;
    b_param <- witness;
    b_result <- witness;
    d <- witness;
    param_3 <- witness;
    result <- witness;
    trace_keccakf1600_4x_theta_rol <- [];
    trace_keccakf1600_4x_theta_rol <-
    (trace_keccakf1600_4x_theta_rol ++ [(Assert, (is_init b_c 0 160))]);
    b_d <- (BArray160.init_arr (W8.of_int 0) 160);
    x <- 0;
    while ((x < 5)) {
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++
      [(Assert,
       ((0 <= (((x + 1) %% 5) * 32)) /\
       (((((x + 1) %% 5) * 32) + 32) <= 160)))]);
      b_d <-
      (BArray160.set256d b_d (x * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      d <- (BArray160.set256 d x (BArray160.get256 c ((x + 1) %% 5)));
      b_param <- b_d;
      param_3 <- d;
      param_2 <- x;
      param_1 <- 1;
      param_0 <- r8;
      param <- r56;
      (result, b_result, tmp__trace) <@ keccakf1600_4x_rol (param_3, 
      b_param, param_2, param_1, param_0, param);
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++ tmp__trace);
      b_d <- b_result;
      d <- result;
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++
      [(Assert, (is_init b_d (x * 32) 32))]);
      trace_keccakf1600_4x_theta_rol <-
      (trace_keccakf1600_4x_theta_rol ++
      [(Assert,
       ((0 <= ((((x - 1) + 5) %% 5) * 32)) /\
       ((((((x - 1) + 5) %% 5) * 32) + 32) <= 160)))]);
      b_d <-
      (BArray160.set256d b_d (x * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      d <-
      (BArray160.set256 d x
      ((BArray160.get256 d x) `^` (BArray160.get256 c (((x - 1) + 5) %% 5))));
      x <- (x + 1);
    }
    return (d, b_d, trace_keccakf1600_4x_theta_rol);
  }
  proc keccakf1600_4x_rol_sum (a:BArray800.t, b_a:BArray800.t, d:BArray160.t,
                               b_d:BArray160.t, y:int, r8:W256.t, r56:W256.t) : 
  BArray160.t * BArray160.t * trace = {
    var b:BArray160.t;
    var x:int;
    var x_:int;
    var y_:int;
    var r:int;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:int;
    var param_2:int;
    var param_3:BArray160.t;
    var result:BArray160.t;
    var param_4:int;
    var param_5:int;
    var result_0:int;
    var b_b:BArray160.t;
    var b_result:BArray160.t;
    var b_param:BArray160.t;
    var trace_keccakf1600_4x_rol_sum:trace;
    b <- witness;
    b_b <- witness;
    b_param <- witness;
    b_result <- witness;
    param_3 <- witness;
    result <- witness;
    trace_keccakf1600_4x_rol_sum <- [];
    trace_keccakf1600_4x_rol_sum <-
    (trace_keccakf1600_4x_rol_sum ++
    [(Assert,
     ((((is_init b_a 0 800) /\ (is_init b_d 0 160)) /\ (0 <= y)) /\ (y < 5)))]);
    b_b <- (BArray160.init_arr (W8.of_int 0) 160);
    x <- 0;
    while ((x < 5)) {
      x_ <- ((x + (3 * y)) %% 5);
      y_ <- x;
      param_5 <- x_;
      param_4 <- y_;
      (result_0, tmp__trace) <@ keccakf1600_rhotates (param_5, param_4);
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++ tmp__trace);
      r <- result_0;
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++
      [(Assert,
       ((0 <= ((x_ + (y_ * 5)) * 32)) /\
       ((((x_ + (y_ * 5)) * 32) + 32) <= 800)))]);
      b_b <-
      (BArray160.set256d b_b (x * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      b <- (BArray160.set256 b x (BArray800.get256 a (x_ + (y_ * 5))));
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++ [(Assert, (is_init b_b (x * 32) 32))]);
      trace_keccakf1600_4x_rol_sum <-
      (trace_keccakf1600_4x_rol_sum ++
      [(Assert, ((0 <= (x_ * 32)) /\ (((x_ * 32) + 32) <= 160)))]);
      b_b <-
      (BArray160.set256d b_b (x * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      b <-
      (BArray160.set256 b x
      ((BArray160.get256 b x) `^` (BArray160.get256 d x_)));
      if ((r <> 0)) {
        b_param <- b_b;
        param_3 <- b;
        param_2 <- x;
        param_1 <- r;
        param_0 <- r8;
        param <- r56;
        (result, b_result, tmp__trace) <@ keccakf1600_4x_rol (param_3,
        b_param, param_2, param_1, param_0, param);
        trace_keccakf1600_4x_rol_sum <-
        (trace_keccakf1600_4x_rol_sum ++ tmp__trace);
        b_b <- b_result;
        b <- result;
      } else {
        
      }
      x <- (x + 1);
    }
    return (b, b_b, trace_keccakf1600_4x_rol_sum);
  }
  proc keccakf1600_4x_set_row (e:BArray800.t, b_e:BArray800.t, b:BArray160.t,
                               b_b:BArray160.t, y:int, rc:W256.t) : BArray800.t *
                                                                    BArray800.t *
                                                                    trace = {
    var x:int;
    var x1:int;
    var x2:int;
    var t:W256.t;
    var trace_keccakf1600_4x_set_row:trace;
    trace_keccakf1600_4x_set_row <- [];
    trace_keccakf1600_4x_set_row <-
    (trace_keccakf1600_4x_set_row ++
    [(Assert, (((is_init b_b 0 160) /\ (0 <= y)) /\ (y < 5)))]);
    x <- 0;
    while ((x < 5)) {
      x1 <- ((x + 1) %% 5);
      x2 <- ((x + 2) %% 5);
      trace_keccakf1600_4x_set_row <-
      (trace_keccakf1600_4x_set_row ++
      [(Assert, ((0 <= (x1 * 32)) /\ (((x1 * 32) + 32) <= 160)))]);
      trace_keccakf1600_4x_set_row <-
      (trace_keccakf1600_4x_set_row ++
      [(Assert, ((0 <= (x2 * 32)) /\ (((x2 * 32) + 32) <= 160)))]);
      t <- (VPANDN_256 (BArray160.get256 b x1) (BArray160.get256 b x2));
      trace_keccakf1600_4x_set_row <-
      (trace_keccakf1600_4x_set_row ++
      [(Assert, ((0 <= (x * 32)) /\ (((x * 32) + 32) <= 160)))]);
      t <- (t `^` (BArray160.get256 b x));
      if (((x = 0) /\ (y = 0))) {
        t <- (t `^` rc);
      } else {
        
      }
      trace_keccakf1600_4x_set_row <-
      (trace_keccakf1600_4x_set_row ++
      [(Assert,
       ((0 <= ((x + (y * 5)) * 32)) /\ ((((x + (y * 5)) * 32) + 32) <= 800)))]);
      b_e <-
      (BArray800.set256d b_e ((x + (y * 5)) * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      e <- (BArray800.set256 e (x + (y * 5)) t);
      x <- (x + 1);
    }
    return (e, b_e, trace_keccakf1600_4x_set_row);
  }
  proc _keccakf1600_4x_round (e:BArray800.t, b_e:BArray800.t, a:BArray800.t,
                              b_a:BArray800.t, rc:W256.t, r8:W256.t,
                              r56:W256.t) : BArray800.t * BArray800.t * trace = {
    var c:BArray160.t;
    var d:BArray160.t;
    var y:int;
    var b:BArray160.t;
    var param:W256.t;
    var param_0:int;
    var param_1:BArray160.t;
    var param_2:BArray800.t;
    var result:BArray800.t;
    var param_3:W256.t;
    var param_4:W256.t;
    var param_5:int;
    var param_6:BArray160.t;
    var param_7:BArray800.t;
    var result_0:BArray160.t;
    var param_8:W256.t;
    var param_9:W256.t;
    var param_10:BArray160.t;
    var result_1:BArray160.t;
    var param_11:BArray800.t;
    var result_2:BArray160.t;
    var b_result:BArray800.t;
    var b_param:BArray800.t;
    var b_result_0:BArray160.t;
    var b_result_1:BArray160.t;
    var b_result_2:BArray160.t;
    var trace__keccakf1600_4x_round:trace;
    b <- witness;
    b_param <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    c <- witness;
    d <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_6 <- witness;
    param_7 <- witness;
    param_10 <- witness;
    param_11 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_2 <- witness;
    trace__keccakf1600_4x_round <- [];
    trace__keccakf1600_4x_round <-
    (trace__keccakf1600_4x_round ++ [(Assert, (is_init b_a 0 800))]);
    param_11 <- a;
    (result_2, b_result_2, tmp__trace) <@ keccakf1600_4x_theta_sum (param_11,
    (BArray800.init_arr (W8.of_int 255) 800));
    trace__keccakf1600_4x_round <-
    (trace__keccakf1600_4x_round ++ tmp__trace);
    trace__keccakf1600_4x_round <-
    (trace__keccakf1600_4x_round ++ [(Assert, (is_init b_result_2 0 160))]);
    c <- result_2;
    param_10 <- c;
    param_9 <- r8;
    param_8 <- r56;
    (result_1, b_result_1, tmp__trace) <@ keccakf1600_4x_theta_rol (param_10,
    (BArray160.init_arr (W8.of_int 255) 160), param_9, param_8);
    trace__keccakf1600_4x_round <-
    (trace__keccakf1600_4x_round ++ tmp__trace);
    trace__keccakf1600_4x_round <-
    (trace__keccakf1600_4x_round ++ [(Assert, (is_init b_result_1 0 160))]);
    d <- result_1;
    y <- 0;
    while ((y < 5)) {
      param_7 <- a;
      param_6 <- d;
      param_5 <- y;
      param_4 <- r8;
      param_3 <- r56;
      (result_0, b_result_0, tmp__trace) <@ keccakf1600_4x_rol_sum (param_7,
      (BArray800.init_arr (W8.of_int 255) 800), param_6,
      (BArray160.init_arr (W8.of_int 255) 160), param_5, param_4, param_3);
      trace__keccakf1600_4x_round <-
      (trace__keccakf1600_4x_round ++ tmp__trace);
      trace__keccakf1600_4x_round <-
      (trace__keccakf1600_4x_round ++ [(Assert, (is_init b_result_0 0 160))]);
      b <- result_0;
      b_param <- b_e;
      param_2 <- e;
      param_1 <- b;
      param_0 <- y;
      param <- rc;
      (result, b_result, tmp__trace) <@ keccakf1600_4x_set_row (param_2,
      b_param, param_1, (BArray160.init_arr (W8.of_int 255) 160), param_0,
      param);
      trace__keccakf1600_4x_round <-
      (trace__keccakf1600_4x_round ++ tmp__trace);
      b_e <- b_result;
      e <- result;
      y <- (y + 1);
    }
    return (e, b_e, trace__keccakf1600_4x_round);
  }
  proc __keccakf1600_avx2x4 (a:BArray800.t, b_a:BArray800.t) : BArray800.t *
                                                               BArray800.t *
                                                               trace = {
    var rC:BArray192.t;
    var s_e:BArray800.t;
    var e:BArray800.t;
    var r8:W256.t;
    var r56:W256.t;
    var rc:W256.t;
    var c:int;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:W256.t;
    var param_2:BArray800.t;
    var param_3:BArray800.t;
    var result:BArray800.t;
    var param_4:W256.t;
    var param_5:W256.t;
    var param_6:W256.t;
    var param_7:BArray800.t;
    var param_8:BArray800.t;
    var result_0:BArray800.t;
    var b_e:BArray800.t;
    var b_result:BArray800.t;
    var b_param:BArray800.t;
    var b_param_0:BArray800.t;
    var b_result_0:BArray800.t;
    var b_param_1:BArray800.t;
    var b_s_e:BArray800.t;
    var trace___keccakf1600_avx2x4:trace;
    rC <- witness;
    b_e <- witness;
    b_param <- witness;
    b_param_0 <- witness;
    b_param_1 <- witness;
    b_result <- witness;
    b_result_0 <- witness;
    b_s_e <- witness;
    e <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_7 <- witness;
    param_8 <- witness;
    result <- witness;
    result_0 <- witness;
    s_e <- witness;
    trace___keccakf1600_avx2x4 <- [];
    trace___keccakf1600_avx2x4 <-
    (trace___keccakf1600_avx2x4 ++ [(Assert, (is_init b_a 0 800))]);
    b_s_e <- (BArray800.init_arr (W8.of_int 0) 800);
    rC <- kECCAK1600_RC;
    b_e <- b_s_e;
    e <- s_e;
    r8 <- rOL8;
    r56 <- rOL56;
    c <- 0;
    while ((c < 24)) {
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++
      [(Assert, ((0 <= (c * 8)) /\ (((c * 8) + 8) <= 192)))]);
      rc <- (VPBROADCAST_4u64 (BArray192.get64 rC c));
      b_param_1 <- b_e;
      param_8 <- e;
      param_7 <- a;
      param_6 <- rc;
      param_5 <- r8;
      param_4 <- r56;
      (result_0, b_result_0, tmp__trace) <@ _keccakf1600_4x_round (param_8,
      b_param_1, param_7, (BArray800.init_arr (W8.of_int 255) 800), param_6,
      param_5, param_4);
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++ tmp__trace);
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++ [(Assert, (is_init b_result_0 0 800))]);
      e <- result_0;
      (b_a, b_e) <-
      (swap_ (BArray800.init_arr (W8.of_int 255) 800)
      (BArray800.init_arr (W8.of_int 255) 800));
      (a, e) <- (swap_ e a);
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++
      [(Assert, ((0 <= ((c + 1) * 8)) /\ ((((c + 1) * 8) + 8) <= 192)))]);
      rc <- (VPBROADCAST_4u64 (BArray192.get64 rC (c + 1)));
      b_param_0 <- b_a;
      param_3 <- a;
      b_param <- b_e;
      param_2 <- e;
      param_1 <- rc;
      param_0 <- r8;
      param <- r56;
      (result, b_result, tmp__trace) <@ _keccakf1600_4x_round (param_3,
      b_param_0, param_2, b_param, param_1, param_0, param);
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++ tmp__trace);
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++ [(Assert, (is_init b_result 0 800))]);
      a <- result;
      (b_a, b_e) <- (swap_ b_e (BArray800.init_arr (W8.of_int 255) 800));
      (a, e) <- (swap_ e a);
      trace___keccakf1600_avx2x4 <-
      (trace___keccakf1600_avx2x4 ++
      [(Assert, ((0 <= (c + 2)) /\ ((c + 2) <= 18446744073709551615)))]);
      c <- (c + 2);
    }
    b_a <- (BArray800.init_arr (W8.of_int 255) 800);
    return (a, b_a, trace___keccakf1600_avx2x4);
  }
  proc _keccakf1600_avx2x4 (a:BArray800.t, b_a:BArray800.t) : BArray800.t *
                                                              BArray800.t *
                                                              trace = {
    var param:BArray800.t;
    var result:BArray800.t;
    var b_result:BArray800.t;
    var trace__keccakf1600_avx2x4:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace__keccakf1600_avx2x4 <- [];
    trace__keccakf1600_avx2x4 <-
    (trace__keccakf1600_avx2x4 ++ [(Assert, (is_init b_a 0 800))]);
    param <- a;
    (result, b_result, tmp__trace) <@ __keccakf1600_avx2x4 (param,
    (BArray800.init_arr (W8.of_int 255) 800));
    trace__keccakf1600_avx2x4 <- (trace__keccakf1600_avx2x4 ++ tmp__trace);
    trace__keccakf1600_avx2x4 <-
    (trace__keccakf1600_avx2x4 ++ [(Assert, (is_init b_result 0 800))]);
    a <- result;
    b_a <- (BArray800.init_arr (W8.of_int 255) 800);
    return (a, b_a, trace__keccakf1600_avx2x4);
  }
  proc _keccakf1600_avx2x4_ (a:BArray800.t, b_a:BArray800.t) : BArray800.t *
                                                               BArray800.t *
                                                               trace = {
    var param:BArray800.t;
    var result:BArray800.t;
    var b_result:BArray800.t;
    var trace__keccakf1600_avx2x4_:trace;
    b_result <- witness;
    param <- witness;
    result <- witness;
    trace__keccakf1600_avx2x4_ <- [];
    trace__keccakf1600_avx2x4_ <-
    (trace__keccakf1600_avx2x4_ ++ [(Assert, (is_init b_a 0 800))]);
    a <- a;
    param <- a;
    (result, b_result, tmp__trace) <@ _keccakf1600_avx2x4 (param,
    (BArray800.init_arr (W8.of_int 255) 800));
    trace__keccakf1600_avx2x4_ <- (trace__keccakf1600_avx2x4_ ++ tmp__trace);
    trace__keccakf1600_avx2x4_ <-
    (trace__keccakf1600_avx2x4_ ++ [(Assert, (is_init b_result 0 800))]);
    a <- result;
    a <- a;
    b_a <- (BArray800.init_arr (W8.of_int 255) 800);
    return (a, b_a, trace__keccakf1600_avx2x4_);
  }

  proc __mread_subu64 (buf:int, lEN:int, tRAIL:int) : int * int * int *
                                                      W64.t * trace = {
    var w:W64.t;
    var iLEN:int;
    var t16:W64.t;
    var t8:W64.t;
    var trace___mread_subu64:trace;
    trace___mread_subu64 <- [];
    trace___mread_subu64 <-
    (trace___mread_subu64 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (((is_valid ptr_modulus Glob.mem_v buf
       ((((lEN < 8) ? lEN : 8) < 0) ? 0 : ((lEN < 8) ? lEN : 8))) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256))))]);
    trace___mread_subu64 <-
    (trace___mread_subu64 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    iLEN <- lEN;
    if ((lEN <= 0)) {
      w <- (W64.of_int (tRAIL %% 256));
      tRAIL <- 0;
    } else {
      if ((8 <= lEN)) {
        trace___mread_subu64 <-
        (trace___mread_subu64 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mread_subu64 <-
        (trace___mread_subu64 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
        w <- (loadW64 Glob.mem buf);
        trace___mread_subu64 <-
        (trace___mread_subu64 ++
        [(Assert, ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
        buf <- (buf + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          trace___mread_subu64 <-
          (trace___mread_subu64 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mread_subu64 <-
          (trace___mread_subu64 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 4))]);
          w <- (zeroextu64 (loadW32 Glob.mem buf));
          trace___mread_subu64 <-
          (trace___mread_subu64 ++
          [(Assert,
           ((0 <= (buf + 4)) /\ ((buf + 4) <= 18446744073709551615)))]);
          buf <- (buf + 4);
          lEN <- (lEN - 4);
        } else {
          w <- (W64.of_int 0);
        }
        if ((2 <= lEN)) {
          trace___mread_subu64 <-
          (trace___mread_subu64 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mread_subu64 <-
          (trace___mread_subu64 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 2))]);
          t16 <- (zeroextu64 (loadW16 Glob.mem buf));
          trace___mread_subu64 <-
          (trace___mread_subu64 ++
          [(Assert,
           ((0 <= (buf + 2)) /\ ((buf + 2) <= 18446744073709551615)))]);
          buf <- (buf + 2);
          lEN <- (lEN - 2);
        } else {
          t16 <- (W64.of_int 0);
        }
        if (((1 <= lEN) \/ ((tRAIL %% 256) <> 0))) {
          if ((1 <= lEN)) {
            trace___mread_subu64 <-
            (trace___mread_subu64 ++
            [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
            trace___mread_subu64 <-
            (trace___mread_subu64 ++
            [(Assert, (is_valid ptr_modulus Glob.mem_v buf 1))]);
            t8 <- (zeroextu64 (loadW8 Glob.mem buf));
            if (((tRAIL %% 256) <> 0)) {
              t8 <- (t8 `|` (W64.of_int (256 * (tRAIL %% 256))));
            } else {
              
            }
            trace___mread_subu64 <-
            (trace___mread_subu64 ++
            [(Assert,
             ((0 <= (buf + 1)) /\ ((buf + 1) <= 18446744073709551615)))]);
            buf <- (buf + 1);
            lEN <- (lEN - 1);
          } else {
            t8 <- (W64.of_int (tRAIL %% 256));
          }
          tRAIL <- 0;
          t8 <- (t8 `<<` (W8.of_int (8 * (2 * ((iLEN %/ 2) %% 2)))));
          t16 <- (t16 `|` t8);
        } else {
          
        }
        t16 <- (t16 `<<` (W8.of_int (8 * (4 * ((iLEN %/ 4) %% 2)))));
        w <- (w `|` t16);
      }
    }
    return (buf, lEN, tRAIL, w, trace___mread_subu64);
  }
  proc __mread_bcast_4subu64 (buf:int, lEN:int, tRAIL:int) : int * int *
                                                             int * W256.t *
                                                             trace = {
    var w:W256.t;
    var t64:W64.t;
    var t128:W128.t;
    var param:int;
    var param_0:int;
    var param_1:int;
    var result:W64.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var trace___mread_bcast_4subu64:trace;
    trace___mread_bcast_4subu64 <- [];
    trace___mread_bcast_4subu64 <-
    (trace___mread_bcast_4subu64 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (((is_valid ptr_modulus Glob.mem_v buf
       ((((lEN < 8) ? lEN : 8) < 0) ? 0 : ((lEN < 8) ? lEN : 8))) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256))))]);
    trace___mread_bcast_4subu64 <-
    (trace___mread_bcast_4subu64 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((8 <= lEN)) {
        trace___mread_bcast_4subu64 <-
        (trace___mread_bcast_4subu64 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mread_bcast_4subu64 <-
        (trace___mread_bcast_4subu64 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
        w <- (VPBROADCAST_4u64 (loadW64 Glob.mem buf));
        trace___mread_bcast_4subu64 <-
        (trace___mread_bcast_4subu64 ++
        [(Assert, ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
        buf <- (buf + 8);
        lEN <- (lEN - 8);
      } else {
        param_1 <- buf;
        param_0 <- lEN;
        param <- tRAIL;
        (result_2, result_1, result_0, result, tmp__trace) <@ __mread_subu64 (
        param_1, param_0, param);
        trace___mread_bcast_4subu64 <-
        (trace___mread_bcast_4subu64 ++ tmp__trace);
        trace___mread_bcast_4subu64 <-
        (trace___mread_bcast_4subu64 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) /\
          (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_1 +
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
          ((param_1 +
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_2 =
           (param_1 +
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
          (result_1 =
          (param_0 -
          ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))) /\
         (result_0 = ((8 <= param_0) ? param : 0))))))]);
        trace___mread_bcast_4subu64 <-
        (trace___mread_bcast_4subu64 ++
        [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
        buf <- result_2;
        lEN <- result_1;
        tRAIL <- result_0;
        t64 <- result;
        t128 <- (zeroextu128 t64);
        w <- (VPBROADCAST_4u64 (truncateu64 t128));
      }
    }
    return (buf, lEN, tRAIL, w, trace___mread_bcast_4subu64);
  }
  proc __mread_subu128 (buf:int, lEN:int, tRAIL:int) : int * int * int *
                                                       W128.t * trace = {
    var w:W128.t;
    var t64:W64.t;
    var param:int;
    var param_0:int;
    var param_1:int;
    var result:W64.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var result_3:W64.t;
    var result_4:int;
    var result_5:int;
    var result_6:int;
    var trace___mread_subu128:trace;
    trace___mread_subu128 <- [];
    trace___mread_subu128 <-
    (trace___mread_subu128 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (((is_valid ptr_modulus Glob.mem_v buf
       ((((lEN < 16) ? lEN : 16) < 0) ? 0 : ((lEN < 16) ? lEN : 16))) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256))))]);
    trace___mread_subu128 <-
    (trace___mread_subu128 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_128);
    } else {
      if ((16 <= lEN)) {
        trace___mread_subu128 <-
        (trace___mread_subu128 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mread_subu128 <-
        (trace___mread_subu128 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 16))]);
        w <- (loadW128 Glob.mem buf);
        trace___mread_subu128 <-
        (trace___mread_subu128 ++
        [(Assert,
         ((0 <= (buf + 16)) /\ ((buf + 16) <= 18446744073709551615)))]);
        buf <- (buf + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
          w <- (VMOV_64 (loadW64 Glob.mem buf));
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert,
           ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
          buf <- (buf + 8);
          lEN <- (lEN - 8);
          param_1 <- buf;
          param_0 <- lEN;
          param <- tRAIL;
          (result_2, result_1, result_0, result, tmp__trace) <@ __mread_subu64 (
          param_1, param_0, param);
          trace___mread_subu128 <- (trace___mread_subu128 ++ tmp__trace);
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? 
                                                    param_0 : 8) : 0)) /\
            (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? 
                                                    param_0 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_1 +
             ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? 
                                                    param_0 : 8) : 0))) /\
            ((param_1 +
             ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? 
                                                    param_0 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_2 =
             (param_1 +
             ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? 
                                                    param_0 : 8) : 0))) /\
            (result_1 =
            (param_0 -
            ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))) /\
           (result_0 = ((8 <= param_0) ? param : 0))))))]);
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
          buf <- result_2;
          lEN <- result_1;
          tRAIL <- result_0;
          t64 <- result;
          w <- (VPINSR_2u64 w t64 (W8.of_int 1));
        } else {
          param_4 <- buf;
          param_3 <- lEN;
          param_2 <- tRAIL;
          (result_6, result_5, result_4, result_3, tmp__trace) <@ __mread_subu64 (
          param_4, param_3, param_2);
          trace___mread_subu128 <- (trace___mread_subu128 ++ tmp__trace);
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0)) /\
            (((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_4 +
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0))) /\
            ((param_4 +
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_6 =
             (param_4 +
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0))) /\
            (result_5 =
            (param_3 -
            ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)))) /\
           (result_4 = ((8 <= param_3) ? param_2 : 0))))))]);
          trace___mread_subu128 <-
          (trace___mread_subu128 ++
          [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
          buf <- result_6;
          lEN <- result_5;
          tRAIL <- result_4;
          t64 <- result_3;
          w <- (zeroextu128 t64);
        }
      }
    }
    return (buf, lEN, tRAIL, w, trace___mread_subu128);
  }
  proc __mread_subu256 (buf:int, lEN:int, tRAIL:int) : int * int * int *
                                                       W256.t * trace = {
    var w:W256.t;
    var t128_1:W128.t;
    var t128_0:W128.t;
    var param:int;
    var param_0:int;
    var param_1:int;
    var result:W128.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var result_3:W128.t;
    var result_4:int;
    var result_5:int;
    var result_6:int;
    var trace___mread_subu256:trace;
    trace___mread_subu256 <- [];
    trace___mread_subu256 <-
    (trace___mread_subu256 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (((is_valid ptr_modulus Glob.mem_v buf
       ((((lEN < 32) ? lEN : 32) < 0) ? 0 : ((lEN < 32) ? lEN : 32))) /\
      (0 <= tRAIL)) /\
     (tRAIL < 256))))]);
    trace___mread_subu256 <-
    (trace___mread_subu256 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if (((lEN <= 0) /\ ((tRAIL %% 256) = 0))) {
      w <- (set0_256);
    } else {
      if ((32 <= lEN)) {
        trace___mread_subu256 <-
        (trace___mread_subu256 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mread_subu256 <-
        (trace___mread_subu256 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 32))]);
        w <- (loadW256 Glob.mem buf);
        trace___mread_subu256 <-
        (trace___mread_subu256 ++
        [(Assert,
         ((0 <= (buf + 32)) /\ ((buf + 32) <= 18446744073709551615)))]);
        buf <- (buf + 32);
        lEN <- (lEN - 32);
      } else {
        if ((16 <= lEN)) {
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 16))]);
          t128_0 <- (loadW128 Glob.mem buf);
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert,
           ((0 <= (buf + 16)) /\ ((buf + 16) <= 18446744073709551615)))]);
          buf <- (buf + 16);
          lEN <- (lEN - 16);
          param_1 <- buf;
          param_0 <- lEN;
          param <- tRAIL;
          (result_2, result_1, result_0, result, tmp__trace) <@ __mread_subu128 (
          param_1, param_0, param);
          trace___mread_subu256 <- (trace___mread_subu256 ++ tmp__trace);
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                      param_0 : 16) : 0)) /\
            (((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                      param_0 : 16) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_1 +
             ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                      param_0 : 16) : 0))) /\
            ((param_1 +
             ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                      param_0 : 16) : 0)) <=
            18446744073709551615)) /\
           (((result_2 =
             (param_1 +
             ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                      param_0 : 16) : 0))) /\
            (result_1 =
            (param_0 -
            ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                     param_0 : 16) : 0)))) /\
           (result_0 = ((16 <= param_0) ? param : 0))))))]);
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
          buf <- result_2;
          lEN <- result_1;
          tRAIL <- result_0;
          t128_1 <- result;
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        } else {
          t128_1 <- (set0_128);
          param_4 <- buf;
          param_3 <- lEN;
          param_2 <- tRAIL;
          (result_6, result_5, result_4, result_3, tmp__trace) <@ __mread_subu128 (
          param_4, param_3, param_2);
          trace___mread_subu256 <- (trace___mread_subu256 ++ tmp__trace);
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_3 < 16) ? param_3 : 16)) ? ((param_3 < 16) ? 
                                                      param_3 : 16) : 0)) /\
            (((0 < ((param_3 < 16) ? param_3 : 16)) ? ((param_3 < 16) ? 
                                                      param_3 : 16) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_4 +
             ((0 < ((param_3 < 16) ? param_3 : 16)) ? ((param_3 < 16) ? 
                                                      param_3 : 16) : 0))) /\
            ((param_4 +
             ((0 < ((param_3 < 16) ? param_3 : 16)) ? ((param_3 < 16) ? 
                                                      param_3 : 16) : 0)) <=
            18446744073709551615)) /\
           (((result_6 =
             (param_4 +
             ((0 < ((param_3 < 16) ? param_3 : 16)) ? ((param_3 < 16) ? 
                                                      param_3 : 16) : 0))) /\
            (result_5 =
            (param_3 -
            ((0 < ((param_3 < 16) ? param_3 : 16)) ? ((param_3 < 16) ? 
                                                     param_3 : 16) : 0)))) /\
           (result_4 = ((16 <= param_3) ? param_2 : 0))))))]);
          trace___mread_subu256 <-
          (trace___mread_subu256 ++
          [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
          buf <- result_6;
          lEN <- result_5;
          tRAIL <- result_4;
          t128_0 <- result_3;
          w <-
          (W256.of_int
          (((W128.to_uint t128_0) %% (2 ^ 128)) +
          ((2 ^ 128) * (W128.to_uint t128_1))));
        }
      }
    }
    return (buf, lEN, tRAIL, w, trace___mread_subu256);
  }
  proc __mwrite_subu64 (buf:int, lEN:int, w:W64.t) : int * int * trace = {
    var trace___mwrite_subu64:trace;
    trace___mwrite_subu64 <- [];
    trace___mwrite_subu64 <-
    (trace___mwrite_subu64 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (is_valid ptr_modulus Glob.mem_v buf
     ((((lEN < 8) ? lEN : 8) < 0) ? 0 : ((lEN < 8) ? lEN : 8)))))]);
    trace___mwrite_subu64 <-
    (trace___mwrite_subu64 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if ((0 < lEN)) {
      if ((8 <= lEN)) {
        trace___mwrite_subu64 <-
        (trace___mwrite_subu64 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mwrite_subu64 <-
        (trace___mwrite_subu64 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
        Glob.mem <- (storeW64 Glob.mem buf w);
        trace___mwrite_subu64 <-
        (trace___mwrite_subu64 ++
        [(Assert, ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
        buf <- (buf + 8);
        lEN <- (lEN - 8);
      } else {
        if ((4 <= lEN)) {
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 4))]);
          Glob.mem <- (storeW32 Glob.mem buf (truncateu32 w));
          w <- (w `>>` (W8.of_int 32));
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert,
           ((0 <= (buf + 4)) /\ ((buf + 4) <= 18446744073709551615)))]);
          buf <- (buf + 4);
          lEN <- (lEN - 4);
        } else {
          
        }
        if ((2 <= lEN)) {
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 2))]);
          Glob.mem <- (storeW16 Glob.mem buf (truncateu16 w));
          w <- (w `>>` (W8.of_int 16));
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert,
           ((0 <= (buf + 2)) /\ ((buf + 2) <= 18446744073709551615)))]);
          buf <- (buf + 2);
          lEN <- (lEN - 2);
        } else {
          
        }
        if ((1 <= lEN)) {
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 1))]);
          Glob.mem <- (storeW8 Glob.mem buf (truncateu8 w));
          trace___mwrite_subu64 <-
          (trace___mwrite_subu64 ++
          [(Assert,
           ((0 <= (buf + 1)) /\ ((buf + 1) <= 18446744073709551615)))]);
          buf <- (buf + 1);
          lEN <- (lEN - 1);
        } else {
          
        }
      }
    } else {
      
    }
    return (buf, lEN, trace___mwrite_subu64);
  }
  proc __mwrite_subu128 (buf:int, lEN:int, w:W128.t) : int * int * trace = {
    var t64:W64.t;
    var param:W64.t;
    var param_0:int;
    var param_1:int;
    var result:int;
    var result_0:int;
    var trace___mwrite_subu128:trace;
    trace___mwrite_subu128 <- [];
    trace___mwrite_subu128 <-
    (trace___mwrite_subu128 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (is_valid ptr_modulus Glob.mem_v buf
     ((((lEN < 16) ? lEN : 16) < 0) ? 0 : ((lEN < 16) ? lEN : 16)))))]);
    trace___mwrite_subu128 <-
    (trace___mwrite_subu128 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if ((0 < lEN)) {
      if ((16 <= lEN)) {
        trace___mwrite_subu128 <-
        (trace___mwrite_subu128 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mwrite_subu128 <-
        (trace___mwrite_subu128 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 16))]);
        Glob.mem <- (storeW128 Glob.mem buf w);
        trace___mwrite_subu128 <-
        (trace___mwrite_subu128 ++
        [(Assert,
         ((0 <= (buf + 16)) /\ ((buf + 16) <= 18446744073709551615)))]);
        buf <- (buf + 16);
        lEN <- (lEN - 16);
      } else {
        if ((8 <= lEN)) {
          trace___mwrite_subu128 <-
          (trace___mwrite_subu128 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mwrite_subu128 <-
          (trace___mwrite_subu128 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
          Glob.mem <- (storeW64 Glob.mem buf (MOVV_64 (truncateu64 w)));
          trace___mwrite_subu128 <-
          (trace___mwrite_subu128 ++
          [(Assert,
           ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
          buf <- (buf + 8);
          lEN <- (lEN - 8);
          w <- (VPUNPCKH_2u64 w w);
        } else {
          
        }
        t64 <- (truncateu64 w);
        param_1 <- buf;
        param_0 <- lEN;
        param <- t64;
        (result_0, result, tmp__trace) <@ __mwrite_subu64 (param_1, param_0,
        param);
        trace___mwrite_subu128 <- (trace___mwrite_subu128 ++ tmp__trace);
        trace___mwrite_subu128 <-
        (trace___mwrite_subu128 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) /\
          (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_1 +
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
          ((param_1 +
           ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) <=
          18446744073709551615)) /\
         ((result_0 =
          (param_1 +
          ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
         (result =
         (param_0 -
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))))))]);
        trace___mwrite_subu128 <-
        (trace___mwrite_subu128 ++
        [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
        buf <- result_0;
        lEN <- result;
      }
    } else {
      
    }
    return (buf, lEN, trace___mwrite_subu128);
  }
  proc __mwrite_subu256 (buf:int, lEN:int, w:W256.t) : int * int * trace = {
    var t128:W128.t;
    var param:W128.t;
    var param_0:int;
    var param_1:int;
    var result:int;
    var result_0:int;
    var trace___mwrite_subu256:trace;
    trace___mwrite_subu256 <- [];
    trace___mwrite_subu256 <-
    (trace___mwrite_subu256 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (is_valid ptr_modulus Glob.mem_v buf
     ((((lEN < 32) ? lEN : 32) < 0) ? 0 : ((lEN < 32) ? lEN : 32)))))]);
    trace___mwrite_subu256 <-
    (trace___mwrite_subu256 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if ((0 < lEN)) {
      if ((32 <= lEN)) {
        trace___mwrite_subu256 <-
        (trace___mwrite_subu256 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___mwrite_subu256 <-
        (trace___mwrite_subu256 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 32))]);
        Glob.mem <- (storeW256 Glob.mem buf w);
        trace___mwrite_subu256 <-
        (trace___mwrite_subu256 ++
        [(Assert,
         ((0 <= (buf + 32)) /\ ((buf + 32) <= 18446744073709551615)))]);
        buf <- (buf + 32);
        lEN <- (lEN - 32);
      } else {
        t128 <- (truncateu128 w);
        if ((16 <= lEN)) {
          trace___mwrite_subu256 <-
          (trace___mwrite_subu256 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___mwrite_subu256 <-
          (trace___mwrite_subu256 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 16))]);
          Glob.mem <- (storeW128 Glob.mem buf t128);
          trace___mwrite_subu256 <-
          (trace___mwrite_subu256 ++
          [(Assert,
           ((0 <= (buf + 16)) /\ ((buf + 16) <= 18446744073709551615)))]);
          buf <- (buf + 16);
          lEN <- (lEN - 16);
          t128 <- (VEXTRACTI128 w (W8.of_int 1));
        } else {
          
        }
        param_1 <- buf;
        param_0 <- lEN;
        param <- t128;
        (result_0, result, tmp__trace) <@ __mwrite_subu128 (param_1, 
        param_0, param);
        trace___mwrite_subu256 <- (trace___mwrite_subu256 ++ tmp__trace);
        trace___mwrite_subu256 <-
        (trace___mwrite_subu256 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                    param_0 : 16) : 0)) /\
          (((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                    param_0 : 16) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_1 +
           ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                    param_0 : 16) : 0))) /\
          ((param_1 +
           ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                    param_0 : 16) : 0)) <=
          18446744073709551615)) /\
         ((result_0 =
          (param_1 +
          ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? 
                                                   param_0 : 16) : 0))) /\
         (result =
         (param_0 -
         ((0 < ((param_0 < 16) ? param_0 : 16)) ? ((param_0 < 16) ? param_0 : 16) : 0)))))))]);
        trace___mwrite_subu256 <-
        (trace___mwrite_subu256 ++
        [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
        buf <- result_0;
        lEN <- result;
      }
    } else {
      
    }
    return (buf, lEN, trace___mwrite_subu256);
  }
  proc __u64_to_u256 (x:W64.t, l:int) : W256.t * trace = {
    var t256:W256.t;
    var t128:W128.t;
    var trace___u64_to_u256:trace;
    trace___u64_to_u256 <- [];
    if (((l %% 2) = 0)) {
      t128 <- (zeroextu128 x);
    } else {
      t128 <- (set0_128);
      t128 <- (VPINSR_2u64 t128 x (W8.of_int 1));
    }
    t256 <- (set0_256);
    if (((l %/ 2) = 0)) {
      t256 <- (VINSERTI128 t256 t128 (W8.of_int 0));
    } else {
      t256 <- (VINSERTI128 t256 t128 (W8.of_int 1));
    }
    return (t256, trace___u64_to_u256);
  }
  proc __state_init_avx2 () : BArray224.t * BArray224.t * trace = {
    var st:BArray224.t;
    var i:int;
    var b_st:BArray224.t;
    var trace___state_init_avx2:trace;
    b_st <- witness;
    st <- witness;
    trace___state_init_avx2 <- [];
    b_st <- (BArray224.init_arr (W8.of_int 0) 224);
    i <- 0;
    while ((i < 7)) {
      trace___state_init_avx2 <-
      (trace___state_init_avx2 ++
      [(Assert, ((0 <= (i * 32)) /\ (((i * 32) + 32) <= 224)))]);
      b_st <-
      (BArray224.set256d b_st (i * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      st <- (BArray224.set256 st i (set0_256));
      i <- (i + 1);
    }
    return (st, b_st, trace___state_init_avx2);
  }
  proc __pstate_init_avx2 (pst:BArray200.t, b_pst:BArray200.t) : BArray200.t *
                                                                 BArray200.t *
                                                                 BArray224.t *
                                                                 BArray224.t *
                                                                 trace = {
    var st:BArray224.t;
    var z256:W256.t;
    var i:int;
    var z64:W64.t;
    var result:BArray224.t;
    var b_st:BArray224.t;
    var b_result:BArray224.t;
    var trace___pstate_init_avx2:trace;
    b_result <- witness;
    b_st <- witness;
    result <- witness;
    st <- witness;
    trace___pstate_init_avx2 <- [];
    z256 <- (set0_256);
    i <- 0;
    while ((i < 6)) {
      trace___pstate_init_avx2 <-
      (trace___pstate_init_avx2 ++
      [(Assert, ((0 <= (i * 32)) /\ (((i * 32) + 32) <= 200)))]);
      b_pst <-
      (BArray200.set256d b_pst (i * 32)
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      pst <- (BArray200.set256 pst i z256);
      i <- (i + 1);
    }
    z64 <- (W64.of_int 0);
    b_pst <- (BArray200.set64d b_pst 192 (W64.of_int 18446744073709551615));
    pst <- (BArray200.set64 pst 24 z64);
    (result, b_result, tmp__trace) <@ __state_init_avx2 ();
    trace___pstate_init_avx2 <- (trace___pstate_init_avx2 ++ tmp__trace);
    trace___pstate_init_avx2 <-
    (trace___pstate_init_avx2 ++ [(Assert, (is_init b_result 0 224))]);
    st <- result;
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (pst, b_pst, st, b_st, trace___pstate_init_avx2);
  }
  proc __perm_reg3456_avx2 (r3:W256.t, r4:W256.t, r5:W256.t, r6:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * trace = {
    var st3:W256.t;
    var st4:W256.t;
    var st5:W256.t;
    var st6:W256.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var trace___perm_reg3456_avx2:trace;
    trace___perm_reg3456_avx2 <- [];
    t256_0 <- (VPBLEND_8u32 r3 r5 (W8.of_int 195));
    t256_1 <- (VPBLEND_8u32 r6 r4 (W8.of_int 195));
    t256_2 <- (VPBLEND_8u32 r4 r3 (W8.of_int 195));
    st3 <- (VPBLEND_8u32 t256_0 t256_1 (W8.of_int 240));
    st4 <- (VPBLEND_8u32 t256_1 t256_0 (W8.of_int 240));
    t256_0 <- (VPBLEND_8u32 r5 r6 (W8.of_int 195));
    st5 <- (VPBLEND_8u32 t256_0 t256_2 (W8.of_int 240));
    st6 <- (VPBLEND_8u32 t256_2 t256_0 (W8.of_int 240));
    return (st3, st4, st5, st6, trace___perm_reg3456_avx2);
  }
  proc __unperm_reg3456_avx2 (st3:W256.t, st4:W256.t, st5:W256.t, st6:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * trace = {
    var r3:W256.t;
    var r4:W256.t;
    var r5:W256.t;
    var r6:W256.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var trace___unperm_reg3456_avx2:trace;
    trace___unperm_reg3456_avx2 <- [];
    t256_0 <- (VPBLEND_8u32 st3 st4 (W8.of_int 240));
    t256_1 <- (VPBLEND_8u32 st4 st3 (W8.of_int 240));
    t256_2 <- (VPBLEND_8u32 st5 st6 (W8.of_int 240));
    t256_3 <- (VPBLEND_8u32 st6 st5 (W8.of_int 240));
    r3 <- (VPBLEND_8u32 t256_0 t256_3 (W8.of_int 195));
    r4 <- (VPBLEND_8u32 t256_3 t256_1 (W8.of_int 195));
    r5 <- (VPBLEND_8u32 t256_2 t256_0 (W8.of_int 195));
    r6 <- (VPBLEND_8u32 t256_1 t256_2 (W8.of_int 195));
    return (r3, r4, r5, r6, trace___unperm_reg3456_avx2);
  }
  proc __state_from_pstate_avx2 (pst:BArray200.t, b_pst:BArray200.t) : 
  BArray224.t * BArray224.t * trace = {
    var st:BArray224.t;
    var t128_0:W128.t;
    var t128_1:W128.t;
    var t:W64.t;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:W256.t;
    var param_2:W256.t;
    var result:W256.t;
    var result_0:W256.t;
    var result_1:W256.t;
    var result_2:W256.t;
    var b_st:BArray224.t;
    var trace___state_from_pstate_avx2:trace;
    b_st <- witness;
    st <- witness;
    trace___state_from_pstate_avx2 <- [];
    trace___state_from_pstate_avx2 <-
    (trace___state_from_pstate_avx2 ++ [(Assert, (is_init b_pst 0 200))]);
    b_st <- (BArray224.init_arr (W8.of_int 0) 224);
    b_st <-
    (BArray224.set256d b_st 0
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <-
    (BArray224.set256 st 0 (VPBROADCAST_4u64 (BArray200.get64d pst 0)));
    b_st <-
    (BArray224.set256d b_st 32
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 1 (BArray200.get256d pst 8));
    t128_0 <- (VMOV_64 (BArray200.get64d pst 40));
    b_st <-
    (BArray224.set256d b_st 96
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 3 (BArray200.get256d pst 48));
    t128_1 <- (VMOV_64 (BArray200.get64d pst 80));
    b_st <-
    (BArray224.set256d b_st 128
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 4 (BArray200.get256d pst 88));
    t <- (BArray200.get64d pst 120);
    t128_0 <- (VPINSR_2u64 t128_0 t (W8.of_int 1));
    b_st <-
    (BArray224.set256d b_st 160
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 5 (BArray200.get256d pst 128));
    t <- (BArray200.get64d pst 160);
    t128_1 <- (VPINSR_2u64 t128_1 t (W8.of_int 1));
    b_st <-
    (BArray224.set256d b_st 64
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <-
    (BArray224.set256 st 2
    (W256.of_int
    (((W128.to_uint t128_1) %% (2 ^ 128)) +
    ((2 ^ 128) * (W128.to_uint t128_0)))));
    b_st <-
    (BArray224.set256d b_st 192
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 6 (BArray200.get256d pst 168));
    trace___state_from_pstate_avx2 <-
    (trace___state_from_pstate_avx2 ++ [(Assert, (is_init b_st 96 32))]);
    trace___state_from_pstate_avx2 <-
    (trace___state_from_pstate_avx2 ++ [(Assert, (is_init b_st 128 32))]);
    trace___state_from_pstate_avx2 <-
    (trace___state_from_pstate_avx2 ++ [(Assert, (is_init b_st 160 32))]);
    trace___state_from_pstate_avx2 <-
    (trace___state_from_pstate_avx2 ++ [(Assert, (is_init b_st 192 32))]);
    param_2 <- (BArray224.get256 st 3);
    param_1 <- (BArray224.get256 st 4);
    param_0 <- (BArray224.get256 st 5);
    param <- (BArray224.get256 st 6);
    (result_2, result_1, result_0, result, tmp__trace) <@ __perm_reg3456_avx2 (
    param_2, param_1, param_0, param);
    trace___state_from_pstate_avx2 <-
    (trace___state_from_pstate_avx2 ++ tmp__trace);
    b_st <-
    (BArray224.set256d b_st 96
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 3 result_2);
    b_st <-
    (BArray224.set256d b_st 128
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 4 result_1);
    b_st <-
    (BArray224.set256d b_st 160
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 5 result_0);
    b_st <-
    (BArray224.set256d b_st 192
    (W256.of_int
    115792089237316195423570985008687907853269984665640564039457584007913129639935
    ));
    st <- (BArray224.set256 st 6 result);
    return (st, b_st, trace___state_from_pstate_avx2);
  }
  proc __addstate_r3456_avx2 (st:BArray224.t, b_st:BArray224.t, r3:W256.t,
                              r4:W256.t, r5:W256.t, r6:W256.t) : BArray224.t *
                                                                 BArray224.t *
                                                                 trace = {
    var param:W256.t;
    var param_0:W256.t;
    var param_1:W256.t;
    var param_2:W256.t;
    var result:W256.t;
    var result_0:W256.t;
    var result_1:W256.t;
    var result_2:W256.t;
    var trace___addstate_r3456_avx2:trace;
    trace___addstate_r3456_avx2 <- [];
    trace___addstate_r3456_avx2 <-
    (trace___addstate_r3456_avx2 ++ [(Assert, (is_init b_st 0 224))]);
    param_2 <- r3;
    param_1 <- r4;
    param_0 <- r5;
    param <- r6;
    (result_2, result_1, result_0, result, tmp__trace) <@ __perm_reg3456_avx2 (
    param_2, param_1, param_0, param);
    trace___addstate_r3456_avx2 <-
    (trace___addstate_r3456_avx2 ++ tmp__trace);
    r3 <- result_2;
    r4 <- result_1;
    r5 <- result_0;
    r6 <- result;
    st <- (BArray224.set256 st 3 ((BArray224.get256 st 3) `^` r3));
    st <- (BArray224.set256 st 4 ((BArray224.get256 st 4) `^` r4));
    st <- (BArray224.set256 st 5 ((BArray224.get256 st 5) `^` r5));
    st <- (BArray224.set256 st 6 ((BArray224.get256 st 6) `^` r6));
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, trace___addstate_r3456_avx2);
  }
  proc __addpst01_avx2 (st:BArray224.t, b_st:BArray224.t, pst:BArray200.t,
                        b_pst:BArray200.t) : BArray224.t * BArray224.t *
                                             trace = {
    var t256:W256.t;
    var trace___addpst01_avx2:trace;
    trace___addpst01_avx2 <- [];
    trace___addpst01_avx2 <-
    (trace___addpst01_avx2 ++ [(Assert, (is_init b_st 0 224))]);
    trace___addpst01_avx2 <-
    (trace___addpst01_avx2 ++ [(Assert, (is_init b_pst 0 200))]);
    t256 <- (VPBROADCAST_4u64 (BArray200.get64d pst 0));
    st <- (BArray224.set256 st 0 ((BArray224.get256 st 0) `^` t256));
    t256 <- (BArray200.get256d pst 8);
    st <- (BArray224.set256 st 1 ((BArray224.get256 st 1) `^` t256));
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, trace___addpst01_avx2);
  }
  proc __addpst23456_avx2 (st:BArray224.t, b_st:BArray224.t, pst:BArray200.t,
                           b_pst:BArray200.t) : BArray224.t * BArray224.t *
                                                trace = {
    var t128_0:W128.t;
    var r3:W256.t;
    var t128_1:W128.t;
    var r4:W256.t;
    var t:W64.t;
    var r5:W256.t;
    var r2:W256.t;
    var r6:W256.t;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:W256.t;
    var param_2:W256.t;
    var param_3:BArray224.t;
    var result:BArray224.t;
    var b_result:BArray224.t;
    var trace___addpst23456_avx2:trace;
    b_result <- witness;
    param_3 <- witness;
    result <- witness;
    trace___addpst23456_avx2 <- [];
    trace___addpst23456_avx2 <-
    (trace___addpst23456_avx2 ++ [(Assert, (is_init b_st 0 224))]);
    trace___addpst23456_avx2 <-
    (trace___addpst23456_avx2 ++ [(Assert, (is_init b_pst 0 200))]);
    t128_0 <- (VMOV_64 (BArray200.get64d pst 40));
    r3 <- (BArray200.get256d pst 48);
    t128_1 <- (VMOV_64 (BArray200.get64d pst 80));
    r4 <- (BArray200.get256d pst 88);
    t <- (BArray200.get64d pst 120);
    t128_0 <- (VPINSR_2u64 t128_0 t (W8.of_int 1));
    r5 <- (BArray200.get256d pst 128);
    t <- (BArray200.get64d pst 160);
    t128_1 <- (VPINSR_2u64 t128_1 t (W8.of_int 1));
    r2 <-
    (W256.of_int
    (((W128.to_uint t128_1) %% (2 ^ 128)) +
    ((2 ^ 128) * (W128.to_uint t128_0))));
    st <- (BArray224.set256 st 2 ((BArray224.get256 st 2) `^` r2));
    r6 <- (BArray200.get256d pst 168);
    param_3 <- st;
    param_2 <- r3;
    param_1 <- r4;
    param_0 <- r5;
    param <- r6;
    (result, b_result, tmp__trace) <@ __addstate_r3456_avx2 (param_3,
    (BArray224.init_arr (W8.of_int 255) 224), param_2, param_1, param_0,
    param);
    trace___addpst23456_avx2 <- (trace___addpst23456_avx2 ++ tmp__trace);
    trace___addpst23456_avx2 <-
    (trace___addpst23456_avx2 ++ [(Assert, (is_init b_result 0 224))]);
    st <- result;
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, trace___addpst23456_avx2);
  }
  proc _addpstate_avx2 (st:BArray224.t, b_st:BArray224.t, pst:BArray200.t,
                        b_pst:BArray200.t) : BArray224.t * BArray224.t *
                                             trace = {
    var param:BArray200.t;
    var param_0:BArray224.t;
    var result:BArray224.t;
    var param_1:BArray200.t;
    var param_2:BArray224.t;
    var result_0:BArray224.t;
    var b_result:BArray224.t;
    var b_result_0:BArray224.t;
    var trace__addpstate_avx2:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    result <- witness;
    result_0 <- witness;
    trace__addpstate_avx2 <- [];
    trace__addpstate_avx2 <-
    (trace__addpstate_avx2 ++ [(Assert, (is_init b_st 0 224))]);
    trace__addpstate_avx2 <-
    (trace__addpstate_avx2 ++ [(Assert, (is_init b_pst 0 200))]);
    param_2 <- st;
    param_1 <- pst;
    (result_0, b_result_0, tmp__trace) <@ __addpst01_avx2 (param_2,
    (BArray224.init_arr (W8.of_int 255) 224), param_1,
    (BArray200.init_arr (W8.of_int 255) 200));
    trace__addpstate_avx2 <- (trace__addpstate_avx2 ++ tmp__trace);
    trace__addpstate_avx2 <-
    (trace__addpstate_avx2 ++ [(Assert, (is_init b_result_0 0 224))]);
    st <- result_0;
    param_0 <- st;
    param <- pst;
    (result, b_result, tmp__trace) <@ __addpst23456_avx2 (param_0,
    (BArray224.init_arr (W8.of_int 255) 224), param,
    (BArray200.init_arr (W8.of_int 255) 200));
    trace__addpstate_avx2 <- (trace__addpstate_avx2 ++ tmp__trace);
    trace__addpstate_avx2 <-
    (trace__addpstate_avx2 ++ [(Assert, (is_init b_result 0 224))]);
    st <- result;
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, trace__addpstate_avx2);
  }
  proc __stavx2_pos_avx2 (pOS:int) : int * int * trace = {
    var r:int;
    var l:int;
    var trace___stavx2_pos_avx2:trace;
    trace___stavx2_pos_avx2 <- [];
    r <- 0;
    l <- 0;
    if ((0 < pOS)) {
      if ((pOS <= 4)) {
        r <- 1;
        l <- (pOS - 1);
      } else {
        if ((pOS = 10)) {
          r <- 2;
          l <- 0;
        } else {
          if ((pOS = 20)) {
            r <- 2;
            l <- 1;
          } else {
            if ((pOS = 5)) {
              r <- 2;
              l <- 2;
            } else {
              if ((pOS = 15)) {
                r <- 2;
                l <- 3;
              } else {
                if ((pOS = 16)) {
                  r <- 3;
                  l <- 0;
                } else {
                  if ((pOS = 7)) {
                    r <- 3;
                    l <- 1;
                  } else {
                    if ((pOS = 23)) {
                      r <- 3;
                      l <- 2;
                    } else {
                      if ((pOS = 14)) {
                        r <- 3;
                        l <- 3;
                      } else {
                        if ((pOS = 11)) {
                          r <- 4;
                          l <- 0;
                        } else {
                          if ((pOS = 22)) {
                            r <- 4;
                            l <- 1;
                          } else {
                            if ((pOS = 8)) {
                              r <- 4;
                              l <- 2;
                            } else {
                              if ((pOS = 19)) {
                                r <- 4;
                                l <- 3;
                              } else {
                                if ((pOS = 21)) {
                                  r <- 5;
                                  l <- 0;
                                } else {
                                  if ((pOS = 17)) {
                                    r <- 5;
                                    l <- 1;
                                  } else {
                                    if ((pOS = 13)) {
                                      r <- 5;
                                      l <- 2;
                                    } else {
                                      if ((pOS = 9)) {
                                        r <- 5;
                                        l <- 3;
                                      } else {
                                        if ((pOS = 6)) {
                                          r <- 6;
                                          l <- 0;
                                        } else {
                                          if ((pOS = 12)) {
                                            r <- 6;
                                            l <- 1;
                                          } else {
                                            if ((pOS = 18)) {
                                              r <- 6;
                                              l <- 2;
                                            } else {
                                              if ((pOS = 24)) {
                                                r <- 6;
                                                l <- 3;
                                              } else {
                                                
                                              }
                                            }
                                          }
                                        }
                                      }
                                    }
                                  }
                                }
                              }
                            }
                          }
                        }
                      }
                    }
                  }
                }
              }
            }
          }
        }
      }
    } else {
      
    }
    return (r, l, trace___stavx2_pos_avx2);
  }
  proc __addratebit_avx2 (st:BArray224.t, b_st:BArray224.t, rATE8:int) : 
  BArray224.t * BArray224.t * trace = {
    var t64:W64.t;
    var r:int;
    var l:int;
    var t256:W256.t;
    var param:int;
    var param_0:W64.t;
    var result:W256.t;
    var param_1:int;
    var result_0:int;
    var result_1:int;
    var trace___addratebit_avx2:trace;
    trace___addratebit_avx2 <- [];
    trace___addratebit_avx2 <-
    (trace___addratebit_avx2 ++ [(Assert, (is_init b_st 0 224))]);
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE8) - 1) %% 64)));
    param_1 <- ((rATE8 - 1) %/ 8);
    (result_1, result_0, tmp__trace) <@ __stavx2_pos_avx2 (param_1);
    trace___addratebit_avx2 <- (trace___addratebit_avx2 ++ tmp__trace);
    trace___addratebit_avx2 <-
    (trace___addratebit_avx2 ++
    [(Assert, ((0 <= result_1) /\ (result_1 < 7)))]);
    r <- result_1;
    l <- result_0;
    if ((r = 0)) {
      t256 <- (VPBROADCAST_4u64 t64);
    } else {
      param_0 <- t64;
      param <- l;
      (result, tmp__trace) <@ __u64_to_u256 (param_0, param);
      trace___addratebit_avx2 <- (trace___addratebit_avx2 ++ tmp__trace);
      t256 <- result;
    }
    trace___addratebit_avx2 <-
    (trace___addratebit_avx2 ++
    [(Assert, ((0 <= (r * 32)) /\ (((r * 32) + 32) <= 224)))]);
    trace___addratebit_avx2 <-
    (trace___addratebit_avx2 ++
    [(Assert, ((0 <= (r * 32)) /\ (((r * 32) + 32) <= 224)))]);
    st <- (BArray224.set256 st r ((BArray224.get256 st r) `^` t256));
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, trace___addratebit_avx2);
  }
  proc __addstate_imem_avx2 (st:BArray224.t, b_st:BArray224.t, buf:int,
                             lEN:int, tRAILB:int) : BArray224.t *
                                                    BArray224.t * int * trace = {
    var r0:W256.t;
    var r1:W256.t;
    var t64:W64.t;
    var t128_1:W128.t;
    var r3:W256.t;
    var t128_0:W128.t;
    var r4:W256.t;
    var r5:W256.t;
    var r2:W256.t;
    var r6:W256.t;
    var param:W256.t;
    var param_0:W256.t;
    var param_1:W256.t;
    var param_2:W256.t;
    var param_3:BArray224.t;
    var result:BArray224.t;
    var param_4:int;
    var param_5:int;
    var param_6:int;
    var result_0:W256.t;
    var result_1:int;
    var result_2:int;
    var result_3:int;
    var param_7:int;
    var param_8:int;
    var param_9:int;
    var result_4:W64.t;
    var result_5:int;
    var result_6:int;
    var result_7:int;
    var param_10:int;
    var param_11:int;
    var param_12:int;
    var result_8:W256.t;
    var result_9:int;
    var result_10:int;
    var result_11:int;
    var param_13:int;
    var param_14:int;
    var param_15:int;
    var result_12:W64.t;
    var result_13:int;
    var result_14:int;
    var result_15:int;
    var param_16:int;
    var param_17:int;
    var param_18:int;
    var result_16:W256.t;
    var result_17:int;
    var result_18:int;
    var result_19:int;
    var param_19:int;
    var param_20:int;
    var param_21:int;
    var result_20:W64.t;
    var result_21:int;
    var result_22:int;
    var result_23:int;
    var param_22:int;
    var param_23:int;
    var param_24:int;
    var result_24:W256.t;
    var result_25:int;
    var result_26:int;
    var result_27:int;
    var param_25:int;
    var param_26:int;
    var param_27:int;
    var result_28:W64.t;
    var result_29:int;
    var result_30:int;
    var result_31:int;
    var param_28:int;
    var param_29:int;
    var param_30:int;
    var result_32:W256.t;
    var result_33:int;
    var result_34:int;
    var result_35:int;
    var param_31:int;
    var param_32:int;
    var param_33:int;
    var result_36:W256.t;
    var result_37:int;
    var result_38:int;
    var result_39:int;
    var b_result:BArray224.t;
    var trace___addstate_imem_avx2:trace;
    b_result <- witness;
    param_3 <- witness;
    result <- witness;
    trace___addstate_imem_avx2 <- [];
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     ((((0 <= lEN) /\ (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
      (is_init b_st 0 224)) /\
     (lEN <= 200))))]);
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    param_33 <- buf;
    param_32 <- lEN;
    param_31 <- tRAILB;
    (result_39, result_38, result_37, result_36, tmp__trace) <@ __mread_bcast_4subu64 (
    param_33, param_32, param_31);
    trace___addstate_imem_avx2 <- (trace___addstate_imem_avx2 ++ tmp__trace);
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert,
     (((0 <=
       ((0 < ((param_32 < 8) ? param_32 : 8)) ? ((param_32 < 8) ? param_32 : 8) : 0)) /\
      (((0 < ((param_32 < 8) ? param_32 : 8)) ? ((param_32 < 8) ? param_32 : 8) : 0) <=
      18446744073709551615)) /\
     (((0 <=
       (param_33 +
       ((0 < ((param_32 < 8) ? param_32 : 8)) ? ((param_32 < 8) ? param_32 : 8) : 0))) /\
      ((param_33 +
       ((0 < ((param_32 < 8) ? param_32 : 8)) ? ((param_32 < 8) ? param_32 : 8) : 0)) <=
      18446744073709551615)) /\
     (((result_39 =
       (param_33 +
       ((0 < ((param_32 < 8) ? param_32 : 8)) ? ((param_32 < 8) ? param_32 : 8) : 0))) /\
      (result_38 =
      (param_32 -
      ((0 < ((param_32 < 8) ? param_32 : 8)) ? ((param_32 < 8) ? param_32 : 8) : 0)))) /\
     (result_37 = ((8 <= param_32) ? param_31 : 0))))))]);
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert, ((0 <= result_39) /\ (result_39 <= 18446744073709551615)))]);
    buf <- result_39;
    lEN <- result_38;
    tRAILB <- result_37;
    r0 <- result_36;
    st <- (BArray224.set256 st 0 ((BArray224.get256 st 0) `^` r0));
    param_30 <- buf;
    param_29 <- lEN;
    param_28 <- tRAILB;
    (result_35, result_34, result_33, result_32, tmp__trace) <@ __mread_subu256 (
    param_30, param_29, param_28);
    trace___addstate_imem_avx2 <- (trace___addstate_imem_avx2 ++ tmp__trace);
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert,
     (((0 <=
       ((0 < ((param_29 < 32) ? param_29 : 32)) ? ((param_29 < 32) ? 
                                                  param_29 : 32) : 0)) /\
      (((0 < ((param_29 < 32) ? param_29 : 32)) ? ((param_29 < 32) ? 
                                                  param_29 : 32) : 0) <=
      18446744073709551615)) /\
     (((0 <=
       (param_30 +
       ((0 < ((param_29 < 32) ? param_29 : 32)) ? ((param_29 < 32) ? 
                                                  param_29 : 32) : 0))) /\
      ((param_30 +
       ((0 < ((param_29 < 32) ? param_29 : 32)) ? ((param_29 < 32) ? 
                                                  param_29 : 32) : 0)) <=
      18446744073709551615)) /\
     (((result_35 =
       (param_30 +
       ((0 < ((param_29 < 32) ? param_29 : 32)) ? ((param_29 < 32) ? 
                                                  param_29 : 32) : 0))) /\
      (result_34 =
      (param_29 -
      ((0 < ((param_29 < 32) ? param_29 : 32)) ? ((param_29 < 32) ? param_29 : 32) : 0)))) /\
     (result_33 = ((32 <= param_29) ? param_28 : 0))))))]);
    trace___addstate_imem_avx2 <-
    (trace___addstate_imem_avx2 ++
    [(Assert, ((0 <= result_35) /\ (result_35 <= 18446744073709551615)))]);
    buf <- result_35;
    lEN <- result_34;
    tRAILB <- result_33;
    r1 <- result_32;
    st <- (BArray224.set256 st 1 ((BArray224.get256 st 1) `^` r1));
    if ((0 < lEN)) {
      param_27 <- buf;
      param_26 <- lEN;
      param_25 <- tRAILB;
      (result_31, result_30, result_29, result_28, tmp__trace) <@ __mread_subu64 (
      param_27, param_26, param_25);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_26 < 8) ? param_26 : 8)) ? ((param_26 < 8) ? param_26 : 8) : 0)) /\
        (((0 < ((param_26 < 8) ? param_26 : 8)) ? ((param_26 < 8) ? param_26 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_27 +
         ((0 < ((param_26 < 8) ? param_26 : 8)) ? ((param_26 < 8) ? param_26 : 8) : 0))) /\
        ((param_27 +
         ((0 < ((param_26 < 8) ? param_26 : 8)) ? ((param_26 < 8) ? param_26 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_31 =
         (param_27 +
         ((0 < ((param_26 < 8) ? param_26 : 8)) ? ((param_26 < 8) ? param_26 : 8) : 0))) /\
        (result_30 =
        (param_26 -
        ((0 < ((param_26 < 8) ? param_26 : 8)) ? ((param_26 < 8) ? param_26 : 8) : 0)))) /\
       (result_29 = ((8 <= param_26) ? param_25 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_31) /\ (result_31 <= 18446744073709551615)))]);
      buf <- result_31;
      lEN <- result_30;
      tRAILB <- result_29;
      t64 <- result_28;
      t128_1 <- (zeroextu128 t64);
      param_24 <- buf;
      param_23 <- lEN;
      param_22 <- tRAILB;
      (result_27, result_26, result_25, result_24, tmp__trace) <@ __mread_subu256 (
      param_24, param_23, param_22);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_23 < 32) ? param_23 : 32)) ? ((param_23 < 32) ? 
                                                    param_23 : 32) : 0)) /\
        (((0 < ((param_23 < 32) ? param_23 : 32)) ? ((param_23 < 32) ? 
                                                    param_23 : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_24 +
         ((0 < ((param_23 < 32) ? param_23 : 32)) ? ((param_23 < 32) ? 
                                                    param_23 : 32) : 0))) /\
        ((param_24 +
         ((0 < ((param_23 < 32) ? param_23 : 32)) ? ((param_23 < 32) ? 
                                                    param_23 : 32) : 0)) <=
        18446744073709551615)) /\
       (((result_27 =
         (param_24 +
         ((0 < ((param_23 < 32) ? param_23 : 32)) ? ((param_23 < 32) ? 
                                                    param_23 : 32) : 0))) /\
        (result_26 =
        (param_23 -
        ((0 < ((param_23 < 32) ? param_23 : 32)) ? ((param_23 < 32) ? 
                                                   param_23 : 32) : 0)))) /\
       (result_25 = ((32 <= param_23) ? param_22 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_27) /\ (result_27 <= 18446744073709551615)))]);
      buf <- result_27;
      lEN <- result_26;
      tRAILB <- result_25;
      r3 <- result_24;
      param_21 <- buf;
      param_20 <- lEN;
      param_19 <- tRAILB;
      (result_23, result_22, result_21, result_20, tmp__trace) <@ __mread_subu64 (
      param_21, param_20, param_19);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_20 < 8) ? param_20 : 8)) ? ((param_20 < 8) ? param_20 : 8) : 0)) /\
        (((0 < ((param_20 < 8) ? param_20 : 8)) ? ((param_20 < 8) ? param_20 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_21 +
         ((0 < ((param_20 < 8) ? param_20 : 8)) ? ((param_20 < 8) ? param_20 : 8) : 0))) /\
        ((param_21 +
         ((0 < ((param_20 < 8) ? param_20 : 8)) ? ((param_20 < 8) ? param_20 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_23 =
         (param_21 +
         ((0 < ((param_20 < 8) ? param_20 : 8)) ? ((param_20 < 8) ? param_20 : 8) : 0))) /\
        (result_22 =
        (param_20 -
        ((0 < ((param_20 < 8) ? param_20 : 8)) ? ((param_20 < 8) ? param_20 : 8) : 0)))) /\
       (result_21 = ((8 <= param_20) ? param_19 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_23) /\ (result_23 <= 18446744073709551615)))]);
      buf <- result_23;
      lEN <- result_22;
      tRAILB <- result_21;
      t64 <- result_20;
      t128_0 <- (zeroextu128 t64);
      param_18 <- buf;
      param_17 <- lEN;
      param_16 <- tRAILB;
      (result_19, result_18, result_17, result_16, tmp__trace) <@ __mread_subu256 (
      param_18, param_17, param_16);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_17 < 32) ? param_17 : 32)) ? ((param_17 < 32) ? 
                                                    param_17 : 32) : 0)) /\
        (((0 < ((param_17 < 32) ? param_17 : 32)) ? ((param_17 < 32) ? 
                                                    param_17 : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_18 +
         ((0 < ((param_17 < 32) ? param_17 : 32)) ? ((param_17 < 32) ? 
                                                    param_17 : 32) : 0))) /\
        ((param_18 +
         ((0 < ((param_17 < 32) ? param_17 : 32)) ? ((param_17 < 32) ? 
                                                    param_17 : 32) : 0)) <=
        18446744073709551615)) /\
       (((result_19 =
         (param_18 +
         ((0 < ((param_17 < 32) ? param_17 : 32)) ? ((param_17 < 32) ? 
                                                    param_17 : 32) : 0))) /\
        (result_18 =
        (param_17 -
        ((0 < ((param_17 < 32) ? param_17 : 32)) ? ((param_17 < 32) ? 
                                                   param_17 : 32) : 0)))) /\
       (result_17 = ((32 <= param_17) ? param_16 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_19) /\ (result_19 <= 18446744073709551615)))]);
      buf <- result_19;
      lEN <- result_18;
      tRAILB <- result_17;
      r4 <- result_16;
      param_15 <- buf;
      param_14 <- lEN;
      param_13 <- tRAILB;
      (result_15, result_14, result_13, result_12, tmp__trace) <@ __mread_subu64 (
      param_15, param_14, param_13);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_14 < 8) ? param_14 : 8)) ? ((param_14 < 8) ? param_14 : 8) : 0)) /\
        (((0 < ((param_14 < 8) ? param_14 : 8)) ? ((param_14 < 8) ? param_14 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_15 +
         ((0 < ((param_14 < 8) ? param_14 : 8)) ? ((param_14 < 8) ? param_14 : 8) : 0))) /\
        ((param_15 +
         ((0 < ((param_14 < 8) ? param_14 : 8)) ? ((param_14 < 8) ? param_14 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_15 =
         (param_15 +
         ((0 < ((param_14 < 8) ? param_14 : 8)) ? ((param_14 < 8) ? param_14 : 8) : 0))) /\
        (result_14 =
        (param_14 -
        ((0 < ((param_14 < 8) ? param_14 : 8)) ? ((param_14 < 8) ? param_14 : 8) : 0)))) /\
       (result_13 = ((8 <= param_14) ? param_13 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_15) /\ (result_15 <= 18446744073709551615)))]);
      buf <- result_15;
      lEN <- result_14;
      tRAILB <- result_13;
      t64 <- result_12;
      t128_1 <- (VPINSR_2u64 t128_1 t64 (W8.of_int 1));
      param_12 <- buf;
      param_11 <- lEN;
      param_10 <- tRAILB;
      (result_11, result_10, result_9, result_8, tmp__trace) <@ __mread_subu256 (
      param_12, param_11, param_10);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_11 < 32) ? param_11 : 32)) ? ((param_11 < 32) ? 
                                                    param_11 : 32) : 0)) /\
        (((0 < ((param_11 < 32) ? param_11 : 32)) ? ((param_11 < 32) ? 
                                                    param_11 : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_12 +
         ((0 < ((param_11 < 32) ? param_11 : 32)) ? ((param_11 < 32) ? 
                                                    param_11 : 32) : 0))) /\
        ((param_12 +
         ((0 < ((param_11 < 32) ? param_11 : 32)) ? ((param_11 < 32) ? 
                                                    param_11 : 32) : 0)) <=
        18446744073709551615)) /\
       (((result_11 =
         (param_12 +
         ((0 < ((param_11 < 32) ? param_11 : 32)) ? ((param_11 < 32) ? 
                                                    param_11 : 32) : 0))) /\
        (result_10 =
        (param_11 -
        ((0 < ((param_11 < 32) ? param_11 : 32)) ? ((param_11 < 32) ? 
                                                   param_11 : 32) : 0)))) /\
       (result_9 = ((32 <= param_11) ? param_10 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_11) /\ (result_11 <= 18446744073709551615)))]);
      buf <- result_11;
      lEN <- result_10;
      tRAILB <- result_9;
      r5 <- result_8;
      param_9 <- buf;
      param_8 <- lEN;
      param_7 <- tRAILB;
      (result_7, result_6, result_5, result_4, tmp__trace) <@ __mread_subu64 (
      param_9, param_8, param_7);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_8 < 8) ? param_8 : 8)) ? ((param_8 < 8) ? param_8 : 8) : 0)) /\
        (((0 < ((param_8 < 8) ? param_8 : 8)) ? ((param_8 < 8) ? param_8 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_9 +
         ((0 < ((param_8 < 8) ? param_8 : 8)) ? ((param_8 < 8) ? param_8 : 8) : 0))) /\
        ((param_9 +
         ((0 < ((param_8 < 8) ? param_8 : 8)) ? ((param_8 < 8) ? param_8 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_7 =
         (param_9 +
         ((0 < ((param_8 < 8) ? param_8 : 8)) ? ((param_8 < 8) ? param_8 : 8) : 0))) /\
        (result_6 =
        (param_8 -
        ((0 < ((param_8 < 8) ? param_8 : 8)) ? ((param_8 < 8) ? param_8 : 8) : 0)))) /\
       (result_5 = ((8 <= param_8) ? param_7 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
      buf <- result_7;
      lEN <- result_6;
      tRAILB <- result_5;
      t64 <- result_4;
      t128_0 <- (VPINSR_2u64 t128_0 t64 (W8.of_int 1));
      r2 <-
      (W256.of_int
      (((W128.to_uint t128_0) %% (2 ^ 128)) +
      ((2 ^ 128) * (W128.to_uint t128_1))));
      st <- (BArray224.set256 st 2 ((BArray224.get256 st 2) `^` r2));
      param_6 <- buf;
      param_5 <- lEN;
      param_4 <- tRAILB;
      (result_3, result_2, result_1, result_0, tmp__trace) <@ __mread_subu256 (
      param_6, param_5, param_4);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_5 < 32) ? param_5 : 32)) ? ((param_5 < 32) ? param_5 : 32) : 0)) /\
        (((0 < ((param_5 < 32) ? param_5 : 32)) ? ((param_5 < 32) ? param_5 : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_6 +
         ((0 < ((param_5 < 32) ? param_5 : 32)) ? ((param_5 < 32) ? param_5 : 32) : 0))) /\
        ((param_6 +
         ((0 < ((param_5 < 32) ? param_5 : 32)) ? ((param_5 < 32) ? param_5 : 32) : 0)) <=
        18446744073709551615)) /\
       (((result_3 =
         (param_6 +
         ((0 < ((param_5 < 32) ? param_5 : 32)) ? ((param_5 < 32) ? param_5 : 32) : 0))) /\
        (result_2 =
        (param_5 -
        ((0 < ((param_5 < 32) ? param_5 : 32)) ? ((param_5 < 32) ? param_5 : 32) : 0)))) /\
       (result_1 = ((32 <= param_5) ? param_4 : 0))))))]);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      buf <- result_3;
      r6 <- result_0;
      param_3 <- st;
      param_2 <- r3;
      param_1 <- r4;
      param_0 <- r5;
      param <- r6;
      (result, b_result, tmp__trace) <@ __addstate_r3456_avx2 (param_3,
      (BArray224.init_arr (W8.of_int 255) 224), param_2, param_1, param_0,
      param);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ tmp__trace);
      trace___addstate_imem_avx2 <-
      (trace___addstate_imem_avx2 ++ [(Assert, (is_init b_result 0 224))]);
      st <- result;
    } else {
      
    }
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, buf, trace___addstate_imem_avx2);
  }
  proc __absorb_imem_avx2 (st:BArray224.t, b_st:BArray224.t, buf:int,
                           lEN:int, rATE8:int, tRAILB:int) : BArray224.t *
                                                             BArray224.t *
                                                             int * trace = {
    var iTERS:int;
    var i:int;
    var param:int;
    var param_0:BArray224.t;
    var result:BArray224.t;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:BArray224.t;
    var result_0:int;
    var result_1:BArray224.t;
    var param_5:BArray224.t;
    var result_2:BArray224.t;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:BArray224.t;
    var result_3:int;
    var result_4:BArray224.t;
    var b_result:BArray224.t;
    var b_result_0:BArray224.t;
    var b_result_1:BArray224.t;
    var b_result_2:BArray224.t;
    var trace___absorb_imem_avx2:trace;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    param_0 <- witness;
    param_4 <- witness;
    param_5 <- witness;
    param_9 <- witness;
    result <- witness;
    result_1 <- witness;
    result_2 <- witness;
    result_4 <- witness;
    trace___absorb_imem_avx2 <- [];
    trace___absorb_imem_avx2 <-
    (trace___absorb_imem_avx2 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (((((0 <= lEN) /\ (0 < rATE8)) /\ (rATE8 < 200)) /\
      (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
     (is_init b_st 0 224))))]);
    trace___absorb_imem_avx2 <-
    (trace___absorb_imem_avx2 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___absorb_imem_avx2 <-
    (trace___absorb_imem_avx2 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    iTERS <- (lEN %/ rATE8);
    if ((0 < iTERS)) {
      i <- 0;
      trace___absorb_imem_avx2 <-
      (trace___absorb_imem_avx2 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_9 <- st;
        param_8 <- buf;
        param_7 <- rATE8;
        param_6 <- 0;
        (result_4, b_result_2, result_3, tmp__trace) <@ __addstate_imem_avx2 (
        param_9, (BArray224.init_arr (W8.of_int 255) 224), param_8, param_7,
        param_6);
        trace___absorb_imem_avx2 <- (trace___absorb_imem_avx2 ++ tmp__trace);
        trace___absorb_imem_avx2 <-
        (trace___absorb_imem_avx2 ++
        [(Assert,
         (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
         (((0 <= (param_8 + param_7)) /\
          ((param_8 + param_7) <= 18446744073709551615)) /\
         ((is_init b_result_2 0 224) /\ (result_3 = (param_8 + param_7))))))]);
        trace___absorb_imem_avx2 <-
        (trace___absorb_imem_avx2 ++
        [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
        st <- result_4;
        buf <- result_3;
        param_5 <- st;
        (result_2, b_result_1, tmp__trace) <@ _keccakf1600_avx2 (param_5,
        (BArray224.init_arr (W8.of_int 255) 224));
        trace___absorb_imem_avx2 <- (trace___absorb_imem_avx2 ++ tmp__trace);
        trace___absorb_imem_avx2 <-
        (trace___absorb_imem_avx2 ++ [(Assert, (is_init b_result_1 0 224))]);
        st <- result_2;
        trace___absorb_imem_avx2 <-
        (trace___absorb_imem_avx2 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb_imem_avx2 <-
        (trace___absorb_imem_avx2 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
    } else {
      
    }
    lEN <- (lEN %% rATE8);
    param_4 <- st;
    param_3 <- buf;
    param_2 <- lEN;
    param_1 <- tRAILB;
    (result_1, b_result_0, result_0, tmp__trace) <@ __addstate_imem_avx2 (
    param_4, (BArray224.init_arr (W8.of_int 255) 224), param_3, param_2,
    param_1);
    trace___absorb_imem_avx2 <- (trace___absorb_imem_avx2 ++ tmp__trace);
    trace___absorb_imem_avx2 <-
    (trace___absorb_imem_avx2 ++
    [(Assert,
     (((0 <= param_2) /\ (param_2 <= 18446744073709551615)) /\
     (((0 <= (param_3 + param_2)) /\
      ((param_3 + param_2) <= 18446744073709551615)) /\
     ((is_init b_result_0 0 224) /\ (result_0 = (param_3 + param_2))))))]);
    trace___absorb_imem_avx2 <-
    (trace___absorb_imem_avx2 ++
    [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
    st <- result_1;
    buf <- result_0;
    if ((tRAILB <> 0)) {
      param_0 <- st;
      param <- rATE8;
      (result, b_result, tmp__trace) <@ __addratebit_avx2 (param_0,
      (BArray224.init_arr (W8.of_int 255) 224), param);
      trace___absorb_imem_avx2 <- (trace___absorb_imem_avx2 ++ tmp__trace);
      trace___absorb_imem_avx2 <-
      (trace___absorb_imem_avx2 ++ [(Assert, (is_init b_result 0 224))]);
      st <- result;
    } else {
      
    }
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (st, b_st, buf, trace___absorb_imem_avx2);
  }
  proc __pstate_imem_avx2 (pst:BArray200.t, b_pst:BArray200.t, aT:int,
                           buf:int, lEN:int, tRAILB:int) : BArray200.t *
                                                           BArray200.t *
                                                           int * int * trace = {
    var aLL:int;
    var lO:int;
    var t64:W64.t;
    var t256:W256.t;
    var t128:W128.t;
    var at:int;
    var param:int;
    var param_0:int;
    var param_1:int;
    var result:W64.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var result_3:W64.t;
    var result_4:int;
    var result_5:int;
    var result_6:int;
    var param_5:int;
    var param_6:int;
    var param_7:int;
    var result_7:W64.t;
    var result_8:int;
    var result_9:int;
    var result_10:int;
    var trace___pstate_imem_avx2:trace;
    trace___pstate_imem_avx2 <- [];
    trace___pstate_imem_avx2 <-
    (trace___pstate_imem_avx2 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     ((((((0 <= lEN) /\ (0 <= aT)) /\ (aT < 200)) /\
       (((aT + lEN) + ((tRAILB <> 0) ? 1 : 0)) < 200)) /\
      (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
     (is_init b_pst 0 200))))]);
    trace___pstate_imem_avx2 <-
    (trace___pstate_imem_avx2 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___pstate_imem_avx2 <-
    (trace___pstate_imem_avx2 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    trace___pstate_imem_avx2 <-
    (trace___pstate_imem_avx2 ++
    [(Assert, ((0 <= (aT %/ 8)) /\ ((aT %/ 8) <= 18446744073709551615)))]);
    at <- (aT %/ 8);
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        param_4 <- buf;
        param_3 <- lEN;
        param_2 <- tRAILB;
        (result_6, result_5, result_4, result_3, tmp__trace) <@ __mread_subu64 (
        param_4, param_3, param_2);
        trace___pstate_imem_avx2 <- (trace___pstate_imem_avx2 ++ tmp__trace);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) /\
          (((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_4 +
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
          ((param_4 +
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_6 =
           (param_4 +
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
          (result_5 =
          (param_3 -
          ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)))) /\
         (result_4 = ((8 <= param_3) ? param_2 : 0))))))]);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
        buf <- result_6;
        tRAILB <- result_4;
        t64 <- result_3;
        t64 <- (t64 `<<` (W8.of_int (8 * lO)));
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 200)))]);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 200)))]);
        pst <- (BArray200.set64 pst at ((BArray200.get64 pst at) `^` t64));
        aT <- 0;
        lEN <- 0;
      } else {
        if ((8 <= lEN)) {
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
          t64 <- (loadW64 Glob.mem buf);
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++
          [(Assert, ((0 <= (8 - lO)) /\ ((8 - lO) <= 18446744073709551615)))]);
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++
          [(Assert,
           ((0 <= (buf + (8 - lO))) /\
           ((buf + (8 - lO)) <= 18446744073709551615)))]);
          buf <- (buf + (8 - lO));
        } else {
          param_7 <- buf;
          param_6 <- (8 - lO);
          param_5 <- 0;
          (result_10, result_9, result_8, result_7, tmp__trace) <@ __mread_subu64 (
          param_7, param_6, param_5);
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++ tmp__trace);
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0)) /\
            (((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_7 +
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0))) /\
            ((param_7 +
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_10 =
             (param_7 +
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0))) /\
            (result_9 =
            (param_6 -
            ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)))) /\
           (result_8 = ((8 <= param_6) ? param_5 : 0))))))]);
          trace___pstate_imem_avx2 <-
          (trace___pstate_imem_avx2 ++
          [(Assert,
           ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
          buf <- result_10;
          t64 <- result_7;
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t64 <- (t64 `<<` (W8.of_int (8 * lO)));
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 200)))]);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 200)))]);
        pst <- (BArray200.set64 pst at ((BArray200.get64 pst at) `^` t64));
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        at <- (at + 1);
      }
    } else {
      
    }
    if ((32 <= lEN)) {
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert,
       ((0 <= ((aT %/ 8) + (4 * (lEN %/ 32)))) /\
       (((aT %/ 8) + (4 * (lEN %/ 32))) <= 18446744073709551615)))]);
      while ((at < ((aT %/ 8) + (4 * (lEN %/ 32))))) {
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 32))]);
        t256 <- (loadW256 Glob.mem buf);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert,
         ((0 <= (buf + 32)) /\ ((buf + 32) <= 18446744073709551615)))]);
        buf <- (buf + 32);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (8 * at)) /\ (((8 * at) + 32) <= 200)))]);
        pst <- (BArray200.set256d pst (8 * at) t256);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert, ((0 <= (at + 4)) /\ ((at + 4) <= 18446744073709551615)))]);
        at <- (at + 4);
        trace___pstate_imem_avx2 <-
        (trace___pstate_imem_avx2 ++
        [(Assert,
         ((0 <= ((aT %/ 8) + (4 * (lEN %/ 32)))) /\
         (((aT %/ 8) + (4 * (lEN %/ 32))) <= 18446744073709551615)))]);
      }
      lEN <- (lEN %% 32);
    } else {
      
    }
    if ((16 <= lEN)) {
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf 16))]);
      t128 <- (loadW128 Glob.mem buf);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (buf + 16)) /\ ((buf + 16) <= 18446744073709551615)))]);
      buf <- (buf + 16);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (8 * at)) /\ (((8 * at) + 16) <= 200)))]);
      pst <- (BArray200.set128d pst (8 * at) t128);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      at <- (at + 2);
      lEN <- (lEN - 16);
    } else {
      
    }
    if ((8 <= lEN)) {
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
      t64 <- (loadW64 Glob.mem buf);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
      buf <- (buf + 8);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (8 * at)) /\ (((8 * at) + 8) <= 200)))]);
      pst <- (BArray200.set64d pst (8 * at) t64);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      lEN <- (lEN - 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lEN) \/ (tRAILB <> 0))) {
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
      } else {
        
      }
      param_1 <- buf;
      param_0 <- lO;
      param <- tRAILB;
      (result_2, result_1, result_0, result, tmp__trace) <@ __mread_subu64 (
      param_1, param_0, param);
      trace___pstate_imem_avx2 <- (trace___pstate_imem_avx2 ++ tmp__trace);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) /\
        (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        ((param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_2 =
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        (result_1 =
        (param_0 -
        ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))) /\
       (result_0 = ((8 <= param_0) ? param : 0))))))]);
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      buf <- result_2;
      t64 <- result;
      trace___pstate_imem_avx2 <-
      (trace___pstate_imem_avx2 ++
      [(Assert, ((0 <= ((aLL %/ 8) * 8)) /\ ((((aLL %/ 8) * 8) + 8) <= 200)))]);
      pst <- (BArray200.set64 pst (aLL %/ 8) t64);
    } else {
      
    }
    b_pst <- (BArray200.init_arr (W8.of_int 255) 200);
    return (pst, b_pst, aLL, buf, trace___pstate_imem_avx2);
  }
  proc __pabsorb_imem_avx2 (pst:BArray200.t, b_pst:BArray200.t, aT:int,
                            st:BArray224.t, b_st:BArray224.t, buf:int,
                            lEN:int, rATE8:int, tRAILB:int) : BArray200.t *
                                                              BArray200.t *
                                                              int *
                                                              BArray224.t *
                                                              BArray224.t *
                                                              int * trace = {
    var aLL:int;
    var iTERS:int;
    var i:int;
    var param:int;
    var param_0:BArray224.t;
    var result:BArray224.t;
    var param_1:BArray200.t;
    var param_2:BArray224.t;
    var result_0:BArray224.t;
    var param_3:BArray200.t;
    var param_4:BArray224.t;
    var result_1:BArray224.t;
    var param_5:int;
    var param_6:int;
    var param_7:int;
    var param_8:int;
    var param_9:BArray200.t;
    var result_2:int;
    var result_3:int;
    var result_4:BArray200.t;
    var param_10:int;
    var param_11:BArray224.t;
    var result_5:BArray224.t;
    var param_12:int;
    var param_13:int;
    var param_14:int;
    var param_15:BArray224.t;
    var result_6:int;
    var result_7:BArray224.t;
    var param_16:int;
    var param_17:int;
    var param_18:int;
    var param_19:int;
    var param_20:BArray200.t;
    var result_8:int;
    var result_9:int;
    var result_10:BArray200.t;
    var param_21:BArray224.t;
    var result_11:BArray224.t;
    var param_22:int;
    var param_23:int;
    var param_24:int;
    var param_25:BArray224.t;
    var result_12:int;
    var result_13:BArray224.t;
    var param_26:BArray224.t;
    var result_14:BArray224.t;
    var param_27:BArray200.t;
    var param_28:BArray224.t;
    var result_15:BArray224.t;
    var param_29:int;
    var param_30:int;
    var param_31:int;
    var param_32:int;
    var param_33:BArray200.t;
    var result_16:int;
    var result_17:int;
    var result_18:BArray200.t;
    var b_result:BArray224.t;
    var b_result_0:BArray224.t;
    var b_result_1:BArray224.t;
    var b_result_2:BArray200.t;
    var b_result_3:BArray224.t;
    var b_result_4:BArray224.t;
    var b_result_5:BArray200.t;
    var b_result_6:BArray224.t;
    var b_result_7:BArray224.t;
    var b_result_8:BArray224.t;
    var b_result_9:BArray224.t;
    var b_result_10:BArray200.t;
    var trace___pabsorb_imem_avx2:trace;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    b_result_7 <- witness;
    b_result_8 <- witness;
    b_result_9 <- witness;
    b_result_10 <- witness;
    param_0 <- witness;
    param_1 <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_4 <- witness;
    param_9 <- witness;
    param_11 <- witness;
    param_15 <- witness;
    param_20 <- witness;
    param_21 <- witness;
    param_25 <- witness;
    param_26 <- witness;
    param_27 <- witness;
    param_28 <- witness;
    param_33 <- witness;
    result <- witness;
    result_0 <- witness;
    result_1 <- witness;
    result_4 <- witness;
    result_5 <- witness;
    result_7 <- witness;
    result_10 <- witness;
    result_11 <- witness;
    result_13 <- witness;
    result_14 <- witness;
    result_15 <- witness;
    result_18 <- witness;
    trace___pabsorb_imem_avx2 <- [];
    trace___pabsorb_imem_avx2 <-
    (trace___pabsorb_imem_avx2 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     ((((((((0 <= lEN) /\ (0 <= aT)) /\ (aT < rATE8)) /\ (0 < rATE8)) /\
        (rATE8 < 200)) /\
       (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
      (is_init b_pst 0 200)) /\
     (is_init b_st 0 224))))]);
    trace___pabsorb_imem_avx2 <-
    (trace___pabsorb_imem_avx2 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___pabsorb_imem_avx2 <-
    (trace___pabsorb_imem_avx2 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      param_9 <- pst;
      param_8 <- aT;
      param_7 <- buf;
      param_6 <- lEN;
      param_5 <- tRAILB;
      (result_4, b_result_2, result_3, result_2, tmp__trace) <@ __pstate_imem_avx2 (
      param_9, (BArray200.init_arr (W8.of_int 255) 200), param_8, param_7,
      param_6, param_5);
      trace___pabsorb_imem_avx2 <- (trace___pabsorb_imem_avx2 ++ tmp__trace);
      trace___pabsorb_imem_avx2 <-
      (trace___pabsorb_imem_avx2 ++
      [(Assert,
       (((0 <= param_6) /\ (param_6 <= 18446744073709551615)) /\
       (((0 <= (param_7 + param_6)) /\
        ((param_7 + param_6) <= 18446744073709551615)) /\
       (((is_init b_result_2 0 200) /\
        (result_3 = ((param_8 + param_6) + ((param_5 <> 0) ? 1 : 0)))) /\
       (result_2 = (param_7 + param_6))))))]);
      trace___pabsorb_imem_avx2 <-
      (trace___pabsorb_imem_avx2 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      pst <- result_4;
      aT <- result_3;
      buf <- result_2;
      if ((tRAILB <> 0)) {
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert,
         ((0 <= ((aT %/ 8) + 1)) /\
         (((aT %/ 8) + 1) <= 18446744073709551615)))]);
        i <- ((aT %/ 8) + 1);
        if ((aT <= 40)) {
          while ((i < 5)) {
            trace___pabsorb_imem_avx2 <-
            (trace___pabsorb_imem_avx2 ++
            [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 200)))]);
            pst <- (BArray200.set64 pst i (W64.of_int 0));
            trace___pabsorb_imem_avx2 <-
            (trace___pabsorb_imem_avx2 ++
            [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
            i <- (i + 1);
          }
          param_2 <- st;
          param_1 <- pst;
          (result_0, b_result_0, tmp__trace) <@ __addpst01_avx2 (param_2,
          (BArray224.init_arr (W8.of_int 255) 224), param_1,
          (BArray200.init_arr (W8.of_int 255) 200));
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++ tmp__trace);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert, (is_init b_result_0 0 224))]);
          st <- result_0;
          param_0 <- st;
          param <- rATE8;
          (result, b_result, tmp__trace) <@ __addratebit_avx2 (param_0,
          (BArray224.init_arr (W8.of_int 255) 224), param);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++ tmp__trace);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++ [(Assert, (is_init b_result 0 224))]);
          st <- result;
        } else {
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert,
           ((0 <= (rATE8 %/ 8)) /\ ((rATE8 %/ 8) <= 18446744073709551615)))]);
          while ((i < (rATE8 %/ 8))) {
            trace___pabsorb_imem_avx2 <-
            (trace___pabsorb_imem_avx2 ++
            [(Assert, ((0 <= (i * 8)) /\ (((i * 8) + 8) <= 200)))]);
            pst <- (BArray200.set64 pst i (W64.of_int 0));
            trace___pabsorb_imem_avx2 <-
            (trace___pabsorb_imem_avx2 ++
            [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
            i <- (i + 1);
            trace___pabsorb_imem_avx2 <-
            (trace___pabsorb_imem_avx2 ++
            [(Assert,
             ((0 <= (rATE8 %/ 8)) /\ ((rATE8 %/ 8) <= 18446744073709551615)))]);
          }
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert, ((0 <= (rATE8 - 1)) /\ (((rATE8 - 1) + 1) <= 200)))]);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert, ((0 <= (rATE8 - 1)) /\ (((rATE8 - 1) + 1) <= 200)))]);
          pst <-
          (BArray200.set8 pst (rATE8 - 1)
          ((BArray200.get8 pst (rATE8 - 1)) `^` (W8.of_int 128)));
          param_4 <- st;
          param_3 <- pst;
          (result_1, b_result_1, tmp__trace) <@ _addpstate_avx2 (param_4,
          (BArray224.init_arr (W8.of_int 255) 224), param_3,
          (BArray200.init_arr (W8.of_int 255) 200));
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++ tmp__trace);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert, (is_init b_result_1 0 224))]);
          st <- result_1;
        }
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        param_33 <- pst;
        param_32 <- aT;
        param_31 <- buf;
        param_30 <- (rATE8 - aT);
        param_29 <- 0;
        (result_18, b_result_10, result_17, result_16, tmp__trace) <@ 
        __pstate_imem_avx2 (param_33,
        (BArray200.init_arr (W8.of_int 255) 200), param_32, param_31,
        param_30, param_29);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert,
         (((0 <= param_30) /\ (param_30 <= 18446744073709551615)) /\
         (((0 <= (param_31 + param_30)) /\
          ((param_31 + param_30) <= 18446744073709551615)) /\
         (((is_init b_result_10 0 200) /\
          (result_17 = ((param_32 + param_30) + ((param_29 <> 0) ? 1 : 0)))) /\
         (result_16 = (param_31 + param_30))))))]);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert, ((0 <= result_16) /\ (result_16 <= 18446744073709551615)))]);
        pst <- result_18;
        buf <- result_16;
        lEN <- (lEN - (rATE8 - aT));
        param_28 <- st;
        param_27 <- pst;
        (result_15, b_result_9, tmp__trace) <@ _addpstate_avx2 (param_28,
        (BArray224.init_arr (W8.of_int 255) 224), param_27,
        (BArray200.init_arr (W8.of_int 255) 200));
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ [(Assert, (is_init b_result_9 0 224))]);
        st <- result_15;
        param_26 <- st;
        (result_14, b_result_8, tmp__trace) <@ _keccakf1600_avx2 (param_26,
        (BArray224.init_arr (W8.of_int 255) 224));
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ [(Assert, (is_init b_result_8 0 224))]);
        st <- result_14;
        aT <- 0;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- 0;
      trace___pabsorb_imem_avx2 <-
      (trace___pabsorb_imem_avx2 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_25 <- st;
        param_24 <- buf;
        param_23 <- rATE8;
        param_22 <- 0;
        (result_13, b_result_7, result_12, tmp__trace) <@ __addstate_imem_avx2 (
        param_25, (BArray224.init_arr (W8.of_int 255) 224), param_24,
        param_23, param_22);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert,
         (((0 <= param_23) /\ (param_23 <= 18446744073709551615)) /\
         (((0 <= (param_24 + param_23)) /\
          ((param_24 + param_23) <= 18446744073709551615)) /\
         ((is_init b_result_7 0 224) /\ (result_12 = (param_24 + param_23))))))]);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert, ((0 <= result_12) /\ (result_12 <= 18446744073709551615)))]);
        st <- result_13;
        buf <- result_12;
        param_21 <- st;
        (result_11, b_result_6, tmp__trace) <@ _keccakf1600_avx2 (param_21,
        (BArray224.init_arr (W8.of_int 255) 224));
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ [(Assert, (is_init b_result_6 0 224))]);
        st <- result_11;
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
      lEN <- (aLL %% rATE8);
      if ((tRAILB <> 0)) {
        param_15 <- st;
        param_14 <- buf;
        param_13 <- lEN;
        param_12 <- tRAILB;
        (result_7, b_result_4, result_6, tmp__trace) <@ __addstate_imem_avx2 (
        param_15, (BArray224.init_arr (W8.of_int 255) 224), param_14,
        param_13, param_12);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert,
         (((0 <= param_13) /\ (param_13 <= 18446744073709551615)) /\
         (((0 <= (param_14 + param_13)) /\
          ((param_14 + param_13) <= 18446744073709551615)) /\
         ((is_init b_result_4 0 224) /\ (result_6 = (param_14 + param_13))))))]);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++
        [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
        st <- result_7;
        buf <- result_6;
        param_11 <- st;
        param_10 <- rATE8;
        (result_5, b_result_3, tmp__trace) <@ __addratebit_avx2 (param_11,
        (BArray224.init_arr (W8.of_int 255) 224), param_10);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ tmp__trace);
        trace___pabsorb_imem_avx2 <-
        (trace___pabsorb_imem_avx2 ++ [(Assert, (is_init b_result_3 0 224))]);
        st <- result_5;
        aT <- 0;
      } else {
        if ((lEN <> 0)) {
          param_20 <- pst;
          param_19 <- 0;
          param_18 <- buf;
          param_17 <- lEN;
          param_16 <- tRAILB;
          (result_10, b_result_5, result_9, result_8, tmp__trace) <@ 
          __pstate_imem_avx2 (param_20,
          (BArray200.init_arr (W8.of_int 255) 200), param_19, param_18,
          param_17, param_16);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++ tmp__trace);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert,
           (((0 <= param_17) /\ (param_17 <= 18446744073709551615)) /\
           (((0 <= (param_18 + param_17)) /\
            ((param_18 + param_17) <= 18446744073709551615)) /\
           (((is_init b_result_5 0 200) /\
            (result_9 = ((param_19 + param_17) + ((param_16 <> 0) ? 1 : 0)))) /\
           (result_8 = (param_18 + param_17))))))]);
          trace___pabsorb_imem_avx2 <-
          (trace___pabsorb_imem_avx2 ++
          [(Assert, ((0 <= result_8) /\ (result_8 <= 18446744073709551615)))]);
          pst <- result_10;
          aT <- result_9;
          buf <- result_8;
        } else {
          
        }
      }
    }
    b_pst <- (BArray200.init_arr (W8.of_int 255) 200);
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (pst, b_pst, aT, st, b_st, buf, trace___pabsorb_imem_avx2);
  }
  proc __dumpstate_imem_avx2 (buf:int, lEN:int, st:BArray224.t,
                              b_st:BArray224.t) : int * trace = {
    var t128_0:W128.t;
    var t128_1:W128.t;
    var t:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var t256_4:W256.t;
    var param:W256.t;
    var param_0:int;
    var param_1:int;
    var result:int;
    var result_0:int;
    var param_2:W64.t;
    var param_3:int;
    var param_4:int;
    var result_1:int;
    var result_2:int;
    var param_5:W256.t;
    var param_6:int;
    var param_7:int;
    var result_3:int;
    var result_4:int;
    var param_8:W64.t;
    var param_9:int;
    var param_10:int;
    var result_5:int;
    var result_6:int;
    var param_11:W256.t;
    var param_12:int;
    var param_13:int;
    var result_7:int;
    var result_8:int;
    var param_14:W64.t;
    var param_15:int;
    var param_16:int;
    var result_9:int;
    var result_10:int;
    var param_17:W256.t;
    var param_18:int;
    var param_19:int;
    var result_11:int;
    var result_12:int;
    var param_20:W64.t;
    var param_21:int;
    var param_22:int;
    var result_13:int;
    var result_14:int;
    var param_23:W256.t;
    var param_24:int;
    var param_25:int;
    var result_15:int;
    var result_16:int;
    var param_26:W256.t;
    var param_27:int;
    var param_28:int;
    var result_17:int;
    var result_18:int;
    var param_29:W256.t;
    var param_30:int;
    var param_31:int;
    var result_19:int;
    var result_20:int;
    var trace___dumpstate_imem_avx2:trace;
    trace___dumpstate_imem_avx2 <- [];
    trace___dumpstate_imem_avx2 <-
    (trace___dumpstate_imem_avx2 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     ((((0 <= lEN) /\ (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
      (is_init b_st 0 224)) /\
     (lEN <= 200))))]);
    trace___dumpstate_imem_avx2 <-
    (trace___dumpstate_imem_avx2 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    if ((8 <= lEN)) {
      param_28 <- buf;
      param_27 <- 8;
      param_26 <- (BArray224.get256 st 0);
      (result_18, result_17, tmp__trace) <@ __mwrite_subu256 (param_28,
      param_27, param_26);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++ tmp__trace);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_27 < 32) ? param_27 : 32)) ? ((param_27 < 32) ? 
                                                    param_27 : 32) : 0)) /\
        (((0 < ((param_27 < 32) ? param_27 : 32)) ? ((param_27 < 32) ? 
                                                    param_27 : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_28 +
         ((0 < ((param_27 < 32) ? param_27 : 32)) ? ((param_27 < 32) ? 
                                                    param_27 : 32) : 0))) /\
        ((param_28 +
         ((0 < ((param_27 < 32) ? param_27 : 32)) ? ((param_27 < 32) ? 
                                                    param_27 : 32) : 0)) <=
        18446744073709551615)) /\
       ((result_18 =
        (param_28 +
        ((0 < ((param_27 < 32) ? param_27 : 32)) ? ((param_27 < 32) ? 
                                                   param_27 : 32) : 0))) /\
       (result_17 =
       (param_27 -
       ((0 < ((param_27 < 32) ? param_27 : 32)) ? ((param_27 < 32) ? 
                                                  param_27 : 32) : 0)))))))]);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++
      [(Assert, ((0 <= result_18) /\ (result_18 <= 18446744073709551615)))]);
      buf <- result_18;
      lEN <- (lEN - 8);
    } else {
      param_31 <- buf;
      param_30 <- lEN;
      param_29 <- (BArray224.get256 st 0);
      (result_20, result_19, tmp__trace) <@ __mwrite_subu256 (param_31,
      param_30, param_29);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++ tmp__trace);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_30 < 32) ? param_30 : 32)) ? ((param_30 < 32) ? 
                                                    param_30 : 32) : 0)) /\
        (((0 < ((param_30 < 32) ? param_30 : 32)) ? ((param_30 < 32) ? 
                                                    param_30 : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_31 +
         ((0 < ((param_30 < 32) ? param_30 : 32)) ? ((param_30 < 32) ? 
                                                    param_30 : 32) : 0))) /\
        ((param_31 +
         ((0 < ((param_30 < 32) ? param_30 : 32)) ? ((param_30 < 32) ? 
                                                    param_30 : 32) : 0)) <=
        18446744073709551615)) /\
       ((result_20 =
        (param_31 +
        ((0 < ((param_30 < 32) ? param_30 : 32)) ? ((param_30 < 32) ? 
                                                   param_30 : 32) : 0))) /\
       (result_19 =
       (param_30 -
       ((0 < ((param_30 < 32) ? param_30 : 32)) ? ((param_30 < 32) ? 
                                                  param_30 : 32) : 0)))))))]);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++
      [(Assert, ((0 <= result_20) /\ (result_20 <= 18446744073709551615)))]);
      buf <- result_20;
      lEN <- result_19;
    }
    param_25 <- buf;
    param_24 <- lEN;
    param_23 <- (BArray224.get256 st 1);
    (result_16, result_15, tmp__trace) <@ __mwrite_subu256 (param_25,
    param_24, param_23);
    trace___dumpstate_imem_avx2 <-
    (trace___dumpstate_imem_avx2 ++ tmp__trace);
    trace___dumpstate_imem_avx2 <-
    (trace___dumpstate_imem_avx2 ++
    [(Assert,
     (((0 <=
       ((0 < ((param_24 < 32) ? param_24 : 32)) ? ((param_24 < 32) ? 
                                                  param_24 : 32) : 0)) /\
      (((0 < ((param_24 < 32) ? param_24 : 32)) ? ((param_24 < 32) ? 
                                                  param_24 : 32) : 0) <=
      18446744073709551615)) /\
     (((0 <=
       (param_25 +
       ((0 < ((param_24 < 32) ? param_24 : 32)) ? ((param_24 < 32) ? 
                                                  param_24 : 32) : 0))) /\
      ((param_25 +
       ((0 < ((param_24 < 32) ? param_24 : 32)) ? ((param_24 < 32) ? 
                                                  param_24 : 32) : 0)) <=
      18446744073709551615)) /\
     ((result_16 =
      (param_25 +
      ((0 < ((param_24 < 32) ? param_24 : 32)) ? ((param_24 < 32) ? param_24 : 32) : 0))) /\
     (result_15 =
     (param_24 -
     ((0 < ((param_24 < 32) ? param_24 : 32)) ? ((param_24 < 32) ? param_24 : 32) : 0)))))))]);
    trace___dumpstate_imem_avx2 <-
    (trace___dumpstate_imem_avx2 ++
    [(Assert, ((0 <= result_16) /\ (result_16 <= 18446744073709551615)))]);
    buf <- result_16;
    lEN <- result_15;
    if ((0 < lEN)) {
      t128_0 <- (truncateu128 (BArray224.get256 st 2));
      t128_1 <- (VEXTRACTI128 (BArray224.get256 st 2) (W8.of_int 1));
      t <- (truncateu64 t128_1);
      param_22 <- buf;
      param_21 <- lEN;
      param_20 <- t;
      (result_14, result_13, tmp__trace) <@ __mwrite_subu64 (param_22,
      param_21, param_20);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++ tmp__trace);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_21 < 8) ? param_21 : 8)) ? ((param_21 < 8) ? param_21 : 8) : 0)) /\
        (((0 < ((param_21 < 8) ? param_21 : 8)) ? ((param_21 < 8) ? param_21 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_22 +
         ((0 < ((param_21 < 8) ? param_21 : 8)) ? ((param_21 < 8) ? param_21 : 8) : 0))) /\
        ((param_22 +
         ((0 < ((param_21 < 8) ? param_21 : 8)) ? ((param_21 < 8) ? param_21 : 8) : 0)) <=
        18446744073709551615)) /\
       ((result_14 =
        (param_22 +
        ((0 < ((param_21 < 8) ? param_21 : 8)) ? ((param_21 < 8) ? param_21 : 8) : 0))) /\
       (result_13 =
       (param_21 -
       ((0 < ((param_21 < 8) ? param_21 : 8)) ? ((param_21 < 8) ? param_21 : 8) : 0)))))))]);
      trace___dumpstate_imem_avx2 <-
      (trace___dumpstate_imem_avx2 ++
      [(Assert, ((0 <= result_14) /\ (result_14 <= 18446744073709551615)))]);
      buf <- result_14;
      lEN <- result_13;
      t128_1 <- (VPUNPCKH_2u64 t128_1 t128_1);
      if ((0 < lEN)) {
        t256_0 <-
        (VPBLEND_8u32 (BArray224.get256 st 3) (BArray224.get256 st 4)
        (W8.of_int 240));
        t256_1 <-
        (VPBLEND_8u32 (BArray224.get256 st 4) (BArray224.get256 st 3)
        (W8.of_int 240));
        t256_2 <-
        (VPBLEND_8u32 (BArray224.get256 st 5) (BArray224.get256 st 6)
        (W8.of_int 240));
        t256_3 <-
        (VPBLEND_8u32 (BArray224.get256 st 6) (BArray224.get256 st 5)
        (W8.of_int 240));
        if ((0 < lEN)) {
          t256_4 <- (VPBLEND_8u32 t256_0 t256_3 (W8.of_int 195));
          param_19 <- buf;
          param_18 <- lEN;
          param_17 <- t256_4;
          (result_12, result_11, tmp__trace) <@ __mwrite_subu256 (param_19,
          param_18, param_17);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_18 < 32) ? param_18 : 32)) ? ((param_18 < 32) ? 
                                                        param_18 : 32) : 0)) /\
            (((0 < ((param_18 < 32) ? param_18 : 32)) ? ((param_18 < 32) ? 
                                                        param_18 : 32) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_19 +
             ((0 < ((param_18 < 32) ? param_18 : 32)) ? ((param_18 < 32) ? 
                                                        param_18 : 32) : 0))) /\
            ((param_19 +
             ((0 < ((param_18 < 32) ? param_18 : 32)) ? ((param_18 < 32) ? 
                                                        param_18 : 32) : 0)) <=
            18446744073709551615)) /\
           ((result_12 =
            (param_19 +
            ((0 < ((param_18 < 32) ? param_18 : 32)) ? ((param_18 < 32) ? 
                                                       param_18 : 32) : 0))) /\
           (result_11 =
           (param_18 -
           ((0 < ((param_18 < 32) ? param_18 : 32)) ? ((param_18 < 32) ? 
                                                      param_18 : 32) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           ((0 <= result_12) /\ (result_12 <= 18446744073709551615)))]);
          buf <- result_12;
          lEN <- result_11;
        } else {
          
        }
        if ((0 < lEN)) {
          t <- (truncateu64 t128_0);
          param_16 <- buf;
          param_15 <- lEN;
          param_14 <- t;
          (result_10, result_9, tmp__trace) <@ __mwrite_subu64 (param_16,
          param_15, param_14);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_15 < 8) ? param_15 : 8)) ? ((param_15 < 8) ? 
                                                      param_15 : 8) : 0)) /\
            (((0 < ((param_15 < 8) ? param_15 : 8)) ? ((param_15 < 8) ? 
                                                      param_15 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_16 +
             ((0 < ((param_15 < 8) ? param_15 : 8)) ? ((param_15 < 8) ? 
                                                      param_15 : 8) : 0))) /\
            ((param_16 +
             ((0 < ((param_15 < 8) ? param_15 : 8)) ? ((param_15 < 8) ? 
                                                      param_15 : 8) : 0)) <=
            18446744073709551615)) /\
           ((result_10 =
            (param_16 +
            ((0 < ((param_15 < 8) ? param_15 : 8)) ? ((param_15 < 8) ? 
                                                     param_15 : 8) : 0))) /\
           (result_9 =
           (param_15 -
           ((0 < ((param_15 < 8) ? param_15 : 8)) ? ((param_15 < 8) ? 
                                                    param_15 : 8) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
          buf <- result_10;
          lEN <- result_9;
          t128_0 <- (VPUNPCKH_2u64 t128_0 t128_0);
        } else {
          
        }
        if ((0 < lEN)) {
          t256_4 <- (VPBLEND_8u32 t256_3 t256_1 (W8.of_int 195));
          param_13 <- buf;
          param_12 <- lEN;
          param_11 <- t256_4;
          (result_8, result_7, tmp__trace) <@ __mwrite_subu256 (param_13,
          param_12, param_11);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_12 < 32) ? param_12 : 32)) ? ((param_12 < 32) ? 
                                                        param_12 : 32) : 0)) /\
            (((0 < ((param_12 < 32) ? param_12 : 32)) ? ((param_12 < 32) ? 
                                                        param_12 : 32) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_13 +
             ((0 < ((param_12 < 32) ? param_12 : 32)) ? ((param_12 < 32) ? 
                                                        param_12 : 32) : 0))) /\
            ((param_13 +
             ((0 < ((param_12 < 32) ? param_12 : 32)) ? ((param_12 < 32) ? 
                                                        param_12 : 32) : 0)) <=
            18446744073709551615)) /\
           ((result_8 =
            (param_13 +
            ((0 < ((param_12 < 32) ? param_12 : 32)) ? ((param_12 < 32) ? 
                                                       param_12 : 32) : 0))) /\
           (result_7 =
           (param_12 -
           ((0 < ((param_12 < 32) ? param_12 : 32)) ? ((param_12 < 32) ? 
                                                      param_12 : 32) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert, ((0 <= result_8) /\ (result_8 <= 18446744073709551615)))]);
          buf <- result_8;
          lEN <- result_7;
        } else {
          
        }
        if ((0 < lEN)) {
          t <- (truncateu64 t128_1);
          param_10 <- buf;
          param_9 <- lEN;
          param_8 <- t;
          (result_6, result_5, tmp__trace) <@ __mwrite_subu64 (param_10,
          param_9, param_8);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? 
                                                    param_9 : 8) : 0)) /\
            (((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? 
                                                    param_9 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_10 +
             ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? 
                                                    param_9 : 8) : 0))) /\
            ((param_10 +
             ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? 
                                                    param_9 : 8) : 0)) <=
            18446744073709551615)) /\
           ((result_6 =
            (param_10 +
            ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0))) /\
           (result_5 =
           (param_9 -
           ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
          buf <- result_6;
          lEN <- result_5;
        } else {
          
        }
        if ((0 < lEN)) {
          t256_4 <- (VPBLEND_8u32 t256_2 t256_0 (W8.of_int 195));
          param_7 <- buf;
          param_6 <- lEN;
          param_5 <- t256_4;
          (result_4, result_3, tmp__trace) <@ __mwrite_subu256 (param_7,
          param_6, param_5);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_6 < 32) ? param_6 : 32)) ? ((param_6 < 32) ? 
                                                      param_6 : 32) : 0)) /\
            (((0 < ((param_6 < 32) ? param_6 : 32)) ? ((param_6 < 32) ? 
                                                      param_6 : 32) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_7 +
             ((0 < ((param_6 < 32) ? param_6 : 32)) ? ((param_6 < 32) ? 
                                                      param_6 : 32) : 0))) /\
            ((param_7 +
             ((0 < ((param_6 < 32) ? param_6 : 32)) ? ((param_6 < 32) ? 
                                                      param_6 : 32) : 0)) <=
            18446744073709551615)) /\
           ((result_4 =
            (param_7 +
            ((0 < ((param_6 < 32) ? param_6 : 32)) ? ((param_6 < 32) ? 
                                                     param_6 : 32) : 0))) /\
           (result_3 =
           (param_6 -
           ((0 < ((param_6 < 32) ? param_6 : 32)) ? ((param_6 < 32) ? 
                                                    param_6 : 32) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
          buf <- result_4;
          lEN <- result_3;
        } else {
          
        }
        if ((0 < lEN)) {
          t <- (truncateu64 t128_0);
          param_4 <- buf;
          param_3 <- lEN;
          param_2 <- t;
          (result_2, result_1, tmp__trace) <@ __mwrite_subu64 (param_4,
          param_3, param_2);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0)) /\
            (((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_4 +
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0))) /\
            ((param_4 +
             ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? 
                                                    param_3 : 8) : 0)) <=
            18446744073709551615)) /\
           ((result_2 =
            (param_4 +
            ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
           (result_1 =
           (param_3 -
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
          buf <- result_2;
          lEN <- result_1;
        } else {
          
        }
        if ((0 < lEN)) {
          t256_4 <- (VPBLEND_8u32 t256_1 t256_2 (W8.of_int 195));
          param_1 <- buf;
          param_0 <- lEN;
          param <- t256_4;
          (result_0, result, tmp__trace) <@ __mwrite_subu256 (param_1,
          param_0, param);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++ tmp__trace);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_0 < 32) ? param_0 : 32)) ? ((param_0 < 32) ? 
                                                      param_0 : 32) : 0)) /\
            (((0 < ((param_0 < 32) ? param_0 : 32)) ? ((param_0 < 32) ? 
                                                      param_0 : 32) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_1 +
             ((0 < ((param_0 < 32) ? param_0 : 32)) ? ((param_0 < 32) ? 
                                                      param_0 : 32) : 0))) /\
            ((param_1 +
             ((0 < ((param_0 < 32) ? param_0 : 32)) ? ((param_0 < 32) ? 
                                                      param_0 : 32) : 0)) <=
            18446744073709551615)) /\
           ((result_0 =
            (param_1 +
            ((0 < ((param_0 < 32) ? param_0 : 32)) ? ((param_0 < 32) ? 
                                                     param_0 : 32) : 0))) /\
           (result =
           (param_0 -
           ((0 < ((param_0 < 32) ? param_0 : 32)) ? ((param_0 < 32) ? 
                                                    param_0 : 32) : 0)))))))]);
          trace___dumpstate_imem_avx2 <-
          (trace___dumpstate_imem_avx2 ++
          [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
          buf <- result_0;
        } else {
          
        }
      } else {
        
      }
    } else {
      
    }
    return (buf, trace___dumpstate_imem_avx2);
  }
  proc __squeeze_imem_avx2 (buf:int, lEN:int, st:BArray224.t,
                            b_st:BArray224.t, rATE8:int) : int *
                                                           BArray224.t *
                                                           BArray224.t *
                                                           trace = {
    var iTERS:int;
    var lO:int;
    var i:int;
    var param:BArray224.t;
    var param_0:int;
    var param_1:int;
    var result:int;
    var param_2:BArray224.t;
    var result_0:BArray224.t;
    var param_3:BArray224.t;
    var param_4:int;
    var param_5:int;
    var result_1:int;
    var param_6:BArray224.t;
    var result_2:BArray224.t;
    var b_result:BArray224.t;
    var b_result_0:BArray224.t;
    var trace___squeeze_imem_avx2:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_2 <- witness;
    param_3 <- witness;
    param_6 <- witness;
    result_0 <- witness;
    result_2 <- witness;
    trace___squeeze_imem_avx2 <- [];
    trace___squeeze_imem_avx2 <-
    (trace___squeeze_imem_avx2 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     (((((0 <= lEN) /\ (0 < rATE8)) /\ (rATE8 < 200)) /\
      (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
     (is_init b_st 0 224))))]);
    trace___squeeze_imem_avx2 <-
    (trace___squeeze_imem_avx2 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- 0;
        trace___squeeze_imem_avx2 <-
        (trace___squeeze_imem_avx2 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
        while ((i < iTERS)) {
          param_6 <- st;
          (result_2, b_result_0, tmp__trace) <@ _keccakf1600_avx2 (param_6,
          (BArray224.init_arr (W8.of_int 255) 224));
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++ tmp__trace);
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++
          [(Assert, (is_init b_result_0 0 224))]);
          st <- result_2;
          param_5 <- buf;
          param_4 <- rATE8;
          param_3 <- st;
          (result_1, tmp__trace) <@ __dumpstate_imem_avx2 (param_5, param_4,
          param_3, (BArray224.init_arr (W8.of_int 255) 224));
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++ tmp__trace);
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++
          [(Assert,
           (((0 <= param_4) /\ (param_4 <= 18446744073709551615)) /\
           (((0 <= (param_5 + param_4)) /\
            ((param_5 + param_4) <= 18446744073709551615)) /\
           (result_1 = (param_5 + param_4)))))]);
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++
          [(Assert, ((0 <= result_1) /\ (result_1 <= 18446744073709551615)))]);
          buf <- result_1;
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++
          [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
          i <- (i + 1);
          trace___squeeze_imem_avx2 <-
          (trace___squeeze_imem_avx2 ++
          [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
        }
      } else {
        
      }
      if ((0 < lO)) {
        param_2 <- st;
        (result_0, b_result, tmp__trace) <@ _keccakf1600_avx2 (param_2,
        (BArray224.init_arr (W8.of_int 255) 224));
        trace___squeeze_imem_avx2 <-
        (trace___squeeze_imem_avx2 ++ tmp__trace);
        trace___squeeze_imem_avx2 <-
        (trace___squeeze_imem_avx2 ++ [(Assert, (is_init b_result 0 224))]);
        st <- result_0;
        param_1 <- buf;
        param_0 <- lO;
        param <- st;
        (result, tmp__trace) <@ __dumpstate_imem_avx2 (param_1, param_0,
        param, (BArray224.init_arr (W8.of_int 255) 224));
        trace___squeeze_imem_avx2 <-
        (trace___squeeze_imem_avx2 ++ tmp__trace);
        trace___squeeze_imem_avx2 <-
        (trace___squeeze_imem_avx2 ++
        [(Assert,
         (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
         (((0 <= (param_1 + param_0)) /\
          ((param_1 + param_0) <= 18446744073709551615)) /\
         (result = (param_1 + param_0)))))]);
        trace___squeeze_imem_avx2 <-
        (trace___squeeze_imem_avx2 ++
        [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
        buf <- result;
      } else {
        
      }
    } else {
      
    }
    b_st <- (BArray224.init_arr (W8.of_int 255) 224);
    return (buf, st, b_st, trace___squeeze_imem_avx2);
  }

   proc __state_init_avx2x4 (st:BArray800.t, b_st:BArray800.t) : BArray800.t *
                                                                BArray800.t *
                                                                trace = {
    var z256:W256.t;
    var i:int;
    var trace___state_init_avx2x4:trace;
    trace___state_init_avx2x4 <- [];
    z256 <- (set0_256);
    i <- 0;
    while ((i < 800)) {
      trace___state_init_avx2x4 <-
      (trace___state_init_avx2x4 ++
      [(Assert, ((0 <= i) /\ ((i + 32) <= 800)))]);
      b_st <-
      (BArray800.set256d b_st i
      (W256.of_int
      115792089237316195423570985008687907853269984665640564039457584007913129639935
      ));
      st <- (BArray800.set256d st i z256);
      trace___state_init_avx2x4 <-
      (trace___state_init_avx2x4 ++
      [(Assert, ((0 <= (i + 32)) /\ ((i + 32) <= 18446744073709551615)))]);
      i <- (i + 32);
    }
    return (st, b_st, trace___state_init_avx2x4);
  }
  proc __addratebit_avx2x4 (st:BArray800.t, b_st:BArray800.t, rATE8:int) : 
  BArray800.t * BArray800.t * trace = {
    var t64:W64.t;
    var t128:W128.t;
    var t256:W256.t;
    var trace___addratebit_avx2x4:trace;
    trace___addratebit_avx2x4 <- [];
    trace___addratebit_avx2x4 <-
    (trace___addratebit_avx2x4 ++
    [(Assert, (((is_init b_st 0 800) /\ (0 < rATE8)) /\ (rATE8 < 200)))]);
    t64 <- (W64.of_int 1);
    t64 <- (t64 `<<` (W8.of_int (((8 * rATE8) - 1) %% 64)));
    t128 <- (zeroextu128 t64);
    t256 <- (VPBROADCAST_4u64 (truncateu64 t128));
    trace___addratebit_avx2x4 <-
    (trace___addratebit_avx2x4 ++
    [(Assert,
     ((0 <= (((rATE8 - 1) %/ 8) * 32)) /\
     (((((rATE8 - 1) %/ 8) * 32) + 32) <= 800)))]);
    t256 <- (t256 `^` (BArray800.get256 st ((rATE8 - 1) %/ 8)));
    trace___addratebit_avx2x4 <-
    (trace___addratebit_avx2x4 ++
    [(Assert,
     ((0 <= (((rATE8 - 1) %/ 8) * 32)) /\
     (((((rATE8 - 1) %/ 8) * 32) + 32) <= 800)))]);
    st <- (BArray800.set256 st ((rATE8 - 1) %/ 8) t256);
    b_st <- (BArray800.init_arr (W8.of_int 255) 800);
    return (st, b_st, trace___addratebit_avx2x4);
  }
  proc __u256x4_4u64x4 (x0:W256.t, x1:W256.t, x2:W256.t, x3:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * trace = {
    var y0:W256.t;
    var y1:W256.t;
    var y2:W256.t;
    var y3:W256.t;
    var trace___u256x4_4u64x4:trace;
    trace___u256x4_4u64x4 <- [];
    y0 <- (VPUNPCKL_4u64 x0 x1);
    y1 <- (VPUNPCKH_4u64 x0 x1);
    y2 <- (VPUNPCKL_4u64 x2 x3);
    y3 <- (VPUNPCKH_4u64 x2 x3);
    x0 <- (VPERM2I128 y0 y2 (W8.of_int 32));
    x1 <- (VPERM2I128 y1 y3 (W8.of_int 32));
    x2 <- (VPERM2I128 y0 y2 (W8.of_int 49));
    x3 <- (VPERM2I128 y1 y3 (W8.of_int 49));
    return (x0, x1, x2, x3, trace___u256x4_4u64x4);
  }
  proc __4u64x4_u256x4 (y0:W256.t, y1:W256.t, y2:W256.t, y3:W256.t) : 
  W256.t * W256.t * W256.t * W256.t * trace = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var trace___4u64x4_u256x4:trace;
    trace___4u64x4_u256x4 <- [];
    x0 <- (VPERM2I128 y0 y2 (W8.of_int 32));
    x1 <- (VPERM2I128 y1 y3 (W8.of_int 32));
    x2 <- (VPERM2I128 y0 y2 (W8.of_int 49));
    x3 <- (VPERM2I128 y1 y3 (W8.of_int 49));
    y0 <- (VPUNPCKL_4u64 x0 x1);
    y1 <- (VPUNPCKH_4u64 x0 x1);
    y2 <- (VPUNPCKL_4u64 x2 x3);
    y3 <- (VPUNPCKH_4u64 x2 x3);
    return (y0, y1, y2, y3, trace___4u64x4_u256x4);
  }
  proc __addstate_bcast_imem_avx2x4 (st:BArray800.t, b_st:BArray800.t,
                                     aT:int, buf:int, lEN:int, tRAILB:int) : 
  BArray800.t * BArray800.t * int * int * trace = {
    var aLL:int;
    var lO:int;
    var t256:W256.t;
    var at:int;
    var param:int;
    var param_0:int;
    var param_1:int;
    var result:W256.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var result_3:W256.t;
    var result_4:int;
    var result_5:int;
    var result_6:int;
    var param_5:int;
    var param_6:int;
    var param_7:int;
    var result_7:W256.t;
    var result_8:int;
    var result_9:int;
    var result_10:int;
    var trace___addstate_bcast_imem_avx2x4:trace;
    trace___addstate_bcast_imem_avx2x4 <- [];
    trace___addstate_bcast_imem_avx2x4 <-
    (trace___addstate_bcast_imem_avx2x4 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     ((((((0 <= lEN) /\ (0 <= aT)) /\ (aT < 200)) /\
       (((aT + lEN) + ((tRAILB <> 0) ? 1 : 0)) < 200)) /\
      (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
     (is_init b_st 0 800))))]);
    trace___addstate_bcast_imem_avx2x4 <-
    (trace___addstate_bcast_imem_avx2x4 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___addstate_bcast_imem_avx2x4 <-
    (trace___addstate_bcast_imem_avx2x4 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    trace___addstate_bcast_imem_avx2x4 <-
    (trace___addstate_bcast_imem_avx2x4 ++
    [(Assert,
     ((0 <= (32 * (aT %/ 8))) /\ ((32 * (aT %/ 8)) <= 18446744073709551615)))]);
    at <- (32 * (aT %/ 8));
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        param_4 <- buf;
        param_3 <- lEN;
        param_2 <- tRAILB;
        (result_6, result_5, result_4, result_3, tmp__trace) <@ __mread_bcast_4subu64 (
        param_4, param_3, param_2);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++ tmp__trace);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) /\
          (((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_4 +
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
          ((param_4 +
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_6 =
           (param_4 +
           ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
          (result_5 =
          (param_3 -
          ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)))) /\
         (result_4 = ((8 <= param_3) ? param_2 : 0))))))]);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
        buf <- result_6;
        tRAILB <- result_4;
        t256 <- result_3;
        t256 <- (VPSLL_4u64 t256 (W128.of_int (8 * lO)));
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
        t256 <- (t256 `^` (BArray800.get256d st at));
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
        st <- (BArray800.set256d st at t256);
        aT <- 0;
        lEN <- 0;
      } else {
        if ((8 <= lEN)) {
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++
          [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
          t256 <- (VPBROADCAST_4u64 (loadW64 Glob.mem buf));
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++
          [(Assert, ((0 <= (8 - lO)) /\ ((8 - lO) <= 18446744073709551615)))]);
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++
          [(Assert,
           ((0 <= (buf + (8 - lO))) /\
           ((buf + (8 - lO)) <= 18446744073709551615)))]);
          buf <- (buf + (8 - lO));
        } else {
          param_7 <- buf;
          param_6 <- (8 - lO);
          param_5 <- 0;
          (result_10, result_9, result_8, result_7, tmp__trace) <@ __mread_bcast_4subu64 (
          param_7, param_6, param_5);
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++ tmp__trace);
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0)) /\
            (((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_7 +
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0))) /\
            ((param_7 +
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_10 =
             (param_7 +
             ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? 
                                                    param_6 : 8) : 0))) /\
            (result_9 =
            (param_6 -
            ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)))) /\
           (result_8 = ((8 <= param_6) ? param_5 : 0))))))]);
          trace___addstate_bcast_imem_avx2x4 <-
          (trace___addstate_bcast_imem_avx2x4 ++
          [(Assert,
           ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
          buf <- result_10;
          t256 <- result_7;
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t256 <- (VPSLL_4u64 t256 (W128.of_int (8 * lO)));
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
        t256 <- (t256 `^` (BArray800.get256d st at));
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
        st <- (BArray800.set256d st at t256);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 32)) /\ ((at + 32) <= 18446744073709551615)))]);
        at <- (at + 32);
      }
    } else {
      
    }
    if ((8 <= lEN)) {
      trace___addstate_bcast_imem_avx2x4 <-
      (trace___addstate_bcast_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((32 * (aT %/ 8)) + (32 * (lEN %/ 8)))) /\
       (((32 * (aT %/ 8)) + (32 * (lEN %/ 8))) <= 18446744073709551615)))]);
      while ((at < ((32 * (aT %/ 8)) + (32 * (lEN %/ 8))))) {
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf 8))]);
        t256 <- (VPBROADCAST_4u64 (loadW64 Glob.mem buf));
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= (buf + 8)) /\ ((buf + 8) <= 18446744073709551615)))]);
        buf <- (buf + 8);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
        t256 <- (t256 `^` (BArray800.get256d st at));
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
        st <- (BArray800.set256d st at t256);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 32)) /\ ((at + 32) <= 18446744073709551615)))]);
        at <- (at + 32);
        trace___addstate_bcast_imem_avx2x4 <-
        (trace___addstate_bcast_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((32 * (aT %/ 8)) + (32 * (lEN %/ 8)))) /\
         (((32 * (aT %/ 8)) + (32 * (lEN %/ 8))) <= 18446744073709551615)))]);
      }
      lEN <- ((aT + lEN) %% 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
      } else {
        
      }
      param_1 <- buf;
      param_0 <- lO;
      param <- tRAILB;
      (result_2, result_1, result_0, result, tmp__trace) <@ __mread_bcast_4subu64 (
      param_1, param_0, param);
      trace___addstate_bcast_imem_avx2x4 <-
      (trace___addstate_bcast_imem_avx2x4 ++ tmp__trace);
      trace___addstate_bcast_imem_avx2x4 <-
      (trace___addstate_bcast_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) /\
        (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        ((param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_2 =
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        (result_1 =
        (param_0 -
        ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))) /\
       (result_0 = ((8 <= param_0) ? param : 0))))))]);
      trace___addstate_bcast_imem_avx2x4 <-
      (trace___addstate_bcast_imem_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      buf <- result_2;
      t256 <- result;
      trace___addstate_bcast_imem_avx2x4 <-
      (trace___addstate_bcast_imem_avx2x4 ++
      [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
      t256 <- (t256 `^` (BArray800.get256d st at));
      trace___addstate_bcast_imem_avx2x4 <-
      (trace___addstate_bcast_imem_avx2x4 ++
      [(Assert, ((0 <= at) /\ ((at + 32) <= 800)))]);
      st <- (BArray800.set256d st at t256);
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255) 800);
    return (st, b_st, aLL, buf, trace___addstate_bcast_imem_avx2x4);
  }
  proc __absorb_bcast_imem_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                                   buf:int, lEN:int, rATE8:int, tRAILB:int) : 
  BArray800.t * BArray800.t * int * int * trace = {
    var aLL:int;
    var iTERS:int;
    var i:int;
    var param:int;
    var param_0:BArray800.t;
    var result:BArray800.t;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:BArray800.t;
    var result_0:int;
    var result_1:int;
    var result_2:BArray800.t;
    var param_6:int;
    var param_7:BArray800.t;
    var result_3:BArray800.t;
    var param_8:int;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var param_12:BArray800.t;
    var result_4:int;
    var result_5:int;
    var result_6:BArray800.t;
    var param_13:BArray800.t;
    var result_7:BArray800.t;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var param_17:int;
    var param_18:BArray800.t;
    var result_8:int;
    var result_9:int;
    var result_10:BArray800.t;
    var param_19:BArray800.t;
    var result_11:BArray800.t;
    var param_20:int;
    var param_21:int;
    var param_22:int;
    var param_23:int;
    var param_24:BArray800.t;
    var result_12:int;
    var result_13:int;
    var result_14:BArray800.t;
    var b_result:BArray800.t;
    var b_result_0:BArray800.t;
    var b_result_1:BArray800.t;
    var b_result_2:BArray800.t;
    var b_result_3:BArray800.t;
    var b_result_4:BArray800.t;
    var b_result_5:BArray800.t;
    var b_result_6:BArray800.t;
    var trace___absorb_bcast_imem_avx2x4:trace;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    param_0 <- witness;
    param_5 <- witness;
    param_7 <- witness;
    param_12 <- witness;
    param_13 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_24 <- witness;
    result <- witness;
    result_2 <- witness;
    result_3 <- witness;
    result_6 <- witness;
    result_7 <- witness;
    result_10 <- witness;
    result_11 <- witness;
    result_14 <- witness;
    trace___absorb_bcast_imem_avx2x4 <- [];
    trace___absorb_bcast_imem_avx2x4 <-
    (trace___absorb_bcast_imem_avx2x4 ++
    [(Assert,
     (((0 <= buf) /\ (buf <= 18446744073709551615)) /\
     ((((((((0 <= lEN) /\ (0 <= aT)) /\ (aT < rATE8)) /\
         (((aT + lEN) + ((tRAILB <> 0) ? 1 : 0)) < 200)) /\
        (0 < rATE8)) /\
       (rATE8 < 200)) /\
      (is_valid ptr_modulus Glob.mem_v buf lEN)) /\
     (is_init b_st 0 800))))]);
    trace___absorb_bcast_imem_avx2x4 <-
    (trace___absorb_bcast_imem_avx2x4 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___absorb_bcast_imem_avx2x4 <-
    (trace___absorb_bcast_imem_avx2x4 ++
    [(Assert, ((0 <= buf) /\ (buf <= 18446744073709551615)))]);
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      param_5 <- st;
      param_4 <- aT;
      param_3 <- buf;
      param_2 <- lEN;
      param_1 <- tRAILB;
      (result_2, b_result_0, result_1, result_0, tmp__trace) <@ __addstate_bcast_imem_avx2x4 (
      param_5, (BArray800.init_arr (W8.of_int 255) 800), param_4, param_3,
      param_2, param_1);
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++
      [(Assert,
       (((0 <= param_2) /\ (param_2 <= 18446744073709551615)) /\
       (((0 <= (param_3 + param_2)) /\
        ((param_3 + param_2) <= 18446744073709551615)) /\
       (((is_init b_result_0 0 800) /\
        (result_1 = ((param_4 + param_2) + ((param_1 <> 0) ? 1 : 0)))) /\
       (result_0 = (param_3 + param_2))))))]);
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      st <- result_2;
      aT <- result_1;
      buf <- result_0;
      if ((tRAILB <> 0)) {
        param_0 <- st;
        param <- rATE8;
        (result, b_result, tmp__trace) <@ __addratebit_avx2x4 (param_0,
        (BArray800.init_arr (W8.of_int 255) 800), param);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, (is_init b_result 0 800))]);
        st <- result;
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        param_24 <- st;
        param_23 <- aT;
        param_22 <- buf;
        param_21 <- (rATE8 - aT);
        param_20 <- 0;
        (result_14, b_result_6, result_13, result_12, tmp__trace) <@ 
        __addstate_bcast_imem_avx2x4 (param_24,
        (BArray800.init_arr (W8.of_int 255) 800), param_23, param_22,
        param_21, param_20);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert,
         (((0 <= param_21) /\ (param_21 <= 18446744073709551615)) /\
         (((0 <= (param_22 + param_21)) /\
          ((param_22 + param_21) <= 18446744073709551615)) /\
         (((is_init b_result_6 0 800) /\
          (result_13 = ((param_23 + param_21) + ((param_20 <> 0) ? 1 : 0)))) /\
         (result_12 = (param_22 + param_21))))))]);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= result_12) /\ (result_12 <= 18446744073709551615)))]);
        st <- result_14;
        buf <- result_12;
        lEN <- (lEN - (rATE8 - aT));
        param_19 <- st;
        (result_11, b_result_5, tmp__trace) <@ _keccakf1600_avx2x4 (param_19,
        (BArray800.init_arr (W8.of_int 255) 800));
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, (is_init b_result_5 0 800))]);
        st <- result_11;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- 0;
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_18 <- st;
        param_17 <- 0;
        param_16 <- buf;
        param_15 <- rATE8;
        param_14 <- 0;
        (result_10, b_result_4, result_9, result_8, tmp__trace) <@ __addstate_bcast_imem_avx2x4 (
        param_18, (BArray800.init_arr (W8.of_int 255) 800), param_17,
        param_16, param_15, param_14);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert,
         (((0 <= param_15) /\ (param_15 <= 18446744073709551615)) /\
         (((0 <= (param_16 + param_15)) /\
          ((param_16 + param_15) <= 18446744073709551615)) /\
         (((is_init b_result_4 0 800) /\
          (result_9 = ((param_17 + param_15) + ((param_14 <> 0) ? 1 : 0)))) /\
         (result_8 = (param_16 + param_15))))))]);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= result_8) /\ (result_8 <= 18446744073709551615)))]);
        st <- result_10;
        buf <- result_8;
        param_13 <- st;
        (result_7, b_result_3, tmp__trace) <@ _keccakf1600_avx2x4 (param_13,
        (BArray800.init_arr (W8.of_int 255) 800));
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, (is_init b_result_3 0 800))]);
        st <- result_7;
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
      lEN <- (aLL %% rATE8);
      param_12 <- st;
      param_11 <- 0;
      param_10 <- buf;
      param_9 <- lEN;
      param_8 <- tRAILB;
      (result_6, b_result_2, result_5, result_4, tmp__trace) <@ __addstate_bcast_imem_avx2x4 (
      param_12, (BArray800.init_arr (W8.of_int 255) 800), param_11, param_10,
      param_9, param_8);
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++
      [(Assert,
       (((0 <= param_9) /\ (param_9 <= 18446744073709551615)) /\
       (((0 <= (param_10 + param_9)) /\
        ((param_10 + param_9) <= 18446744073709551615)) /\
       (((is_init b_result_2 0 800) /\
        (result_5 = ((param_11 + param_9) + ((param_8 <> 0) ? 1 : 0)))) /\
       (result_4 = (param_10 + param_9))))))]);
      trace___absorb_bcast_imem_avx2x4 <-
      (trace___absorb_bcast_imem_avx2x4 ++
      [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
      st <- result_6;
      aT <- result_5;
      buf <- result_4;
      if ((tRAILB <> 0)) {
        param_7 <- st;
        param_6 <- rATE8;
        (result_3, b_result_1, tmp__trace) <@ __addratebit_avx2x4 (param_7,
        (BArray800.init_arr (W8.of_int 255) 800), param_6);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++ tmp__trace);
        trace___absorb_bcast_imem_avx2x4 <-
        (trace___absorb_bcast_imem_avx2x4 ++
        [(Assert, (is_init b_result_1 0 800))]);
        st <- result_3;
      } else {
        
      }
    }
    b_st <- (BArray800.init_arr (W8.of_int 255) 800);
    return (st, b_st, aT, buf, trace___absorb_bcast_imem_avx2x4);
  }
  proc __addstate_imem_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                               buf0:int, buf1:int, buf2:int, buf3:int,
                               lEN:int, tRAILB:int) : BArray800.t *
                                                      BArray800.t * int *
                                                      int * int * int * int *
                                                      trace = {
    var aLL:int;
    var lO:int;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var t256_0:W256.t;
    var t256_1:W256.t;
    var t256_2:W256.t;
    var t256_3:W256.t;
    var at:int;
    var param:int;
    var param_0:int;
    var param_1:int;
    var result:W64.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var result_3:W64.t;
    var result_4:int;
    var result_5:int;
    var result_6:int;
    var param_5:int;
    var param_6:int;
    var param_7:int;
    var result_7:W64.t;
    var result_8:int;
    var result_9:int;
    var result_10:int;
    var param_8:int;
    var param_9:int;
    var param_10:int;
    var result_11:W64.t;
    var result_12:int;
    var result_13:int;
    var result_14:int;
    var param_11:W256.t;
    var param_12:W256.t;
    var param_13:W256.t;
    var param_14:W256.t;
    var result_15:W256.t;
    var result_16:W256.t;
    var result_17:W256.t;
    var result_18:W256.t;
    var param_15:int;
    var param_16:int;
    var param_17:int;
    var result_19:W64.t;
    var result_20:int;
    var result_21:int;
    var result_22:int;
    var param_18:int;
    var param_19:int;
    var param_20:int;
    var result_23:W64.t;
    var result_24:int;
    var result_25:int;
    var result_26:int;
    var param_21:int;
    var param_22:int;
    var param_23:int;
    var result_27:W64.t;
    var result_28:int;
    var result_29:int;
    var result_30:int;
    var param_24:int;
    var param_25:int;
    var param_26:int;
    var result_31:W64.t;
    var result_32:int;
    var result_33:int;
    var result_34:int;
    var param_27:int;
    var param_28:int;
    var param_29:int;
    var result_35:W64.t;
    var result_36:int;
    var result_37:int;
    var result_38:int;
    var param_30:int;
    var param_31:int;
    var param_32:int;
    var result_39:W64.t;
    var result_40:int;
    var result_41:int;
    var result_42:int;
    var param_33:int;
    var param_34:int;
    var param_35:int;
    var result_43:W64.t;
    var result_44:int;
    var result_45:int;
    var result_46:int;
    var param_36:int;
    var param_37:int;
    var param_38:int;
    var result_47:W64.t;
    var result_48:int;
    var result_49:int;
    var result_50:int;
    var trace___addstate_imem_avx2x4:trace;
    trace___addstate_imem_avx2x4 <- [];
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert,
     (((0 <= buf0) /\ (buf0 <= 18446744073709551615)) /\
     (((0 <= buf1) /\ (buf1 <= 18446744073709551615)) /\
     (((0 <= buf2) /\ (buf2 <= 18446744073709551615)) /\
     (((0 <= buf3) /\ (buf3 <= 18446744073709551615)) /\
     (((((((((0 <= lEN) /\ (0 <= aT)) /\ (aT < 200)) /\
          (((aT + lEN) + ((tRAILB <> 0) ? 1 : 0)) < 200)) /\
         (is_valid ptr_modulus Glob.mem_v buf0 lEN)) /\
        (is_valid ptr_modulus Glob.mem_v buf1 lEN)) /\
       (is_valid ptr_modulus Glob.mem_v buf2 lEN)) /\
      (is_valid ptr_modulus Glob.mem_v buf3 lEN)) /\
     (is_init b_st 0 800)))))))]);
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
    aLL <- (aT + lEN);
    lO <- (aT %% 8);
    trace___addstate_imem_avx2x4 <-
    (trace___addstate_imem_avx2x4 ++
    [(Assert,
     ((0 <= (4 * (aT %/ 8))) /\ ((4 * (aT %/ 8)) <= 18446744073709551615)))]);
    at <- (4 * (aT %/ 8));
    if ((0 < lO)) {
      if (((lO + lEN) < 8)) {
        if ((tRAILB <> 0)) {
          aLL <- (aLL + 1);
        } else {
          
        }
        param_26 <- buf0;
        param_25 <- lEN;
        param_24 <- tRAILB;
        (result_34, result_33, result_32, result_31, tmp__trace) <@ __mread_subu64 (
        param_26, param_25, param_24);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++ tmp__trace);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_25 < 8) ? param_25 : 8)) ? ((param_25 < 8) ? 
                                                    param_25 : 8) : 0)) /\
          (((0 < ((param_25 < 8) ? param_25 : 8)) ? ((param_25 < 8) ? 
                                                    param_25 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_26 +
           ((0 < ((param_25 < 8) ? param_25 : 8)) ? ((param_25 < 8) ? 
                                                    param_25 : 8) : 0))) /\
          ((param_26 +
           ((0 < ((param_25 < 8) ? param_25 : 8)) ? ((param_25 < 8) ? 
                                                    param_25 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_34 =
           (param_26 +
           ((0 < ((param_25 < 8) ? param_25 : 8)) ? ((param_25 < 8) ? 
                                                    param_25 : 8) : 0))) /\
          (result_33 =
          (param_25 -
          ((0 < ((param_25 < 8) ? param_25 : 8)) ? ((param_25 < 8) ? 
                                                   param_25 : 8) : 0)))) /\
         (result_32 = ((8 <= param_25) ? param_24 : 0))))))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= result_34) /\ (result_34 <= 18446744073709551615)))]);
        buf0 <- result_34;
        t0 <- result_31;
        param_23 <- buf1;
        param_22 <- lEN;
        param_21 <- tRAILB;
        (result_30, result_29, result_28, result_27, tmp__trace) <@ __mread_subu64 (
        param_23, param_22, param_21);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++ tmp__trace);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_22 < 8) ? param_22 : 8)) ? ((param_22 < 8) ? 
                                                    param_22 : 8) : 0)) /\
          (((0 < ((param_22 < 8) ? param_22 : 8)) ? ((param_22 < 8) ? 
                                                    param_22 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_23 +
           ((0 < ((param_22 < 8) ? param_22 : 8)) ? ((param_22 < 8) ? 
                                                    param_22 : 8) : 0))) /\
          ((param_23 +
           ((0 < ((param_22 < 8) ? param_22 : 8)) ? ((param_22 < 8) ? 
                                                    param_22 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_30 =
           (param_23 +
           ((0 < ((param_22 < 8) ? param_22 : 8)) ? ((param_22 < 8) ? 
                                                    param_22 : 8) : 0))) /\
          (result_29 =
          (param_22 -
          ((0 < ((param_22 < 8) ? param_22 : 8)) ? ((param_22 < 8) ? 
                                                   param_22 : 8) : 0)))) /\
         (result_28 = ((8 <= param_22) ? param_21 : 0))))))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= result_30) /\ (result_30 <= 18446744073709551615)))]);
        buf1 <- result_30;
        t1 <- result_27;
        param_20 <- buf2;
        param_19 <- lEN;
        param_18 <- tRAILB;
        (result_26, result_25, result_24, result_23, tmp__trace) <@ __mread_subu64 (
        param_20, param_19, param_18);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++ tmp__trace);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_19 < 8) ? param_19 : 8)) ? ((param_19 < 8) ? 
                                                    param_19 : 8) : 0)) /\
          (((0 < ((param_19 < 8) ? param_19 : 8)) ? ((param_19 < 8) ? 
                                                    param_19 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_20 +
           ((0 < ((param_19 < 8) ? param_19 : 8)) ? ((param_19 < 8) ? 
                                                    param_19 : 8) : 0))) /\
          ((param_20 +
           ((0 < ((param_19 < 8) ? param_19 : 8)) ? ((param_19 < 8) ? 
                                                    param_19 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_26 =
           (param_20 +
           ((0 < ((param_19 < 8) ? param_19 : 8)) ? ((param_19 < 8) ? 
                                                    param_19 : 8) : 0))) /\
          (result_25 =
          (param_19 -
          ((0 < ((param_19 < 8) ? param_19 : 8)) ? ((param_19 < 8) ? 
                                                   param_19 : 8) : 0)))) /\
         (result_24 = ((8 <= param_19) ? param_18 : 0))))))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= result_26) /\ (result_26 <= 18446744073709551615)))]);
        buf2 <- result_26;
        t2 <- result_23;
        param_17 <- buf3;
        param_16 <- lEN;
        param_15 <- tRAILB;
        (result_22, result_21, result_20, result_19, tmp__trace) <@ __mread_subu64 (
        param_17, param_16, param_15);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++ tmp__trace);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         (((0 <=
           ((0 < ((param_16 < 8) ? param_16 : 8)) ? ((param_16 < 8) ? 
                                                    param_16 : 8) : 0)) /\
          (((0 < ((param_16 < 8) ? param_16 : 8)) ? ((param_16 < 8) ? 
                                                    param_16 : 8) : 0) <=
          18446744073709551615)) /\
         (((0 <=
           (param_17 +
           ((0 < ((param_16 < 8) ? param_16 : 8)) ? ((param_16 < 8) ? 
                                                    param_16 : 8) : 0))) /\
          ((param_17 +
           ((0 < ((param_16 < 8) ? param_16 : 8)) ? ((param_16 < 8) ? 
                                                    param_16 : 8) : 0)) <=
          18446744073709551615)) /\
         (((result_22 =
           (param_17 +
           ((0 < ((param_16 < 8) ? param_16 : 8)) ? ((param_16 < 8) ? 
                                                    param_16 : 8) : 0))) /\
          (result_21 =
          (param_16 -
          ((0 < ((param_16 < 8) ? param_16 : 8)) ? ((param_16 < 8) ? 
                                                   param_16 : 8) : 0)))) /\
         (result_20 = ((8 <= param_16) ? param_15 : 0))))))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= result_22) /\ (result_22 <= 18446744073709551615)))]);
        buf3 <- result_22;
        t3 <- result_19;
        t0 <- (t0 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
        t0 <- (t0 `^` (BArray800.get64 st at));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st at t0);
        t1 <- (t1 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
        t1 <- (t1 `^` (BArray800.get64 st (at + 1)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 1) t1);
        t2 <- (t2 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
        t2 <- (t2 `^` (BArray800.get64 st (at + 2)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 2) t2);
        t3 <- (t3 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
        t3 <- (t3 `^` (BArray800.get64 st (at + 3)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 3) t3);
        aT <- 0;
        lEN <- 0;
        tRAILB <- 0;
      } else {
        if ((8 <= lEN)) {
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf0 8))]);
          t0 <- (loadW64 Glob.mem buf0);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= (8 - lO)) /\ ((8 - lO) <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= (buf0 + (8 - lO))) /\
           ((buf0 + (8 - lO)) <= 18446744073709551615)))]);
          buf0 <- (buf0 + (8 - lO));
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf1 8))]);
          t1 <- (loadW64 Glob.mem buf1);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= (8 - lO)) /\ ((8 - lO) <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= (buf1 + (8 - lO))) /\
           ((buf1 + (8 - lO)) <= 18446744073709551615)))]);
          buf1 <- (buf1 + (8 - lO));
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf2 8))]);
          t2 <- (loadW64 Glob.mem buf2);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= (8 - lO)) /\ ((8 - lO) <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= (buf2 + (8 - lO))) /\
           ((buf2 + (8 - lO)) <= 18446744073709551615)))]);
          buf2 <- (buf2 + (8 - lO));
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, (is_valid ptr_modulus Glob.mem_v buf3 8))]);
          t3 <- (loadW64 Glob.mem buf3);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert, ((0 <= (8 - lO)) /\ ((8 - lO) <= 18446744073709551615)))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= (buf3 + (8 - lO))) /\
           ((buf3 + (8 - lO)) <= 18446744073709551615)))]);
          buf3 <- (buf3 + (8 - lO));
        } else {
          param_38 <- buf0;
          param_37 <- (8 - lO);
          param_36 <- tRAILB;
          (result_50, result_49, result_48, result_47, tmp__trace) <@ 
          __mread_subu64 (param_38, param_37, param_36);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++ tmp__trace);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_37 < 8) ? param_37 : 8)) ? ((param_37 < 8) ? 
                                                      param_37 : 8) : 0)) /\
            (((0 < ((param_37 < 8) ? param_37 : 8)) ? ((param_37 < 8) ? 
                                                      param_37 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_38 +
             ((0 < ((param_37 < 8) ? param_37 : 8)) ? ((param_37 < 8) ? 
                                                      param_37 : 8) : 0))) /\
            ((param_38 +
             ((0 < ((param_37 < 8) ? param_37 : 8)) ? ((param_37 < 8) ? 
                                                      param_37 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_50 =
             (param_38 +
             ((0 < ((param_37 < 8) ? param_37 : 8)) ? ((param_37 < 8) ? 
                                                      param_37 : 8) : 0))) /\
            (result_49 =
            (param_37 -
            ((0 < ((param_37 < 8) ? param_37 : 8)) ? ((param_37 < 8) ? 
                                                     param_37 : 8) : 0)))) /\
           (result_48 = ((8 <= param_37) ? param_36 : 0))))))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= result_50) /\ (result_50 <= 18446744073709551615)))]);
          buf0 <- result_50;
          t0 <- result_47;
          param_35 <- buf1;
          param_34 <- (8 - lO);
          param_33 <- tRAILB;
          (result_46, result_45, result_44, result_43, tmp__trace) <@ 
          __mread_subu64 (param_35, param_34, param_33);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++ tmp__trace);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_34 < 8) ? param_34 : 8)) ? ((param_34 < 8) ? 
                                                      param_34 : 8) : 0)) /\
            (((0 < ((param_34 < 8) ? param_34 : 8)) ? ((param_34 < 8) ? 
                                                      param_34 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_35 +
             ((0 < ((param_34 < 8) ? param_34 : 8)) ? ((param_34 < 8) ? 
                                                      param_34 : 8) : 0))) /\
            ((param_35 +
             ((0 < ((param_34 < 8) ? param_34 : 8)) ? ((param_34 < 8) ? 
                                                      param_34 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_46 =
             (param_35 +
             ((0 < ((param_34 < 8) ? param_34 : 8)) ? ((param_34 < 8) ? 
                                                      param_34 : 8) : 0))) /\
            (result_45 =
            (param_34 -
            ((0 < ((param_34 < 8) ? param_34 : 8)) ? ((param_34 < 8) ? 
                                                     param_34 : 8) : 0)))) /\
           (result_44 = ((8 <= param_34) ? param_33 : 0))))))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= result_46) /\ (result_46 <= 18446744073709551615)))]);
          buf1 <- result_46;
          t1 <- result_43;
          param_32 <- buf2;
          param_31 <- (8 - lO);
          param_30 <- tRAILB;
          (result_42, result_41, result_40, result_39, tmp__trace) <@ 
          __mread_subu64 (param_32, param_31, param_30);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++ tmp__trace);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_31 < 8) ? param_31 : 8)) ? ((param_31 < 8) ? 
                                                      param_31 : 8) : 0)) /\
            (((0 < ((param_31 < 8) ? param_31 : 8)) ? ((param_31 < 8) ? 
                                                      param_31 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_32 +
             ((0 < ((param_31 < 8) ? param_31 : 8)) ? ((param_31 < 8) ? 
                                                      param_31 : 8) : 0))) /\
            ((param_32 +
             ((0 < ((param_31 < 8) ? param_31 : 8)) ? ((param_31 < 8) ? 
                                                      param_31 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_42 =
             (param_32 +
             ((0 < ((param_31 < 8) ? param_31 : 8)) ? ((param_31 < 8) ? 
                                                      param_31 : 8) : 0))) /\
            (result_41 =
            (param_31 -
            ((0 < ((param_31 < 8) ? param_31 : 8)) ? ((param_31 < 8) ? 
                                                     param_31 : 8) : 0)))) /\
           (result_40 = ((8 <= param_31) ? param_30 : 0))))))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= result_42) /\ (result_42 <= 18446744073709551615)))]);
          buf2 <- result_42;
          t2 <- result_39;
          param_29 <- buf3;
          param_28 <- (8 - lO);
          param_27 <- tRAILB;
          (result_38, result_37, result_36, result_35, tmp__trace) <@ 
          __mread_subu64 (param_29, param_28, param_27);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++ tmp__trace);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           (((0 <=
             ((0 < ((param_28 < 8) ? param_28 : 8)) ? ((param_28 < 8) ? 
                                                      param_28 : 8) : 0)) /\
            (((0 < ((param_28 < 8) ? param_28 : 8)) ? ((param_28 < 8) ? 
                                                      param_28 : 8) : 0) <=
            18446744073709551615)) /\
           (((0 <=
             (param_29 +
             ((0 < ((param_28 < 8) ? param_28 : 8)) ? ((param_28 < 8) ? 
                                                      param_28 : 8) : 0))) /\
            ((param_29 +
             ((0 < ((param_28 < 8) ? param_28 : 8)) ? ((param_28 < 8) ? 
                                                      param_28 : 8) : 0)) <=
            18446744073709551615)) /\
           (((result_38 =
             (param_29 +
             ((0 < ((param_28 < 8) ? param_28 : 8)) ? ((param_28 < 8) ? 
                                                      param_28 : 8) : 0))) /\
            (result_37 =
            (param_28 -
            ((0 < ((param_28 < 8) ? param_28 : 8)) ? ((param_28 < 8) ? 
                                                     param_28 : 8) : 0)))) /\
           (result_36 = ((8 <= param_28) ? param_27 : 0))))))]);
          trace___addstate_imem_avx2x4 <-
          (trace___addstate_imem_avx2x4 ++
          [(Assert,
           ((0 <= result_38) /\ (result_38 <= 18446744073709551615)))]);
          buf3 <- result_38;
          t3 <- result_35;
        }
        lEN <- (lEN - (8 - lO));
        aT <- (aT + (8 - lO));
        t0 <- (t0 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
        t0 <- (t0 `^` (BArray800.get64 st at));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st at t0);
        t1 <- (t1 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
        t1 <- (t1 `^` (BArray800.get64 st (at + 1)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 1) t1);
        t2 <- (t2 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
        t2 <- (t2 `^` (BArray800.get64 st (at + 2)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 2) t2);
        t3 <- (t3 `<<` (W8.of_int (8 * lO)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
        t3 <- (t3 `^` (BArray800.get64 st (at + 3)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 3) t3);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 4)) /\ ((at + 4) <= 18446744073709551615)))]);
        at <- (at + 4);
      }
    } else {
      
    }
    if ((8 <= lEN)) {
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * (aT %/ 8)) + (16 * (lEN %/ 32)))) /\
       (((4 * (aT %/ 8)) + (16 * (lEN %/ 32))) <= 18446744073709551615)))]);
      while ((at < ((4 * (aT %/ 8)) + (16 * (lEN %/ 32))))) {
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf0 32))]);
        t256_0 <- (loadW256 Glob.mem buf0);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf0 + 32)) /\ ((buf0 + 32) <= 18446744073709551615)))]);
        buf0 <- (buf0 + 32);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf1 32))]);
        t256_1 <- (loadW256 Glob.mem buf1);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf1 + 32)) /\ ((buf1 + 32) <= 18446744073709551615)))]);
        buf1 <- (buf1 + 32);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf2 32))]);
        t256_2 <- (loadW256 Glob.mem buf2);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf2 + 32)) /\ ((buf2 + 32) <= 18446744073709551615)))]);
        buf2 <- (buf2 + 32);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf3 32))]);
        t256_3 <- (loadW256 Glob.mem buf3);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf3 + 32)) /\ ((buf3 + 32) <= 18446744073709551615)))]);
        buf3 <- (buf3 + 32);
        param_14 <- t256_0;
        param_13 <- t256_1;
        param_12 <- t256_2;
        param_11 <- t256_3;
        (result_18, result_17, result_16, result_15, tmp__trace) <@ __4u64x4_u256x4 (
        param_14, param_13, param_12, param_11);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++ tmp__trace);
        t256_0 <- result_18;
        t256_1 <- result_17;
        t256_2 <- result_16;
        t256_3 <- result_15;
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (8 * at)) /\ (((8 * at) + 32) <= 800)))]);
        st <- (BArray800.set256d st (8 * at) t256_0);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((8 * at) + 32)) /\
         (((8 * at) + 32) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((8 * at) + 32)) /\ ((((8 * at) + 32) + 32) <= 800)))]);
        st <- (BArray800.set256d st ((8 * at) + 32) t256_1);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((8 * at) + 64)) /\
         (((8 * at) + 64) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((8 * at) + 64)) /\ ((((8 * at) + 64) + 32) <= 800)))]);
        st <- (BArray800.set256d st ((8 * at) + 64) t256_2);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (8 * at)) /\ ((8 * at) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((8 * at) + 96)) /\
         (((8 * at) + 96) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((8 * at) + 96)) /\ ((((8 * at) + 96) + 32) <= 800)))]);
        st <- (BArray800.set256d st ((8 * at) + 96) t256_3);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 32)) /\ ((at + 32) <= 18446744073709551615)))]);
        at <- (at + 16);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((4 * (aT %/ 8)) + (16 * (lEN %/ 32)))) /\
         (((4 * (aT %/ 8)) + (16 * (lEN %/ 32))) <= 18446744073709551615)))]);
      }
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * (aT %/ 8)) + (4 * (lEN %/ 8)))) /\
       (((4 * (aT %/ 8)) + (4 * (lEN %/ 8))) <= 18446744073709551615)))]);
      while ((at < ((4 * (aT %/ 8)) + (4 * (lEN %/ 8))))) {
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf0 8))]);
        t0 <- (loadW64 Glob.mem buf0);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf0 + 8)) /\ ((buf0 + 8) <= 18446744073709551615)))]);
        buf0 <- (buf0 + 8);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
        t0 <- (t0 `^` (BArray800.get64 st at));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st at t0);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf1 8))]);
        t1 <- (loadW64 Glob.mem buf1);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf1 + 8)) /\ ((buf1 + 8) <= 18446744073709551615)))]);
        buf1 <- (buf1 + 8);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
        t1 <- (t1 `^` (BArray800.get64 st (at + 1)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 1) t1);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf2 8))]);
        t2 <- (loadW64 Glob.mem buf2);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf2 + 8)) /\ ((buf2 + 8) <= 18446744073709551615)))]);
        buf2 <- (buf2 + 8);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
        t2 <- (t2 `^` (BArray800.get64 st (at + 2)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 2) t2);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, (is_valid ptr_modulus Glob.mem_v buf3 8))]);
        t3 <- (loadW64 Glob.mem buf3);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= (buf3 + 8)) /\ ((buf3 + 8) <= 18446744073709551615)))]);
        buf3 <- (buf3 + 8);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
        t3 <- (t3 `^` (BArray800.get64 st (at + 3)));
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
        st <- (BArray800.set64 st (at + 3) t3);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert, ((0 <= (at + 4)) /\ ((at + 4) <= 18446744073709551615)))]);
        at <- (at + 4);
        trace___addstate_imem_avx2x4 <-
        (trace___addstate_imem_avx2x4 ++
        [(Assert,
         ((0 <= ((4 * (aT %/ 8)) + (4 * (lEN %/ 8)))) /\
         (((4 * (aT %/ 8)) + (4 * (lEN %/ 8))) <= 18446744073709551615)))]);
      }
      lEN <- ((aT + lEN) %% 8);
    } else {
      
    }
    lO <- ((aT + lEN) %% 8);
    if (((0 < lO) \/ (tRAILB <> 0))) {
      param_10 <- buf0;
      param_9 <- lO;
      param_8 <- tRAILB;
      (result_14, result_13, result_12, result_11, tmp__trace) <@ __mread_subu64 (
      param_10, param_9, param_8);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++ tmp__trace);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)) /\
        (((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_10 +
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0))) /\
        ((param_10 +
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_14 =
         (param_10 +
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0))) /\
        (result_13 =
        (param_9 -
        ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)))) /\
       (result_12 = ((8 <= param_9) ? param_8 : 0))))))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_14) /\ (result_14 <= 18446744073709551615)))]);
      buf0 <- result_14;
      t0 <- result_11;
      param_7 <- buf1;
      param_6 <- lO;
      param_5 <- tRAILB;
      (result_10, result_9, result_8, result_7, tmp__trace) <@ __mread_subu64 (
      param_7, param_6, param_5);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++ tmp__trace);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)) /\
        (((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_7 +
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0))) /\
        ((param_7 +
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_10 =
         (param_7 +
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0))) /\
        (result_9 =
        (param_6 -
        ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)))) /\
       (result_8 = ((8 <= param_6) ? param_5 : 0))))))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
      buf1 <- result_10;
      t1 <- result_7;
      param_4 <- buf2;
      param_3 <- lO;
      param_2 <- tRAILB;
      (result_6, result_5, result_4, result_3, tmp__trace) <@ __mread_subu64 (
      param_4, param_3, param_2);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++ tmp__trace);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) /\
        (((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_4 +
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
        ((param_4 +
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_6 =
         (param_4 +
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
        (result_5 =
        (param_3 -
        ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)))) /\
       (result_4 = ((8 <= param_3) ? param_2 : 0))))))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
      buf2 <- result_6;
      t2 <- result_3;
      param_1 <- buf3;
      param_0 <- lO;
      param <- tRAILB;
      (result_2, result_1, result_0, result, tmp__trace) <@ __mread_subu64 (
      param_1, param_0, param);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++ tmp__trace);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) /\
        (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        ((param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) <=
        18446744073709551615)) /\
       (((result_2 =
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        (result_1 =
        (param_0 -
        ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))) /\
       (result_0 = ((8 <= param_0) ? param : 0))))))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      buf3 <- result_2;
      t3 <- result;
      if ((tRAILB <> 0)) {
        aLL <- (aLL + 1);
      } else {
        
      }
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
      t0 <- (t0 `^` (BArray800.get64 st at));
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= at) /\ (at <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at * 8)) /\ (((at * 8) + 8) <= 800)))]);
      st <- (BArray800.set64 st at t0);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
      t1 <- (t1 `^` (BArray800.get64 st (at + 1)));
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at + 1)) /\ ((at + 1) <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((at + 1) * 8)) /\ ((((at + 1) * 8) + 8) <= 800)))]);
      st <- (BArray800.set64 st (at + 1) t1);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
      t2 <- (t2 `^` (BArray800.get64 st (at + 2)));
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at + 2)) /\ ((at + 2) <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((at + 2) * 8)) /\ ((((at + 2) * 8) + 8) <= 800)))]);
      st <- (BArray800.set64 st (at + 2) t2);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
      t3 <- (t3 `^` (BArray800.get64 st (at + 3)));
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= (at + 3)) /\ ((at + 3) <= 18446744073709551615)))]);
      trace___addstate_imem_avx2x4 <-
      (trace___addstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((at + 3) * 8)) /\ ((((at + 3) * 8) + 8) <= 800)))]);
      st <- (BArray800.set64 st (at + 3) t3);
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255) 800);
    return (st, b_st, aLL, buf0, buf1, buf2, buf3,
           trace___addstate_imem_avx2x4);
  }
  proc __absorb_imem_avx2x4 (st:BArray800.t, b_st:BArray800.t, aT:int,
                             buf0:int, buf1:int, buf2:int, buf3:int, lEN:int,
                             rATE8:int, tRAILB:int) : BArray800.t *
                                                      BArray800.t * int *
                                                      int * int * int * int *
                                                      trace = {
    var aLL:int;
    var iTERS:int;
    var i:int;
    var param:int;
    var param_0:BArray800.t;
    var result:BArray800.t;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var param_5:int;
    var param_6:int;
    var param_7:int;
    var param_8:BArray800.t;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var result_3:int;
    var result_4:int;
    var result_5:BArray800.t;
    var param_9:int;
    var param_10:BArray800.t;
    var result_6:BArray800.t;
    var param_11:int;
    var param_12:int;
    var param_13:int;
    var param_14:int;
    var param_15:int;
    var param_16:int;
    var param_17:int;
    var param_18:BArray800.t;
    var result_7:int;
    var result_8:int;
    var result_9:int;
    var result_10:int;
    var result_11:int;
    var result_12:BArray800.t;
    var param_19:BArray800.t;
    var result_13:BArray800.t;
    var param_20:int;
    var param_21:int;
    var param_22:int;
    var param_23:int;
    var param_24:int;
    var param_25:int;
    var param_26:int;
    var param_27:BArray800.t;
    var result_14:int;
    var result_15:int;
    var result_16:int;
    var result_17:int;
    var result_18:int;
    var result_19:BArray800.t;
    var param_28:BArray800.t;
    var result_20:BArray800.t;
    var param_29:int;
    var param_30:int;
    var param_31:int;
    var param_32:int;
    var param_33:int;
    var param_34:int;
    var param_35:int;
    var param_36:BArray800.t;
    var result_21:int;
    var result_22:int;
    var result_23:int;
    var result_24:int;
    var result_25:int;
    var result_26:BArray800.t;
    var b_result:BArray800.t;
    var b_result_0:BArray800.t;
    var b_result_1:BArray800.t;
    var b_result_2:BArray800.t;
    var b_result_3:BArray800.t;
    var b_result_4:BArray800.t;
    var b_result_5:BArray800.t;
    var b_result_6:BArray800.t;
    var trace___absorb_imem_avx2x4:trace;
    b_result <- witness;
    b_result_0 <- witness;
    b_result_1 <- witness;
    b_result_2 <- witness;
    b_result_3 <- witness;
    b_result_4 <- witness;
    b_result_5 <- witness;
    b_result_6 <- witness;
    param_0 <- witness;
    param_8 <- witness;
    param_10 <- witness;
    param_18 <- witness;
    param_19 <- witness;
    param_27 <- witness;
    param_28 <- witness;
    param_36 <- witness;
    result <- witness;
    result_5 <- witness;
    result_6 <- witness;
    result_12 <- witness;
    result_13 <- witness;
    result_19 <- witness;
    result_20 <- witness;
    result_26 <- witness;
    trace___absorb_imem_avx2x4 <- [];
    trace___absorb_imem_avx2x4 <-
    (trace___absorb_imem_avx2x4 ++
    [(Assert,
     (((0 <= buf0) /\ (buf0 <= 18446744073709551615)) /\
     (((0 <= buf1) /\ (buf1 <= 18446744073709551615)) /\
     (((0 <= buf2) /\ (buf2 <= 18446744073709551615)) /\
     (((0 <= buf3) /\ (buf3 <= 18446744073709551615)) /\
     (((((((((((0 <= lEN) /\ (0 <= aT)) /\ (aT < rATE8)) /\ (0 < rATE8)) /\
           (rATE8 < 200)) /\
          (((aT + lEN) + ((tRAILB <> 0) ? 1 : 0)) < 200)) /\
         (is_valid ptr_modulus Glob.mem_v buf0 lEN)) /\
        (is_valid ptr_modulus Glob.mem_v buf1 lEN)) /\
       (is_valid ptr_modulus Glob.mem_v buf2 lEN)) /\
      (is_valid ptr_modulus Glob.mem_v buf3 lEN)) /\
     (is_init b_st 0 800)))))))]);
    trace___absorb_imem_avx2x4 <-
    (trace___absorb_imem_avx2x4 ++
    [(Assert, ((0 <= tRAILB) /\ (tRAILB < 256)))]);
    trace___absorb_imem_avx2x4 <-
    (trace___absorb_imem_avx2x4 ++
    [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
    trace___absorb_imem_avx2x4 <-
    (trace___absorb_imem_avx2x4 ++
    [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
    trace___absorb_imem_avx2x4 <-
    (trace___absorb_imem_avx2x4 ++
    [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
    trace___absorb_imem_avx2x4 <-
    (trace___absorb_imem_avx2x4 ++
    [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
    aLL <- (aT + lEN);
    if (((aT + lEN) < rATE8)) {
      param_8 <- st;
      param_7 <- aT;
      param_6 <- buf0;
      param_5 <- buf1;
      param_4 <- buf2;
      param_3 <- buf3;
      param_2 <- lEN;
      param_1 <- tRAILB;
      (result_5, b_result_0, result_4, result_3, result_2, result_1,
      result_0, tmp__trace) <@ __addstate_imem_avx2x4 (param_8,
      (BArray800.init_arr (W8.of_int 255) 800), param_7, param_6, param_5,
      param_4, param_3, param_2, param_1);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++ tmp__trace);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert,
       (((0 <= param_2) /\ (param_2 <= 18446744073709551615)) /\
       (((0 <= (param_6 + param_2)) /\
        ((param_6 + param_2) <= 18446744073709551615)) /\
       (((0 <= param_2) /\ (param_2 <= 18446744073709551615)) /\
       (((0 <= (param_5 + param_2)) /\
        ((param_5 + param_2) <= 18446744073709551615)) /\
       (((0 <= param_2) /\ (param_2 <= 18446744073709551615)) /\
       (((0 <= (param_4 + param_2)) /\
        ((param_4 + param_2) <= 18446744073709551615)) /\
       (((0 <= param_2) /\ (param_2 <= 18446744073709551615)) /\
       (((0 <= (param_3 + param_2)) /\
        ((param_3 + param_2) <= 18446744073709551615)) /\
       ((((((is_init b_result_0 0 800) /\
           (result_4 = ((param_7 + param_2) + ((param_1 <> 0) ? 1 : 0)))) /\
          (result_3 = (param_6 + param_2))) /\
         (result_2 = (param_5 + param_2))) /\
        (result_1 = (param_4 + param_2))) /\
       (result_0 = (param_3 + param_2))))))))))))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_3) /\ (result_3 <= 18446744073709551615)))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_1) /\ (result_1 <= 18446744073709551615)))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      st <- result_5;
      aT <- result_4;
      buf0 <- result_3;
      buf1 <- result_2;
      buf2 <- result_1;
      buf3 <- result_0;
      if ((tRAILB <> 0)) {
        param_0 <- st;
        param <- rATE8;
        (result, b_result, tmp__trace) <@ __addratebit_avx2x4 (param_0,
        (BArray800.init_arr (W8.of_int 255) 800), param);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ tmp__trace);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ [(Assert, (is_init b_result 0 800))]);
        st <- result;
      } else {
        
      }
    } else {
      if ((aT <> 0)) {
        param_36 <- st;
        param_35 <- aT;
        param_34 <- buf0;
        param_33 <- buf1;
        param_32 <- buf2;
        param_31 <- buf3;
        param_30 <- (rATE8 - aT);
        param_29 <- 0;
        (result_26, b_result_6, result_25, result_24, result_23, result_22,
        result_21, tmp__trace) <@ __addstate_imem_avx2x4 (param_36,
        (BArray800.init_arr (W8.of_int 255) 800), param_35, param_34,
        param_33, param_32, param_31, param_30, param_29);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ tmp__trace);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert,
         (((0 <= param_30) /\ (param_30 <= 18446744073709551615)) /\
         (((0 <= (param_34 + param_30)) /\
          ((param_34 + param_30) <= 18446744073709551615)) /\
         (((0 <= param_30) /\ (param_30 <= 18446744073709551615)) /\
         (((0 <= (param_33 + param_30)) /\
          ((param_33 + param_30) <= 18446744073709551615)) /\
         (((0 <= param_30) /\ (param_30 <= 18446744073709551615)) /\
         (((0 <= (param_32 + param_30)) /\
          ((param_32 + param_30) <= 18446744073709551615)) /\
         (((0 <= param_30) /\ (param_30 <= 18446744073709551615)) /\
         (((0 <= (param_31 + param_30)) /\
          ((param_31 + param_30) <= 18446744073709551615)) /\
         ((((((is_init b_result_6 0 800) /\
             (result_25 =
             ((param_35 + param_30) + ((param_29 <> 0) ? 1 : 0)))) /\
            (result_24 = (param_34 + param_30))) /\
           (result_23 = (param_33 + param_30))) /\
          (result_22 = (param_32 + param_30))) /\
         (result_21 = (param_31 + param_30))))))))))))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_24) /\ (result_24 <= 18446744073709551615)))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_23) /\ (result_23 <= 18446744073709551615)))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_22) /\ (result_22 <= 18446744073709551615)))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_21) /\ (result_21 <= 18446744073709551615)))]);
        st <- result_26;
        buf0 <- result_24;
        buf1 <- result_23;
        buf2 <- result_22;
        buf3 <- result_21;
        lEN <- (lEN - (rATE8 - aT));
        param_28 <- st;
        (result_20, b_result_5, tmp__trace) <@ _keccakf1600_avx2x4 (param_28,
        (BArray800.init_arr (W8.of_int 255) 800));
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ tmp__trace);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, (is_init b_result_5 0 800))]);
        st <- result_20;
      } else {
        
      }
      iTERS <- (lEN %/ rATE8);
      i <- 0;
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      while ((i < iTERS)) {
        param_27 <- st;
        param_26 <- 0;
        param_25 <- buf0;
        param_24 <- buf1;
        param_23 <- buf2;
        param_22 <- buf3;
        param_21 <- rATE8;
        param_20 <- 0;
        (result_19, b_result_4, result_18, result_17, result_16, result_15,
        result_14, tmp__trace) <@ __addstate_imem_avx2x4 (param_27,
        (BArray800.init_arr (W8.of_int 255) 800), param_26, param_25,
        param_24, param_23, param_22, param_21, param_20);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ tmp__trace);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert,
         (((0 <= param_21) /\ (param_21 <= 18446744073709551615)) /\
         (((0 <= (param_25 + param_21)) /\
          ((param_25 + param_21) <= 18446744073709551615)) /\
         (((0 <= param_21) /\ (param_21 <= 18446744073709551615)) /\
         (((0 <= (param_24 + param_21)) /\
          ((param_24 + param_21) <= 18446744073709551615)) /\
         (((0 <= param_21) /\ (param_21 <= 18446744073709551615)) /\
         (((0 <= (param_23 + param_21)) /\
          ((param_23 + param_21) <= 18446744073709551615)) /\
         (((0 <= param_21) /\ (param_21 <= 18446744073709551615)) /\
         (((0 <= (param_22 + param_21)) /\
          ((param_22 + param_21) <= 18446744073709551615)) /\
         ((((((is_init b_result_4 0 800) /\
             (result_18 =
             ((param_26 + param_21) + ((param_20 <> 0) ? 1 : 0)))) /\
            (result_17 = (param_25 + param_21))) /\
           (result_16 = (param_24 + param_21))) /\
          (result_15 = (param_23 + param_21))) /\
         (result_14 = (param_22 + param_21))))))))))))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_17) /\ (result_17 <= 18446744073709551615)))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_16) /\ (result_16 <= 18446744073709551615)))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_15) /\ (result_15 <= 18446744073709551615)))]);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= result_14) /\ (result_14 <= 18446744073709551615)))]);
        st <- result_19;
        buf0 <- result_17;
        buf1 <- result_16;
        buf2 <- result_15;
        buf3 <- result_14;
        param_19 <- st;
        (result_13, b_result_3, tmp__trace) <@ _keccakf1600_avx2x4 (param_19,
        (BArray800.init_arr (W8.of_int 255) 800));
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ tmp__trace);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, (is_init b_result_3 0 800))]);
        st <- result_13;
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
        i <- (i + 1);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
      }
      lEN <- (aLL %% rATE8);
      param_18 <- st;
      param_17 <- 0;
      param_16 <- buf0;
      param_15 <- buf1;
      param_14 <- buf2;
      param_13 <- buf3;
      param_12 <- lEN;
      param_11 <- tRAILB;
      (result_12, b_result_2, result_11, result_10, result_9, result_8,
      result_7, tmp__trace) <@ __addstate_imem_avx2x4 (param_18,
      (BArray800.init_arr (W8.of_int 255) 800), param_17, param_16, param_15,
      param_14, param_13, param_12, param_11);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++ tmp__trace);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert,
       (((0 <= param_12) /\ (param_12 <= 18446744073709551615)) /\
       (((0 <= (param_16 + param_12)) /\
        ((param_16 + param_12) <= 18446744073709551615)) /\
       (((0 <= param_12) /\ (param_12 <= 18446744073709551615)) /\
       (((0 <= (param_15 + param_12)) /\
        ((param_15 + param_12) <= 18446744073709551615)) /\
       (((0 <= param_12) /\ (param_12 <= 18446744073709551615)) /\
       (((0 <= (param_14 + param_12)) /\
        ((param_14 + param_12) <= 18446744073709551615)) /\
       (((0 <= param_12) /\ (param_12 <= 18446744073709551615)) /\
       (((0 <= (param_13 + param_12)) /\
        ((param_13 + param_12) <= 18446744073709551615)) /\
       ((((((is_init b_result_2 0 800) /\
           (result_11 = ((param_17 + param_12) + ((param_11 <> 0) ? 1 : 0)))) /\
          (result_10 = (param_16 + param_12))) /\
         (result_9 = (param_15 + param_12))) /\
        (result_8 = (param_14 + param_12))) /\
       (result_7 = (param_13 + param_12))))))))))))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_10) /\ (result_10 <= 18446744073709551615)))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_9) /\ (result_9 <= 18446744073709551615)))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_8) /\ (result_8 <= 18446744073709551615)))]);
      trace___absorb_imem_avx2x4 <-
      (trace___absorb_imem_avx2x4 ++
      [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
      st <- result_12;
      aT <- result_11;
      buf0 <- result_10;
      buf1 <- result_9;
      buf2 <- result_8;
      buf3 <- result_7;
      if ((tRAILB <> 0)) {
        param_10 <- st;
        param_9 <- rATE8;
        (result_6, b_result_1, tmp__trace) <@ __addratebit_avx2x4 (param_10,
        (BArray800.init_arr (W8.of_int 255) 800), param_9);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++ tmp__trace);
        trace___absorb_imem_avx2x4 <-
        (trace___absorb_imem_avx2x4 ++
        [(Assert, (is_init b_result_1 0 800))]);
        st <- result_6;
      } else {
        
      }
    }
    b_st <- (BArray800.init_arr (W8.of_int 255) 800);
    return (st, b_st, aT, buf0, buf1, buf2, buf3, trace___absorb_imem_avx2x4);
  }
  proc __dumpstate_imem_avx2x4 (buf0:int, buf1:int, buf2:int, buf3:int,
                                lEN:int, st:BArray800.t, b_st:BArray800.t) : 
  int * int * int * int * trace = {
    var x0:W256.t;
    var x1:W256.t;
    var x2:W256.t;
    var x3:W256.t;
    var t0:W64.t;
    var t1:W64.t;
    var t2:W64.t;
    var t3:W64.t;
    var i:int;
    var param:W64.t;
    var param_0:int;
    var param_1:int;
    var result:int;
    var result_0:int;
    var param_2:W64.t;
    var param_3:int;
    var param_4:int;
    var result_1:int;
    var result_2:int;
    var param_5:W64.t;
    var param_6:int;
    var param_7:int;
    var result_3:int;
    var result_4:int;
    var param_8:W64.t;
    var param_9:int;
    var param_10:int;
    var result_5:int;
    var result_6:int;
    var param_11:W256.t;
    var param_12:W256.t;
    var param_13:W256.t;
    var param_14:W256.t;
    var result_7:W256.t;
    var result_8:W256.t;
    var result_9:W256.t;
    var result_10:W256.t;
    var trace___dumpstate_imem_avx2x4:trace;
    trace___dumpstate_imem_avx2x4 <- [];
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert,
     (((0 <= buf0) /\ (buf0 <= 18446744073709551615)) /\
     (((0 <= buf1) /\ (buf1 <= 18446744073709551615)) /\
     (((0 <= buf2) /\ (buf2 <= 18446744073709551615)) /\
     (((0 <= buf3) /\ (buf3 <= 18446744073709551615)) /\
     ((((((0 <= lEN) /\ (is_valid ptr_modulus Glob.mem_v buf0 lEN)) /\
        (is_valid ptr_modulus Glob.mem_v buf1 lEN)) /\
       (is_valid ptr_modulus Glob.mem_v buf2 lEN)) /\
      (is_valid ptr_modulus Glob.mem_v buf3 lEN)) /\
     (is_init b_st 0 800)))))))]);
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
    i <- 0;
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert,
     ((0 <= (32 * (lEN %/ 32))) /\
     ((32 * (lEN %/ 32)) <= 18446744073709551615)))]);
    while ((i < (32 * (lEN %/ 32)))) {
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ (((4 * i) + 32) <= 800)))]);
      x0 <- (BArray800.get256d st (4 * i));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 32)) /\ (((4 * i) + 32) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 32)) /\ ((((4 * i) + 32) + 32) <= 800)))]);
      x1 <- (BArray800.get256d st ((4 * i) + 32));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 64)) /\ (((4 * i) + 64) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 64)) /\ ((((4 * i) + 64) + 32) <= 800)))]);
      x2 <- (BArray800.get256d st ((4 * i) + 64));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 96)) /\ (((4 * i) + 96) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 96)) /\ ((((4 * i) + 96) + 32) <= 800)))]);
      x3 <- (BArray800.get256d st ((4 * i) + 96));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (i + 32)) /\ ((i + 32) <= 18446744073709551615)))]);
      i <- (i + 32);
      param_14 <- x0;
      param_13 <- x1;
      param_12 <- x2;
      param_11 <- x3;
      (result_10, result_9, result_8, result_7, tmp__trace) <@ __4u64x4_u256x4 (
      param_14, param_13, param_12, param_11);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++ tmp__trace);
      x0 <- result_10;
      x1 <- result_9;
      x2 <- result_8;
      x3 <- result_7;
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf0 32))]);
      Glob.mem <- (storeW256 Glob.mem buf0 x0);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= (buf0 + 32)) /\ ((buf0 + 32) <= 18446744073709551615)))]);
      buf0 <- (buf0 + 32);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf1 32))]);
      Glob.mem <- (storeW256 Glob.mem buf1 x1);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= (buf1 + 32)) /\ ((buf1 + 32) <= 18446744073709551615)))]);
      buf1 <- (buf1 + 32);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf2 32))]);
      Glob.mem <- (storeW256 Glob.mem buf2 x2);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= (buf2 + 32)) /\ ((buf2 + 32) <= 18446744073709551615)))]);
      buf2 <- (buf2 + 32);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf3 32))]);
      Glob.mem <- (storeW256 Glob.mem buf3 x3);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= (buf3 + 32)) /\ ((buf3 + 32) <= 18446744073709551615)))]);
      buf3 <- (buf3 + 32);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= (32 * (lEN %/ 32))) /\
       ((32 * (lEN %/ 32)) <= 18446744073709551615)))]);
    }
    trace___dumpstate_imem_avx2x4 <-
    (trace___dumpstate_imem_avx2x4 ++
    [(Assert,
     ((0 <= (8 * (lEN %/ 8))) /\ ((8 * (lEN %/ 8)) <= 18446744073709551615)))]);
    while ((i < (8 * (lEN %/ 8)))) {
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ (((4 * i) + 8) <= 800)))]);
      t0 <- (BArray800.get64d st (4 * i));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 8)) /\ (((4 * i) + 8) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 8)) /\ ((((4 * i) + 8) + 8) <= 800)))]);
      t1 <- (BArray800.get64d st ((4 * i) + 8));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 16)) /\ (((4 * i) + 16) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 16)) /\ ((((4 * i) + 16) + 8) <= 800)))]);
      t2 <- (BArray800.get64d st ((4 * i) + 16));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 24)) /\ (((4 * i) + 24) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 24)) /\ ((((4 * i) + 24) + 8) <= 800)))]);
      t3 <- (BArray800.get64d st ((4 * i) + 24));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (i + 8)) /\ ((i + 8) <= 18446744073709551615)))]);
      i <- (i + 8);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf0 8))]);
      Glob.mem <- (storeW64 Glob.mem buf0 t0);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (buf0 + 8)) /\ ((buf0 + 8) <= 18446744073709551615)))]);
      buf0 <- (buf0 + 8);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf1 8))]);
      Glob.mem <- (storeW64 Glob.mem buf1 t1);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (buf1 + 8)) /\ ((buf1 + 8) <= 18446744073709551615)))]);
      buf1 <- (buf1 + 8);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf2 8))]);
      Glob.mem <- (storeW64 Glob.mem buf2 t2);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (buf2 + 8)) /\ ((buf2 + 8) <= 18446744073709551615)))]);
      buf2 <- (buf2 + 8);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, (is_valid ptr_modulus Glob.mem_v buf3 8))]);
      Glob.mem <- (storeW64 Glob.mem buf3 t3);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (buf3 + 8)) /\ ((buf3 + 8) <= 18446744073709551615)))]);
      buf3 <- (buf3 + 8);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= (8 * (lEN %/ 8))) /\
       ((8 * (lEN %/ 8)) <= 18446744073709551615)))]);
    }
    if ((0 < (lEN %% 8))) {
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ (((4 * i) + 8) <= 800)))]);
      t0 <- (BArray800.get64d st (4 * i));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 8)) /\ (((4 * i) + 8) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 8)) /\ ((((4 * i) + 8) + 8) <= 800)))]);
      t1 <- (BArray800.get64d st ((4 * i) + 8));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 16)) /\ (((4 * i) + 16) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 16)) /\ ((((4 * i) + 16) + 8) <= 800)))]);
      t2 <- (BArray800.get64d st ((4 * i) + 16));
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= (4 * i)) /\ ((4 * i) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       ((0 <= ((4 * i) + 24)) /\ (((4 * i) + 24) <= 18446744073709551615)))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= ((4 * i) + 24)) /\ ((((4 * i) + 24) + 8) <= 800)))]);
      t3 <- (BArray800.get64d st ((4 * i) + 24));
      param_10 <- buf0;
      param_9 <- (lEN %% 8);
      param_8 <- t0;
      (result_6, result_5, tmp__trace) <@ __mwrite_subu64 (param_10, 
      param_9, param_8);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++ tmp__trace);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)) /\
        (((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_10 +
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0))) /\
        ((param_10 +
         ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)) <=
        18446744073709551615)) /\
       ((result_6 =
        (param_10 +
        ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0))) /\
       (result_5 =
       (param_9 -
       ((0 < ((param_9 < 8) ? param_9 : 8)) ? ((param_9 < 8) ? param_9 : 8) : 0)))))))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
      buf0 <- result_6;
      param_7 <- buf1;
      param_6 <- (lEN %% 8);
      param_5 <- t1;
      (result_4, result_3, tmp__trace) <@ __mwrite_subu64 (param_7, param_6,
      param_5);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++ tmp__trace);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)) /\
        (((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_7 +
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0))) /\
        ((param_7 +
         ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)) <=
        18446744073709551615)) /\
       ((result_4 =
        (param_7 +
        ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0))) /\
       (result_3 =
       (param_6 -
       ((0 < ((param_6 < 8) ? param_6 : 8)) ? ((param_6 < 8) ? param_6 : 8) : 0)))))))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
      buf1 <- result_4;
      param_4 <- buf2;
      param_3 <- (lEN %% 8);
      param_2 <- t2;
      (result_2, result_1, tmp__trace) <@ __mwrite_subu64 (param_4, param_3,
      param_2);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++ tmp__trace);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) /\
        (((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_4 +
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
        ((param_4 +
         ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)) <=
        18446744073709551615)) /\
       ((result_2 =
        (param_4 +
        ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0))) /\
       (result_1 =
       (param_3 -
       ((0 < ((param_3 < 8) ? param_3 : 8)) ? ((param_3 < 8) ? param_3 : 8) : 0)))))))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
      buf2 <- result_2;
      param_1 <- buf3;
      param_0 <- (lEN %% 8);
      param <- t3;
      (result_0, result, tmp__trace) <@ __mwrite_subu64 (param_1, param_0,
      param);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++ tmp__trace);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert,
       (((0 <=
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) /\
        (((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
        ((param_1 +
         ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)) <=
        18446744073709551615)) /\
       ((result_0 =
        (param_1 +
        ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0))) /\
       (result =
       (param_0 -
       ((0 < ((param_0 < 8) ? param_0 : 8)) ? ((param_0 < 8) ? param_0 : 8) : 0)))))))]);
      trace___dumpstate_imem_avx2x4 <-
      (trace___dumpstate_imem_avx2x4 ++
      [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
      buf3 <- result_0;
    } else {
      
    }
    return (buf0, buf1, buf2, buf3, trace___dumpstate_imem_avx2x4);
  }
  proc __squeeze_imem_avx2x4 (buf0:int, buf1:int, buf2:int, buf3:int,
                              lEN:int, st:BArray800.t, b_st:BArray800.t,
                              rATE8:int) : int * int * int * int *
                                           BArray800.t * BArray800.t * trace = {
    var iTERS:int;
    var lO:int;
    var i:int;
    var param:BArray800.t;
    var param_0:int;
    var param_1:int;
    var param_2:int;
    var param_3:int;
    var param_4:int;
    var result:int;
    var result_0:int;
    var result_1:int;
    var result_2:int;
    var param_5:BArray800.t;
    var result_3:BArray800.t;
    var param_6:BArray800.t;
    var param_7:int;
    var param_8:int;
    var param_9:int;
    var param_10:int;
    var param_11:int;
    var result_4:int;
    var result_5:int;
    var result_6:int;
    var result_7:int;
    var param_12:BArray800.t;
    var result_8:BArray800.t;
    var b_result:BArray800.t;
    var b_result_0:BArray800.t;
    var trace___squeeze_imem_avx2x4:trace;
    b_result <- witness;
    b_result_0 <- witness;
    param <- witness;
    param_5 <- witness;
    param_6 <- witness;
    param_12 <- witness;
    result_3 <- witness;
    result_8 <- witness;
    trace___squeeze_imem_avx2x4 <- [];
    trace___squeeze_imem_avx2x4 <-
    (trace___squeeze_imem_avx2x4 ++
    [(Assert,
     (((0 <= buf0) /\ (buf0 <= 18446744073709551615)) /\
     (((0 <= buf1) /\ (buf1 <= 18446744073709551615)) /\
     (((0 <= buf2) /\ (buf2 <= 18446744073709551615)) /\
     (((0 <= buf3) /\ (buf3 <= 18446744073709551615)) /\
     ((((((((0 <= lEN) /\ (0 < rATE8)) /\ (rATE8 < 200)) /\
         (is_valid ptr_modulus Glob.mem_v buf0 lEN)) /\
        (is_valid ptr_modulus Glob.mem_v buf1 lEN)) /\
       (is_valid ptr_modulus Glob.mem_v buf2 lEN)) /\
      (is_valid ptr_modulus Glob.mem_v buf3 lEN)) /\
     (is_init b_st 0 800)))))))]);
    trace___squeeze_imem_avx2x4 <-
    (trace___squeeze_imem_avx2x4 ++
    [(Assert, ((0 <= buf0) /\ (buf0 <= 18446744073709551615)))]);
    trace___squeeze_imem_avx2x4 <-
    (trace___squeeze_imem_avx2x4 ++
    [(Assert, ((0 <= buf1) /\ (buf1 <= 18446744073709551615)))]);
    trace___squeeze_imem_avx2x4 <-
    (trace___squeeze_imem_avx2x4 ++
    [(Assert, ((0 <= buf2) /\ (buf2 <= 18446744073709551615)))]);
    trace___squeeze_imem_avx2x4 <-
    (trace___squeeze_imem_avx2x4 ++
    [(Assert, ((0 <= buf3) /\ (buf3 <= 18446744073709551615)))]);
    iTERS <- (lEN %/ rATE8);
    lO <- (lEN %% rATE8);
    if ((0 < lEN)) {
      if ((0 < iTERS)) {
        i <- 0;
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++
        [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
        while ((i < iTERS)) {
          param_12 <- st;
          (result_8, b_result_0, tmp__trace) <@ _keccakf1600_avx2x4 (
          param_12, (BArray800.init_arr (W8.of_int 255) 800));
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++ tmp__trace);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, (is_init b_result_0 0 800))]);
          st <- result_8;
          param_11 <- buf0;
          param_10 <- buf1;
          param_9 <- buf2;
          param_8 <- buf3;
          param_7 <- rATE8;
          param_6 <- st;
          (result_7, result_6, result_5, result_4, tmp__trace) <@ __dumpstate_imem_avx2x4 (
          param_11, param_10, param_9, param_8, param_7, param_6,
          (BArray800.init_arr (W8.of_int 255) 800));
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++ tmp__trace);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert,
           (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
           (((0 <= (param_11 + param_7)) /\
            ((param_11 + param_7) <= 18446744073709551615)) /\
           (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
           (((0 <= (param_10 + param_7)) /\
            ((param_10 + param_7) <= 18446744073709551615)) /\
           (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
           (((0 <= (param_9 + param_7)) /\
            ((param_9 + param_7) <= 18446744073709551615)) /\
           (((0 <= param_7) /\ (param_7 <= 18446744073709551615)) /\
           (((0 <= (param_8 + param_7)) /\
            ((param_8 + param_7) <= 18446744073709551615)) /\
           ((((result_7 = (param_11 + param_7)) /\
             (result_6 = (param_10 + param_7))) /\
            (result_5 = (param_9 + param_7))) /\
           (result_4 = (param_8 + param_7))))))))))))]);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, ((0 <= result_7) /\ (result_7 <= 18446744073709551615)))]);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, ((0 <= result_6) /\ (result_6 <= 18446744073709551615)))]);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, ((0 <= result_5) /\ (result_5 <= 18446744073709551615)))]);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, ((0 <= result_4) /\ (result_4 <= 18446744073709551615)))]);
          buf0 <- result_7;
          buf1 <- result_6;
          buf2 <- result_5;
          buf3 <- result_4;
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, ((0 <= (i + 1)) /\ ((i + 1) <= 18446744073709551615)))]);
          i <- (i + 1);
          trace___squeeze_imem_avx2x4 <-
          (trace___squeeze_imem_avx2x4 ++
          [(Assert, ((0 <= iTERS) /\ (iTERS <= 18446744073709551615)))]);
        }
      } else {
        
      }
      if ((0 < lO)) {
        param_5 <- st;
        (result_3, b_result, tmp__trace) <@ _keccakf1600_avx2x4 (param_5,
        (BArray800.init_arr (W8.of_int 255) 800));
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++ tmp__trace);
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++ [(Assert, (is_init b_result 0 800))]);
        st <- result_3;
        param_4 <- buf0;
        param_3 <- buf1;
        param_2 <- buf2;
        param_1 <- buf3;
        param_0 <- lO;
        param <- st;
        (result_2, result_1, result_0, result, tmp__trace) <@ __dumpstate_imem_avx2x4 (
        param_4, param_3, param_2, param_1, param_0, param,
        (BArray800.init_arr (W8.of_int 255) 800));
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++ tmp__trace);
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++
        [(Assert,
         (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
         (((0 <= (param_4 + param_0)) /\
          ((param_4 + param_0) <= 18446744073709551615)) /\
         (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
         (((0 <= (param_3 + param_0)) /\
          ((param_3 + param_0) <= 18446744073709551615)) /\
         (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
         (((0 <= (param_2 + param_0)) /\
          ((param_2 + param_0) <= 18446744073709551615)) /\
         (((0 <= param_0) /\ (param_0 <= 18446744073709551615)) /\
         (((0 <= (param_1 + param_0)) /\
          ((param_1 + param_0) <= 18446744073709551615)) /\
         ((((result_2 = (param_4 + param_0)) /\
           (result_1 = (param_3 + param_0))) /\
          (result_0 = (param_2 + param_0))) /\
         (result = (param_1 + param_0))))))))))))]);
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++
        [(Assert, ((0 <= result_2) /\ (result_2 <= 18446744073709551615)))]);
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++
        [(Assert, ((0 <= result_1) /\ (result_1 <= 18446744073709551615)))]);
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++
        [(Assert, ((0 <= result_0) /\ (result_0 <= 18446744073709551615)))]);
        trace___squeeze_imem_avx2x4 <-
        (trace___squeeze_imem_avx2x4 ++
        [(Assert, ((0 <= result) /\ (result <= 18446744073709551615)))]);
        buf0 <- result_2;
        buf1 <- result_1;
        buf2 <- result_0;
        buf3 <- result;
      } else {
        
      }
    } else {
      
    }
    b_st <- (BArray800.init_arr (W8.of_int 255) 800);
    return (buf0, buf1, buf2, buf3, st, b_st, trace___squeeze_imem_avx2x4);
  }
}.

(* The post and trace are valid. *)

lemma keccakf1600_index_trace _x _y :
      hoare [M.keccakf1600_index :
      (((_y = y) /\ (_x = x)) /\ true) ==> (true /\ (valid res.`2))].
proof.
by proc; auto .
qed .

lemma keccakf1600_rho_offsets_trace _i :
      hoare [M.keccakf1600_rho_offsets :
      ((_i = i) /\ true) ==> (true /\ (valid res.`2))].
proof.
proc; inline *; while (true); auto .
qed .

lemma keccakf1600_rhotates_trace _x _y :
      hoare [M.keccakf1600_rhotates :
      (((_y = y) /\ (_x = x)) /\ true) ==> (true /\ (valid res.`2))].
proof.
proc; inline *; auto; while(true); auto .
qed .

lemma __keccakf1600_pround_avx2_trace _state _b_state :
      hoare [M.__keccakf1600_pround_avx2 :
      (((_b_state = b_state) /\ (_state = state)) /\
      (is_init _b_state 0 224)) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
  proc. rewrite /=. wp -1.
  seq 2: (valid trace___keccakf1600_pround_avx2). by auto.
  conseq (:true). smt(BArray224.init_arrP).
  by auto.
qed.


lemma _keccakf1600_avx2_trace _state _b_state :
      hoare [M._keccakf1600_avx2 :
      (((_b_state = b_state) /\ (_state = state)) /\
      (is_init _b_state 0 224)) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
while ((valid trace__keccakf1600_avx2) /\ is_init b_state 0 224 /\ 0 <=  r).
auto .
ecall (__keccakf1600_pround_avx2_trace param (BArray224.init_arr
                                             (W8.of_int 255) 224)).
auto .
rewrite /is_init /valid /=.
smt (all_cat BArray224.init_arrP ).
auto .
ecall (__keccakf1600_pround_avx2_trace param (BArray224.init_arr
                                             (W8.of_int 255) 224)).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray224.init_arrP ).
qed .

lemma __stavx2_pack_trace _st _b_st :
      hoare [M.__stavx2_pack :
      (((_b_st = b_st) /\ (_st = st)) /\ (is_init _b_st 0 200)) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __stavx2_unpack_trace _st _b_st _state _b_state :
      hoare [M.__stavx2_unpack :
      (((_b_state = b_state) /\
       ((_state = state) /\ ((_b_st = b_st) /\ (_st = st)))) /\
      (is_init _b_state 0 224)) ==>
      ((is_init res.`2 0 200) /\ (valid res.`3))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __mread_subu64_trace _buf _lEN _tRAIL :
      hoare [M.__mread_subu64 :
      (((_tRAIL = tRAIL) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((is_valid ptr_modulus Glob.mem_v _buf
        ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8))) /\
       (0 <= _tRAIL)) /\
      (_tRAIL < 256))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)) /\
        (((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)) <=
        18446744073709551615)) /\
       (((res.`1 =
         (_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))) /\
        (res.`2 =
        (_lEN -
        ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)))) /\
       (res.`3 = ((8 <= _lEN) ? _tRAIL : 0)))))) /\
      (valid res.`5))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __mread_bcast_4subu64_trace _buf _lEN _tRAIL :
      hoare [M.__mread_bcast_4subu64 :
      (((_tRAIL = tRAIL) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((is_valid ptr_modulus Glob.mem_v _buf
        ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8))) /\
       (0 <= _tRAIL)) /\
      (_tRAIL < 256))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)) /\
        (((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)) <=
        18446744073709551615)) /\
       (((res.`1 =
         (_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))) /\
        (res.`2 =
        (_lEN -
        ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)))) /\
       (res.`3 = ((8 <= _lEN) ? _tRAIL : 0)))))) /\
      (valid res.`5))].
proof.
proc; auto . sp.
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
ecall (__mread_subu64_trace param_1 param_0 param).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
qed .

lemma __mread_subu128_trace _buf _lEN _tRAIL :
      hoare [M.__mread_subu128 :
      (((_tRAIL = tRAIL) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((is_valid ptr_modulus Glob.mem_v _buf
        ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16))) /\
       (0 <= _tRAIL)) /\
      (_tRAIL < 256))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <=
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0)) /\
        (((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0)) <=
        18446744073709551615)) /\
       (((res.`1 =
         (_buf +
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0))) /\
        (res.`2 =
        (_lEN -
        ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0)))) /\
       (res.`3 = ((16 <= _lEN) ? _tRAIL : 0)))))) /\
      (valid res.`5))].
proof.
proc; auto . sp.
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
if .
auto .
ecall (__mread_subu64_trace param_1 param_0 param).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
ecall (__mread_subu64_trace param_4 param_3 param_2).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
qed .

lemma __mread_subu256_trace _buf _lEN _tRAIL :
      hoare [M.__mread_subu256 :
      (((_tRAIL = tRAIL) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((is_valid ptr_modulus Glob.mem_v _buf
        ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32))) /\
       (0 <= _tRAIL)) /\
      (_tRAIL < 256))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <=
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0)) /\
        (((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0)) <=
        18446744073709551615)) /\
       (((res.`1 =
         (_buf +
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0))) /\
        (res.`2 =
        (_lEN -
        ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0)))) /\
       (res.`3 = ((32 <= _lEN) ? _tRAIL : 0)))))) /\
      (valid res.`5))].
proof.
proc; auto . sp.
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
if .
auto .
ecall (__mread_subu128_trace param_1 param_0 param).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
ecall (__mread_subu128_trace param_4 param_3 param_2).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
qed .

lemma __mwrite_subu64_trace _buf _lEN _w :
      hoare [M.__mwrite_subu64 :
      (((_w = w) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (is_valid ptr_modulus Glob.mem_v _buf
      ((((_lEN < 8) ? _lEN : 8) < 0) ? 0 : ((_lEN < 8) ? _lEN : 8)))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)) /\
        (((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0)) <=
        18446744073709551615)) /\
       ((res.`1 =
        (_buf +
        ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))) /\
       (res.`2 =
       (_lEN - ((0 < ((_lEN < 8) ? _lEN : 8)) ? ((_lEN < 8) ? _lEN : 8) : 0))))))) /\
      (valid res.`3))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __mwrite_subu128_trace _buf _lEN _w :
      hoare [M.__mwrite_subu128 :
      (((_w = w) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (is_valid ptr_modulus Glob.mem_v _buf
      ((((_lEN < 16) ? _lEN : 16) < 0) ? 0 : ((_lEN < 16) ? _lEN : 16)))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <=
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0)) /\
        (((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0)) <=
        18446744073709551615)) /\
       ((res.`1 =
        (_buf +
        ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0))) /\
       (res.`2 =
       (_lEN -
       ((0 < ((_lEN < 16) ? _lEN : 16)) ? ((_lEN < 16) ? _lEN : 16) : 0))))))) /\
      (valid res.`3))].
proof.
proc; auto . sp.
if .
auto .
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
ecall (__mwrite_subu64_trace param_1 param_0 param).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
qed .

lemma __mwrite_subu256_trace _buf _lEN _w :
      hoare [M.__mwrite_subu256 :
      (((_w = w) /\ ((_lEN = lEN) /\ (_buf = buf))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (is_valid ptr_modulus Glob.mem_v _buf
      ((((_lEN < 32) ? _lEN : 32) < 0) ? 0 : ((_lEN < 32) ? _lEN : 32)))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <=
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0)) /\
        (((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0) <=
        18446744073709551615)) /\
       (((0 <=
         (_buf +
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0))) /\
        ((_buf +
         ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0)) <=
        18446744073709551615)) /\
       ((res.`1 =
        (_buf +
        ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0))) /\
       (res.`2 =
       (_lEN -
       ((0 < ((_lEN < 32) ? _lEN : 32)) ? ((_lEN < 32) ? _lEN : 32) : 0))))))) /\
      (valid res.`3))].
proof.
proc; auto . sp.
if .
auto .
if .
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
ecall (__mwrite_subu128_trace param_1 param_0 param).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
qed .

lemma __u64_to_u256_trace _x _l :
      hoare [M.__u64_to_u256 :
      (((_l = l) /\ (_x = x)) /\ true) ==> (true /\ (valid res.`2))].
proof.
by proc; auto .
qed .

lemma __state_init_avx2_trace  :
      hoare [M.__state_init_avx2 :
      (true /\ true) ==> ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
while ((valid trace___state_init_avx2) /\  (((0 <= i) /\ (i <= 7)) /\
    (is_init b_st 0 (32 * i)))).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __pstate_init_avx2_trace _pst _b_pst :
      hoare [M.__pstate_init_avx2 :
      (((_b_pst = b_pst) /\ (_pst = pst)) /\ true) ==>
      (((is_init res.`2 0 200) /\ (is_init res.`4 0 224)) /\ (valid res.`5))].
proof.
proc; auto .
ecall (__state_init_avx2_trace).
auto .
while ((valid trace___pstate_init_avx2) /\  (((0 <= i) /\ (i <= 6)) /\
                                            (is_init b_pst 0 (32 * i)))).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray224.init_arrP).
qed .

lemma __perm_reg3456_avx2_trace _r3 _r4 _r5 _r6 :
      hoare [M.__perm_reg3456_avx2 :
      (((_r6 = r6) /\ ((_r5 = r5) /\ ((_r4 = r4) /\ (_r3 = r3)))) /\ true) ==>
      (true /\ (valid res.`5))].
proof.
by proc; auto .
qed .

lemma __unperm_reg3456_avx2_trace _st3 _st4 _st5 _st6 :
      hoare [M.__unperm_reg3456_avx2 :
      (((_st6 = st6) /\ ((_st5 = st5) /\ ((_st4 = st4) /\ (_st3 = st3)))) /\
      true) ==> (true /\ (valid res.`5))].
proof.
by proc; auto .
qed .

lemma __state_from_pstate_avx2_trace _pst _b_pst :
      hoare [M.__state_from_pstate_avx2 :
      (((_b_pst = b_pst) /\ (_pst = pst)) /\ (is_init _b_pst 0 200)) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
ecall (__perm_reg3456_avx2_trace param_2 param_1 param_0 param).
auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __addstate_r3456_avx2_trace _st _b_st _r3 _r4 _r5 _r6 :
      hoare [M.__addstate_r3456_avx2 :
      (((_r6 = r6) /\
       ((_r5 = r5) /\
       ((_r4 = r4) /\ ((_r3 = r3) /\ ((_b_st = b_st) /\ (_st = st)))))) /\
      (is_init _b_st 0 224)) ==> ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
ecall (__perm_reg3456_avx2_trace param_2 param_1 param_0 param).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray224.init_arrP).
qed .

lemma __addpst01_avx2_trace _st _b_st _pst _b_pst :
      hoare [M.__addpst01_avx2 :
      (((_b_pst = b_pst) /\ ((_pst = pst) /\ ((_b_st = b_st) /\ (_st = st)))) /\
      ((is_init _b_pst 0 200) /\ (is_init _b_st 0 224))) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat BArray224.init_arrP).
qed .

lemma __addpst23456_avx2_trace _st _b_st _pst _b_pst :
      hoare [M.__addpst23456_avx2 :
      (((_b_pst = b_pst) /\ ((_pst = pst) /\ ((_b_st = b_st) /\ (_st = st)))) /\
      ((is_init _b_pst 0 200) /\ (is_init _b_st 0 224))) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
ecall (__addstate_r3456_avx2_trace param_3 (BArray224.init_arr
                                           (W8.of_int 255) 224) param_2 
       param_1 param_0 param).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray224.init_arrP).
qed .

lemma _addpstate_avx2_trace _st _b_st _pst _b_pst :
      hoare [M._addpstate_avx2 :
      (((_b_pst = b_pst) /\ ((_pst = pst) /\ ((_b_st = b_st) /\ (_st = st)))) /\
      ((is_init _b_pst 0 200) /\ (is_init _b_st 0 224))) ==>
      ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; auto .
ecall (__addpst23456_avx2_trace param_0 (BArray224.init_arr (W8.of_int 255)
                                        224) param (BArray200.init_arr
                                                   (W8.of_int 255) 200)).
auto .
ecall (__addpst01_avx2_trace param_2 (BArray224.init_arr (W8.of_int 255) 224) 
       param_1 (BArray200.init_arr (W8.of_int 255) 200)).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray200.init_arrP BArray224.init_arrP).
qed .

lemma __stavx2_pos_avx2_trace _pOS :
      hoare [M.__stavx2_pos_avx2 :
      ((_pOS = pOS) /\ true) ==>
      (((0 <= res.`1) /\ (res.`1 < 7)) /\ (valid res.`3))].
proof.
by proc; auto .
qed .

lemma __addratebit_avx2_trace _st _b_st _rATE8 :
      hoare [M.__addratebit_avx2 :
      (((_rATE8 = rATE8) /\ ((_b_st = b_st) /\ (_st = st))) /\
      (is_init _b_st 0 224)) ==> ((is_init res.`2 0 224) /\ (valid res.`3))].
proof.
proc; rewrite /=.
  seq 10: (#pre /\ valid trace___addratebit_avx2 /\ 0<=r /\ r < 7 ).
  + auto. ecall (__stavx2_pos_avx2_trace param_1).
    auto. smt(all_cat).
  if .
  + auto .
    rewrite /trace /is_init /valid /=.
    smt (all_cat BArray224.init_arrP).
  auto .
  ecall (__u64_to_u256_trace param_0 param).
  auto .
  rewrite /trace /is_init /valid /=.
  smt (all_cat BArray224.init_arrP).
qed .

lemma __addstate_imem_avx2_trace _st _b_st _buf _lEN _tRAILB :
      hoare [M.__addstate_imem_avx2 :
      (((_tRAILB = tRAILB) /\
       ((_lEN = lEN) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      ((((0 <= _lEN) /\ (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
       (is_init _b_st 0 224)) /\
      (_lEN <= 200)))))) ==>
      ((((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf + _lEN)) /\ ((_buf + _lEN) <= 18446744073709551615)) /\
       ((is_init res.`2 0 224) /\ (res.`3 = (_buf + _lEN)))))) /\
      (valid res.`4))].
proof.
  proc; rewrite /= .
  seq 31: (valid trace___addstate_imem_avx2 /\ is_init b_st 0 224 /\
           buf = _buf + (if _lEN < 40 then _lEN else 40) /\ 0<=_buf /\
           lEN = (if _lEN < 40 then 0  else _lEN - 40) /\ _lEN <= 200 /\
           is_valid ptr_modulus Glob.mem_v _buf _lEN /\ 0 <= _lEN /\ 0<=tRAILB /\ tRAILB <256).
  + auto.
    ecall (__mread_subu256_trace param_30 param_29 param_28).
    auto .
    ecall (__mread_bcast_4subu64_trace param_33 param_32 param_31).
    auto. move => &m /> 5? h *.
    rewrite /is_init /valid /=. 
    smt(all_cat).
  if.
  + pose len_40 := _lEN - 40.
    seq 12: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_40 <= 8 then _lEN else 48) /\  0<=_buf /\
              lEN = (if len_40 <= 8 then 0 else _lEN - 48)).
    + auto. ecall(__mread_subu64_trace param_27 param_26 param_25). auto.
      smt( all_cat).
    pose len_48 := _lEN - 48.
    seq 11: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_48 <= 32 then _lEN else 80) /\  0<=_buf /\
              lEN = (if len_48 <= 32 then 0 else _lEN - 80)).
    + auto. ecall(__mread_subu256_trace param_24 param_23 param_22). auto.
      smt( all_cat).
    pose len_80 := _lEN - 80.
    seq 12: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid ptr_modulus Glob.mem_v  _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_80 <= 8 then _lEN else 88) /\  0<=_buf /\
              lEN = (if len_80 <= 8 then 0 else _lEN - 88)).
    + auto. ecall(__mread_subu64_trace param_21 param_20 param_19). auto.
      smt( all_cat).
    pose len_88 := _lEN - 88.
    seq 11: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_88 <= 32 then _lEN else 120) /\ 0<=_buf /\
              lEN = (if len_88 <= 32 then 0 else _lEN - 120)).
    + auto. ecall(__mread_subu256_trace param_18 param_17 param_16). auto.
      smt( all_cat).
    pose len_120 := _lEN - 120.
    seq 12: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid  ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_120 <= 8 then _lEN else 128) /\ 0<=_buf /\
              lEN = (if len_120 <= 8 then 0 else _lEN - 128)).
    + auto. ecall(__mread_subu64_trace param_15 param_14 param_13). auto.
      smt( all_cat).
    pose len_128 := _lEN - 128.
    seq 11: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid  ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_128 <= 32 then _lEN else 160) /\ 0<=_buf /\
              lEN = (if len_128 <= 32 then 0 else _lEN - 160)).
    + auto. ecall(__mread_subu256_trace param_12 param_11 param_10). auto.
      smt( all_cat).
    pose len_160 := _lEN - 160.
    seq 12: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\ 
  is_valid  ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf + (if len_160 <= 8 then _lEN else 168) /\ 0<=_buf /\
              lEN = (if len_160 <= 8 then 0 else _lEN - 168)).
    + auto. ecall(__mread_subu64_trace param_9 param_8 param_7). auto.
      smt( all_cat).
    pose len_168 := _lEN - 168.
    seq 11: ( valid  trace___addstate_imem_avx2 /\ _lEN <= 200 /\  0<=_buf /\
  is_valid ptr_modulus Glob.mem_v _buf _lEN  /\
  0  <= _lEN /\ 0<=tRAILB /\ tRAILB <256 /\
               buf = _buf +  _lEN ).
    + auto. ecall(__mread_subu256_trace param_6 param_5 param_4). auto.
      smt( all_cat).
    auto. ecall(__addstate_r3456_avx2_trace param_3 (BArray224.init_arr (W8.of_int 255) 224) param_2 param_1 param_0 param). auto. move => &m />  *.
  smt(BArray224.init_arrP all_cat).
  auto.  move => &m />  *. smt(BArray224.init_arrP).
qed.

lemma __absorb_imem_avx2_trace _st _b_st _buf _lEN _rATE8 _tRAILB :
      hoare [M.__absorb_imem_avx2 :
      (((_tRAILB = tRAILB) /\
       ((_rATE8 = rATE8) /\
       ((_lEN = lEN) /\ ((_buf = buf) /\ ((_b_st = b_st) /\ (_st = st)))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((((0 <= _lEN) /\ (0 < _rATE8)) /\ (_rATE8 < 200)) /\
       (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
      (is_init _b_st 0 224)))))) ==>
      ((((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)) /\
       (is_init res.`2 0 224)) /\
      (valid res.`4))].
proof.
 proc. rewrite /=.
  seq 16: (#pre /\ valid trace___absorb_imem_avx2). by auto.
  sp. if.
  + sp 1.
    seq 13: (is_init b_st 0 224 /\ valid trace___absorb_imem_avx2 /\ 0<=buf /\ buf < W64.modulus).
    + auto.
      ecall (__addstate_imem_avx2_trace param_4 (BArray224.init_arr (W8.of_int 255)
                                          224) param_3 param_2 param_1). auto.
      while ((valid trace___absorb_imem_avx2) /\ 0<= i /\ i <= iTERS/\ 0<= _buf /\
  0 <= tRAILB /\ tRAILB < 256 /\ 0 <= lEN /\ is_valid ptr_modulus Glob.mem_v _buf lEN /\ 0<rATE8 /\ rATE8 <200
  /\ iTERS = lEN%/ rATE8 /\ buf = _buf + i*rATE8).
      + auto.
        ecall (_keccakf1600_avx2_trace param_5 (BArray224.init_arr (W8.of_int 255)
                                       224)). auto .
        ecall (__addstate_imem_avx2_trace param_9 (BArray224.init_arr (W8.of_int 255)
                                          224) param_8 param_7 param_6). auto .
        rewrite /trace /is_init /valid /=.
        move => &m /> *.
        split. split. smt(). split. smt(). split. split; smt(BArray224.init_arrP). smt().
        move => /> *.
        rewrite !all_cat /=. smt(Ring.IntID.mulrDl).
      auto.
      move => &m /> *.
      smt(all_cat  W64.to_uint_cmp BArray224.init_arrP).
    if.     
    + auto.
      ecall (__addratebit_avx2_trace param_0 (BArray224.init_arr (W8.of_int 255)
                                       224) param). auto .
      move => &m /> *.
      smt(all_cat BArray224.init_arrP).
    auto. smt( BArray224.init_arrP).
  seq 11: (is_init b_st 0 224 /\ valid trace___absorb_imem_avx2 /\  0<=buf /\ buf < W64.modulus).
  + auto.  ecall (__addstate_imem_avx2_trace param_4 (BArray224.init_arr (W8.of_int 255)
                                          224) param_3 param_2 param_1). auto.
    smt(all_cat is_validP BArray224.init_arrP).
  if. 
  + auto. ecall (__addratebit_avx2_trace param_0 (BArray224.init_arr (W8.of_int 255)
  224) param). auto . smt(BArray224.init_arrP all_cat).
  auto. smt( BArray224.init_arrP).
qed .


lemma __pstate_imem_avx2_trace _pst _b_pst _aT _buf _lEN _tRAILB :
      hoare [M.__pstate_imem_avx2 :
      (((_tRAILB = tRAILB) /\
       ((_lEN = lEN) /\
       ((_buf = buf) /\ ((_aT = aT) /\ ((_b_pst = b_pst) /\ (_pst = pst)))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      ((((((0 <= _lEN) /\ (0 <= _aT)) /\ (_aT < 200)) /\
        (((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)) < 200)) /\
       (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
      (is_init _b_pst 0 200)))))) ==>
      ((((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf + _lEN)) /\ ((_buf + _lEN) <= 18446744073709551615)) /\
       (((is_init res.`2 0 200) /\
        (res.`3 = ((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)))) /\
       (res.`4 = (_buf + _lEN)))))) /\
      (valid res.`5))].
proof.
 proc; rewrite /=.
  seq 9: (is_valid ptr_modulus Glob.mem_v  _buf _lEN /\ valid trace___pstate_imem_avx2 /\
          0 <= _tRAILB /\ _tRAILB < 256 /\ 0 <= _lEN /\ 0 <= _aT /\ 0<=_buf /\
          aT %% 8 = 0 /\ _aT + _lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\ 0<= aT /\ aT < 200 /\
          aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
          tRAILB =( if 0 < lO /\ lO + _lEN < 8 then 0 else _tRAILB) /\ lO = _aT %% 8 /\
          at=(if 0 < lO /\ lO + _lEN < 8 then _aT %/ 8 else  aT%/8)/\
          lEN =(if 0 < lO then if lO + _lEN < 8 then 0 else  _lEN - 8 + lO else _lEN)  /\
          aT =(if 0 < lO then if lO + _lEN < 8 then 0 else  _aT + 8 - lO else _aT)  /\
          buf = _buf + (if 0 < lO then if lO + _lEN < 8 then _lEN else 8 - lO else 0)).
  + sp.  
    if.
    + if.
      + auto. ecall (__mread_subu64_trace param_4 param_3 param_2). auto.
        rewrite /valid /=. move => />  *. smt(all_cat). 
      if.
      + auto.  move => &m />  *.
        smt(). 
      auto.  
      ecall (__mread_subu64_trace param_7 param_6 param_5). auto.
      rewrite /valid /=. move => &m /> *.
      smt( all_cat).
    auto.
    rewrite /valid /=. move => &m /> *.
    smt().
  auto.
  seq 1: ( is_valid ptr_modulus Glob.mem_v  buf lEN /\ valid trace___pstate_imem_avx2 /\
          0 <= _tRAILB /\ _tRAILB < 256 /\ 0<= _aT /\ 0<=_buf /\
          aT %% 8 = 0 /\ _aT + _lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\ 0 <= aT /\
          aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
          buf = _buf +  (_lEN - lEN) /\ lEN <= _lEN /\ 0<=lEN /\ 0<= at /\
          tRAILB =( if 0 < lO /\ lO + _lEN < 8 then 0 else _tRAILB) /\ lO = _aT %% 8 /\
          lEN < 32 /\ _buf + _lEN < W64.modulus /\ 8 *  at <= _aT + _lEN - lEN).
  + if. wp.
  + while ( is_valid ptr_modulus Glob.mem_v  ( buf) (lEN - ( at - aT%/8) * 8) /\ _lEN < 200
            /\ valid trace___pstate_imem_avx2 /\ 32 <= _lEN /\ 0<=_buf /\
          0 <= _tRAILB /\ _tRAILB < 256 /\ 0 <= lEN /\ 0 <= aT /\ _aT + _lEN = aT + lEN /\
          aT %% 8 = 0 /\ aT + lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\ aT%/8 <=  at /\
          aLL = _aT + _lEN + (if 0 < lO /\ lO + lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
          buf =  _buf + (_lEN - lEN) +(at - aT%/8) * 8 /\ lEN <= _lEN /\ lO = _aT %% 8 /\
          tRAILB =( if 0 < lO /\ lO + _lEN < 8 then 0 else _tRAILB) /\  (at - aT%/8) %% 4 = 0 /\
          (at < aT %/ 8 + 4 * (lEN %/ 32) =>  32 <= (lEN - (at - aT%/8) * 8)) /\
          (at - aT%/8) * 8 <= lEN - lEN%%32 /\ at <= aT %/ 8 + 4 * (lEN %/ 32)).
      + auto. rewrite /trace  /=. move => &m /> *.
        smt( all_cat).
      auto. rewrite /valid /=. move => &m /> *.
      smt( all_cat).
    auto. rewrite /valid /=. move => &m /> *.
    smt().
  seq 1: ( is_valid ptr_modulus Glob.mem_v buf lEN /\ valid trace___pstate_imem_avx2 /\
          0 <= _tRAILB /\ _tRAILB < 256 /\ _lEN < 200 /\ 0 <= _buf /\ 0<=at /\
          aT %% 8 = 0 /\ _aT + _lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\ 0 <= aT /\
          aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
          buf = _buf + (_lEN - lEN) /\ lEN <= _lEN /\ 0<=lEN /\ lO = _aT %% 8 /\
          tRAILB =( if 0 < lO /\ lO + _lEN < 8 then 0 else _tRAILB) /\
          lEN < 16 /\   _buf + _lEN < W64.modulus /\
          8 *  at <= _aT + _lEN - lEN). 
  + if.
    + auto.  rewrite /valid /=. move => &m />  *.
      smt(all_cat).
    auto. smt().
  seq 1: ( is_valid ptr_modulus Glob.mem_v buf lEN /\ valid trace___pstate_imem_avx2 /\
          0 <= _tRAILB /\ _tRAILB < 256 /\ _lEN < 200 /\  0<= _buf /\ 0<= at /\
          aT %% 8 = 0 /\ _aT + _lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\ 0 <= aT /\
          aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
          buf = _buf + (_lEN - lEN) /\ lEN <= _lEN /\ 0<=lEN /\ lO = _aT %% 8 /\
          tRAILB =( if 0 < lO /\ lO + _lEN < 8 then 0 else _tRAILB) /\ lEN < 8 /\  _buf + _lEN < W64.modulus /\
          8 * at <= _aT + _lEN - lEN). 
  + if.
    + auto. rewrite /valid /=. move => &m />  *.
      smt(all_cat).
    auto. smt().
  sp.
  if.
  + auto. ecall(__mread_subu64_trace param_1 param_0 param). auto.
    auto.  rewrite /valid /=. move => &m />  *.
    split. smt( all_cat BArray200.init_arrP). move => *.
    split. smt( all_cat BArray200.init_arrP). move => *.
    smt( all_cat BArray200.init_arrP).
  auto.  smt( all_cat BArray200.init_arrP).
qed.



lemma __pabsorb_imem_avx2_trace _pst _b_pst _aT _st _b_st _buf _lEN _rATE8 _tRAILB :
      hoare [M.__pabsorb_imem_avx2 :
      (((_tRAILB = tRAILB) /\
       ((_rATE8 = rATE8) /\
       ((_lEN = lEN) /\
       ((_buf = buf) /\
       ((_b_st = b_st) /\
       ((_st = st) /\ ((_aT = aT) /\ ((_b_pst = b_pst) /\ (_pst = pst))))))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      ((((((((0 <= _lEN) /\ (0 <= _aT)) /\ (_aT < _rATE8)) /\ (0 < _rATE8)) /\
         (_rATE8 < 200)) /\
        (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
       (is_init _b_pst 0 200)) /\
      (is_init _b_st 0 224)))))) ==>
      ((((0 <= res.`6) /\ (res.`6 <= 18446744073709551615)) /\
       ((is_init res.`2 0 200) /\ (is_init res.`5 0 224))) /\
      (valid res.`7))].
proof.
proc. rewrite /= .
  seq 43: (#pre /\ valid trace___pabsorb_imem_avx2) . by auto.
  sp.
  if .
  + seq 12:( valid trace___pabsorb_imem_avx2 /\ is_init b_st 0 224 /\ 0<rATE8 /\ rATE8 <200 /\ 0<=aT /\ aT < 200 /\ 0<=buf /\ buf < W64.modulus ).
    + auto. ecall (__pstate_imem_avx2_trace param_9 (BArray200.init_arr (W8.of_int 255)
          200) param_8 param_7 param_6 param_5). auto.
      smt(all_cat BArray200.init_arrP).
    if . sp.
    + if .
      + auto.
        ecall (__addratebit_avx2_trace param_0 (BArray224.init_arr (W8.of_int 255) 224) param). auto .
        ecall (__addpst01_avx2_trace param_2 (BArray224.init_arr (W8.of_int 255) 224) 
             param_1 (BArray200.init_arr (W8.of_int 255) 200)). auto.
        while ((valid trace___pabsorb_imem_avx2) /\ 0<=aT /\ 0<=buf /\ buf < W64.modulus /\
                0<= i /\ is_init b_st 0 224 /\ 0<rATE8 /\ rATE8 <200 ).
        + auto. move => &m. smt(all_cat).
        auto. move => /> *.
        smt(all_cat BArray200.init_arrP BArray224.init_arrP).
      auto.
      ecall (_addpstate_avx2_trace param_4 (BArray224.init_arr (W8.of_int 255) 224) 
       param_3 (BArray200.init_arr (W8.of_int 255) 200)). auto .
      while ((valid trace___pabsorb_imem_avx2) /\ aT < 200 /\  0<=buf /\ buf < W64.modulus /\
                0<= i /\ is_init b_st 0 224 /\ 0<rATE8 /\ rATE8 <200 ).
      + auto. smt(all_cat).
      auto. smt(all_cat BArray200.init_arrP BArray224.init_arrP).
    auto. smt( BArray200.init_arrP BArray224.init_arrP).
  seq 6: ( valid trace___pabsorb_imem_avx2 /\ is_init b_st 0 224 /\
           is_valid ptr_modulus Glob.mem_v buf lEN /\
           0<=tRAILB /\ tRAILB < 256 /\ 0<=lEN /\ lEN < 200 /\  0<=buf /\ buf < W64.modulus /\
           0<rATE8 /\ rATE8 <200 ). wp.
  + while( iTERS = lEN %/rATE8 /\ 0<= i /\ i <= iTERS /\ _buf + _lEN < W64.modulus /\ lEN <= _lEN /\
           valid trace___pabsorb_imem_avx2 /\ is_init b_st 0 224 /\  0<=buf /\ buf < W64.modulus /\
           0<=tRAILB /\ tRAILB < 256 /\ ( i<iTERS => rATE8 *  i < lEN - lEN%%rATE8) /\
           0<rATE8 /\ rATE8 <200 /\ 0<=_buf /\
           is_valid ptr_modulus Glob.mem_v buf (lEN - (i)*rATE8)).
    + auto.  
      ecall (_keccakf1600_avx2_trace param_21 (BArray224.init_arr (W8.of_int 255) 224)). auto .
      ecall (__addstate_imem_avx2_trace param_25 (BArray224.init_arr (W8.of_int 255) 224) param_24 param_23 param_22). auto .
      rewrite /valid /=.
      move => &m /> *.
      split. smt(BArray224.init_arrP).
      move => 4? r *. 
      split. smt(BArray224.init_arrP).
      move => *. split. smt(). split. rewrite !all_cat /=. smt().
      rewrite -divzE. smt().
    auto. if.
    + auto.
      ecall (_keccakf1600_avx2_trace param_26 (BArray224.init_arr (W8.of_int 255) 224)). auto .
      ecall (_addpstate_avx2_trace param_28 (BArray224.init_arr (W8.of_int 255) 224) param_27 (BArray200.init_arr (W8.of_int 255) 200)). auto .
      ecall (__pstate_imem_avx2_trace param_33 (BArray200.init_arr (W8.of_int 255) 200) param_32 param_31 param_30  param_29). auto . 
      move => &m /> *.
      split. smt( BArray200.init_arrP). move => 8? r *.
      split. smt(BArray224.init_arrP). move => *.
      split.  smt(all_cat).
      move => buf0 i 8?  h1.
      have h2: (i * rATE8{m} = lEN{m} - (rATE8{m} - aT{m}) - (lEN{m} - (rATE8{m} - aT{m}))%%rATE8{m}). smt(). rewrite h2 /=. 
      have h3:((lEN{m} - (rATE8{m} - aT{m}) -
    (lEN{m} - (rATE8{m} - aT{m}) - (lEN{m} - (rATE8{m} - aT{m})) %% rATE8{m})) = (lEN{m} - rATE8{m} + aT{m}) %% rATE8{m}).  smt(). rewrite h3 /=. have /= ? := modzMDr (-1) (lEN{m} + aT{m}) (rATE8{m}).
      smt().
    auto.
    move => &m />  *.
    smt(all_cat).
  if.
  + auto.
    ecall (__addratebit_avx2_trace param_11 (BArray224.init_arr (W8.of_int 255) 224) param_10).
    auto .
    ecall (__addstate_imem_avx2_trace param_15 (BArray224.init_arr (W8.of_int 255) 224) param_14 param_13 param_12).
    auto . 
    smt(BArray224.init_arrP BArray200.init_arrP all_cat).
  if.    
  + auto.
    ecall (__pstate_imem_avx2_trace param_20 (BArray200.init_arr (W8.of_int 255) 200) param_19 param_18 param_17 param_16). auto.
    move => &m /> 2? h *.  smt(BArray224.init_arrP BArray200.init_arrP all_cat).
  auto.  smt(BArray224.init_arrP BArray200.init_arrP all_cat).
qed .

lemma __dumpstate_imem_avx2_trace _buf _lEN _st _b_st :
      hoare [M.__dumpstate_imem_avx2 :
      (((_b_st = b_st) /\ ((_st = st) /\ ((_lEN = lEN) /\ (_buf = buf)))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      ((((0 <= _lEN) /\ (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
       (is_init _b_st 0 224)) /\
      (_lEN <= 200))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf + _lEN)) /\ ((_buf + _lEN) <= 18446744073709551615)) /\
       (res.`1 = (_buf + _lEN))))) /\
      (valid res.`2))].
proof.
 proc. rewrite /=.
  seq 3: (#pre /\ valid trace___dumpstate_imem_avx2). by auto.
  case (_lEN < 8).
  + if. exfalso. smt().
    seq 18: ( lEN = 0 /\ valid trace___dumpstate_imem_avx2 /\ buf = _buf +  _lEN /\ 0<=buf /\ buf < W64.modulus /\ 0 <= _buf /\ 0 <= _lEN).
    + auto. ecall ( __mwrite_subu256_trace param_25 param_24 param_23). auto.
      ecall (__mwrite_subu256_trace param_31 param_30 param_29). auto. 
      move => &m /> *.
      smt(all_cat).
    if. exfalso. smt().
    auto. smt().
  seq 1: ( valid trace___dumpstate_imem_avx2 /\ 0 <= _lEN /\ _lEN <= 200 /\ 8<=_lEN /\  0<=buf /\ buf < W64.modulus /\ 0 <= _buf /\
           is_valid ptr_modulus Glob.mem_v _buf _lEN  /\ lEN = _lEN - 8 /\ buf = _buf +  8).
  + if.
    + auto . ecall(__mwrite_subu256_trace param_28 param_27 param_26). auto.
      smt(all_cat).
    exfalso. smt().
  case (lEN <= 32).  
  + seq 9: ( lEN = 0 /\ valid trace___dumpstate_imem_avx2 /\ buf = _buf + _lEN /\  0<=buf /\ buf < W64.modulus  /\ 0 <= _buf /\ 0 <= _lEN).
    + auto.  ecall ( __mwrite_subu256_trace param_25 param_24 param_23). auto. 
      move => &m />  *.
      smt(all_cat).
    if. exfalso. smt().
    auto. move => /> *. smt().
  seq 9: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 40<_lEN /\ buf < W64.modulus  /\ 0 <= _buf /\
           is_valid ptr_modulus Glob.mem_v _buf _lEN  /\ lEN = _lEN - 40 /\ buf = _buf + 40).
  + auto. ecall(__mwrite_subu256_trace param_25 param_24 param_23). auto.
    move => &m  />  *.
    smt(all_cat).
  if.
  + case (lEN <= 8).
    + seq 13: ( lEN = 0 /\ valid trace___dumpstate_imem_avx2 /\ buf = _buf + _lEN /\ 0<=buf /\ buf < W64.modulus  /\ 0 <= _buf /\ 0 <= _lEN).
      + auto. ecall( __mwrite_subu64_trace param_22 param_21 param_20). auto. 
        move => &m /> *.
        smt(all_cat).
      if. exfalso. smt().
      auto. smt().
    seq 13: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 48<_lEN /\  buf < W64.modulus
         /\ 0 <= _buf /\ is_valid ptr_modulus Glob.mem_v _buf _lEN  /\ lEN = _lEN - 48 /\ buf = _buf +  48).
    + auto. ecall( __mwrite_subu64_trace param_22 param_21 param_20). auto. 
      move => &m /> *.
      smt(all_cat).
    if.
    pose len_48 := (_lEN - 48).
    + seq 5: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 
               is_valid ptr_modulus Glob.mem_v _buf _lEN  /\ 0 <= _buf /\
               0  <= _lEN /\ buf = _buf + (if len_48 <= 32 then _lEN else 80) /\
              lEN = (if len_48 <= 32 then 0 else _lEN - 80)).
      + sp. if.
        + auto. ecall(__mwrite_subu256_trace param_19 param_18 param_17). auto.
          move => &m /> *.
          smt(all_cat).
        by auto.
      pose len_80 := (_lEN - 80).
      seq 1: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 
              is_valid ptr_modulus Glob.mem_v  _buf _lEN  /\ 0 <= _buf /\
              0  <= _lEN /\ buf = _buf + (if len_80 <= 8 then _lEN else 88) /\
              lEN = (if len_80 <= 8 then 0 else _lEN - 88)).
      + if. auto.
        +  ecall( __mwrite_subu64_trace param_16 param_15 param_14).  auto.
           move => &m /> *.
           smt(all_cat).
        auto. smt().
      pose len_88 := (_lEN - 88).
      seq 1: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 
              is_valid ptr_modulus Glob.mem_v _buf _lEN  /\  0 <= _buf /\
              0  <= _lEN /\ buf = _buf + (if len_88 <= 32 then _lEN else 120) /\
              lEN = (if len_88 <= 32 then 0 else _lEN - 120)).
      + if. auto. ecall( __mwrite_subu256_trace param_13 param_12 param_11). auto.
        + move => &m /> *.
          smt(all_cat).
        auto. smt().
      pose len_120 := (_lEN - 120).
      seq 1: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 
              is_valid ptr_modulus Glob.mem_v  _buf _lEN  /\  0 <= _buf /\
              0  <= _lEN /\ buf = _buf + (if len_120 <= 8 then _lEN else 128) /\
              lEN = (if len_120 <= 8 then 0 else _lEN - 128)).
      + if. auto. ecall( __mwrite_subu64_trace param_10 param_9 param_8). auto.
        + move => &m /> *.
          smt(all_cat).
        auto. smt().
      pose len_128 := (_lEN - 128).
      seq 1: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 
              is_valid ptr_modulus Glob.mem_v  _buf _lEN  /\ 0 <= _buf /\
              0  <= _lEN /\ buf = _buf + (if len_128 <= 32 then _lEN else 160) /\
              lEN = (if len_128 <= 32 then 0 else _lEN - 160)).
      + if. auto. ecall( __mwrite_subu256_trace param_7 param_6 param_5). auto.
        + move => &m /> *.
          smt(all_cat).
        auto. smt().
      pose len_160 := (_lEN - 160).
      seq 1: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\ 
              is_valid ptr_modulus Glob.mem_v _buf _lEN  /\ 0 <= _buf /\
              0  <= _lEN /\ buf = _buf + (if len_160 <= 8 then _lEN else 168) /\
              lEN = (if len_160 <= 8 then 0 else _lEN - 168)).
      + if. auto. ecall( __mwrite_subu64_trace param_4 param_3 param_2). auto.
        + move => &m /> *.
          smt(all_cat).
        auto. smt().
      pose len_168 := (_lEN - 168).
      seq 1: ( valid trace___dumpstate_imem_avx2 /\ _lEN <= 200 /\  0 <= _buf /\ 0<=_lEN /\
              is_valid ptr_modulus Glob.mem_v _buf _lEN  /\ buf = _buf + _lEN).
      + if. auto. ecall( __mwrite_subu256_trace param_1 param_0 param). auto.
        + move => &m /> *.
          smt(all_cat).
        auto. smt().
      auto. move => &m /> *.  smt().        
    auto. smt().
  auto. smt().
qed .

lemma __squeeze_imem_avx2_trace _buf _lEN _st _b_st _rATE8 :
      hoare [M.__squeeze_imem_avx2 :
      (((_rATE8 = rATE8) /\
       ((_b_st = b_st) /\ ((_st = st) /\ ((_lEN = lEN) /\ (_buf = buf))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((((0 <= _lEN) /\ (0 < _rATE8)) /\ (_rATE8 < 200)) /\
       (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
      (is_init _b_st 0 224))))) ==>
      ((((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf + _lEN)) /\ ((_buf + _lEN) <= 18446744073709551615)) /\
       ((res.`1 = (_buf + _lEN)) /\ (is_init res.`3 0 224))))) /\
      (valid res.`4))].
proof.
  proc; rewrite /= .
  seq 11: (#pre /\ valid trace___squeeze_imem_avx2). by auto.
  sp.
  if .
  + seq 1: ( 0<=_lEN /\ 0<=_buf /\ is_init b_st 0 224 /\ valid trace___squeeze_imem_avx2 /\
             0 < rATE8 /\ rATE8 < 200 /\
            lO = _lEN %% rATE8 /\ buf = _buf + _lEN - _lEN%%rATE8 /\
            is_valid ptr_modulus Glob.mem_v buf lO).
    + if.
      + auto .
        while ((valid trace___squeeze_imem_avx2) /\  0<=_lEN /\ 0<=_buf /\ is_init b_st 0 224 /\
               lO = _lEN %% _rATE8 /\ buf = _buf + i*rATE8 /\ 0<= i /\ i <= _lEN %/ rATE8 /\
               is_valid ptr_modulus Glob.mem_v _buf _lEN /\ i * rATE8 <= _lEN
                /\ 0 < rATE8 /\ rATE8 < 200 /\ 
               (i<iTERS => rATE8 *  i < rATE8 * (_lEN %/ rATE8)) /\ iTERS = _lEN%/rATE8).
        + auto.
          ecall (__dumpstate_imem_avx2_trace param_5 param_4 param_3 (BArray224.init_arr (W8.of_int 255) 224)). auto .
          ecall (_keccakf1600_avx2_trace param_6 (BArray224.init_arr (W8.of_int 255) 224)). auto.
          rewrite /valid /=. move => &m => /> *.
          split. smt(BArray224.init_arrP).
          move => *. split.  smt().
          move => *. split. rewrite !all_cat /=. smt().
          split. smt(). split. smt(). split. smt(). split. smt(). smt().
        auto. rewrite /valid /=. move => &m />  *.
        smt(all_cat ).
      auto. rewrite /valid /=. move => &m />  *.
      smt().
    if.
    + auto. ecall (__dumpstate_imem_avx2_trace param_1 param_0 param (BArray224.init_arr (W8.of_int 255) 224)).
      auto . ecall (_keccakf1600_avx2_trace param_2 (BArray224.init_arr (W8.of_int 255) 224)). 
      auto . rewrite /valid /=. move => &m /> *.
      smt(BArray224.init_arrP all_cat).
    auto. rewrite /valid /=. move => &m /> *.
    smt(BArray224.init_arrP).
  auto. smt(BArray224.init_arrP).
qed .

lemma keccakf1600_4x_theta_sum_trace _a _b_a :
      hoare [M.keccakf1600_4x_theta_sum :
      (((_b_a = b_a) /\ (_a = a)) /\ (is_init _b_a 0 800)) ==>
      ((is_init res.`2 0 160) /\ (valid res.`3))].
proof.
proc; auto .
  while(is_init b_c 0 (32*5) /\ 0<=y /\ is_init b_a 0 800 /\ valid trace_keccakf1600_4x_theta_sum).
  + auto.
    while(is_init b_c 0 (32*5) /\ 0<=y /\ is_init b_a 0 800 /\
          valid trace_keccakf1600_4x_theta_sum /\ 0<=x  /\ y<5);
    auto; rewrite /is_init /valid  /=; smt(all_cat).
  auto.
  while(is_init b_c 0 (32*x) /\ 0<=x /\ x<=5 /\  is_init b_a 0 800 /\ valid trace_keccakf1600_4x_theta_sum);
  auto; rewrite /is_init  /valid /=; smt(all_cat).
qed .


lemma keccakf1600_4x_rol_trace _a _b_a _x _r _r8 _r56 :
      hoare [M.keccakf1600_4x_rol :
      (((_r56 = r56) /\
       ((_r8 = r8) /\ ((_r = r) /\ ((_x = x) /\ ((_b_a = b_a) /\ (_a = a)))))) /\
      (((is_init _b_a (_x * 32) 32) /\ (0 <= _x)) /\ (_x < 5))) ==>
      ((foldr (fun x => (fun acc => (x /\ acc))) true
       (map (fun k => ((is_init res.`2 k 1) = (is_init _b_a k 1)))
       (iota_ 0 160))) /\
      (valid res.`3))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat and_iota).
qed .

lemma keccakf1600_4x_theta_rol_trace _c _b_c _r8 _r56 :
      hoare [M.keccakf1600_4x_theta_rol :
      (((_r56 = r56) /\ ((_r8 = r8) /\ ((_b_c = b_c) /\ (_c = c)))) /\
      (is_init _b_c 0 160)) ==> ((is_init res.`2 0 160) /\ (valid res.`3))].
proof.
proc; auto .
while ((valid trace_keccakf1600_4x_theta_rol) /\ is_init b_c 0 160 /\ is_init b_d 0 (x*32) /\ 0<=x /\ x<=5).
auto .
ecall (keccakf1600_4x_rol_trace param_3 b_param param_2 param_1 param_0 param).
auto .
rewrite /is_init /valid /= => &m /> *.
smt (all_cat and_iota).
auto .
rewrite /is_init /valid /= .
smt (all_cat and_iota).
qed .

lemma keccakf1600_4x_rol_sum_trace _a _b_a _d _b_d _y _r8 _r56 :
      hoare [M.keccakf1600_4x_rol_sum :
      (((_r56 = r56) /\
       ((_r8 = r8) /\
       ((_y = y) /\
       ((_b_d = b_d) /\ ((_d = d) /\ ((_b_a = b_a) /\ (_a = a))))))) /\
      ((((is_init _b_a 0 800) /\ (is_init _b_d 0 160)) /\ (0 <= _y)) /\
      (_y < 5))) ==> ((is_init res.`2 0 160) /\ (valid res.`3))].
proof.
  proc; auto .
  while(is_init b_b 0 (x*32) /\ 0 <= x /\ x <= 5 /\ valid trace_keccakf1600_4x_rol_sum).
  + seq 17: (is_init b_b 0 ((x+1)*32) /\ 0 <= x /\ x < 5 /\ valid trace_keccakf1600_4x_rol_sum).
    + auto . ecall (keccakf1600_rhotates_trace param_5 param_4). auto. 
      rewrite /is_init /valid /= .
      smt (all_cat).
    if .
    + auto . ecall (keccakf1600_4x_rol_trace param_3 b_param param_2 param_1 param_0 param).
      auto . rewrite /is_init /valid /= => &m /> *.
      smt (all_cat and_iota).
    auto .
    rewrite /is_init /valid /=.
    smt (all_cat).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
qed .

lemma keccakf1600_4x_set_row_trace _e _b_e _b _b_b _y _rc :
      hoare [M.keccakf1600_4x_set_row :
      (((_rc = rc) /\
       ((_y = y) /\
       ((_b_b = b_b) /\ ((_b = b) /\ ((_b_e = b_e) /\ (_e = e)))))) /\
      (((is_init _b_b 0 160) /\ (0 <= _y)) /\ (_y < 5))) ==>
      ((foldr (fun x => (fun acc => (x /\ acc))) true
       (map
       (fun k =>
       ((is_init res.`2 k 1) =
       ((is_init _b_e k 1) \/
       ((((_y * 5) * 32) <= k) /\ (k < (((_y + 1) * 5) * 32))))))
       (iota_ 0 800))) /\
      (valid res.`3))].
proof.
proc;auto.
  while(is_init b_e (32*y*5) (32*x) /\ 0 <= x /\ x <= 5 /\ valid trace_keccakf1600_4x_set_row /\ 0<=y /\ y<5 /\ forall k, (k < (32*y*5) \/ (32*(y+1)*5) <= k) => is_init b_e k 1 = is_init _b_e k 1).
  + auto. rewrite /is_init /valid /trace /=. smt(all_cat).
  auto. rewrite /is_init /valid /trace /= => &m /> *.
  smt(and_iota).
qed .

lemma _keccakf1600_4x_round_trace _e _b_e _a _b_a _rc _r8 _r56 :
      hoare [M._keccakf1600_4x_round :
      (((_r56 = r56) /\
       ((_r8 = r8) /\
       ((_rc = rc) /\
       ((_b_a = b_a) /\ ((_a = a) /\ ((_b_e = b_e) /\ (_e = e))))))) /\
      (is_init _b_a 0 800)) ==> ((is_init res.`2 0 800) /\ (valid res.`3))].
proof.
proc; auto .
  while(is_init b_e 0 (y*160) /\ 0<=y /\ y<=5 /\ valid  trace__keccakf1600_4x_round).
  + auto . ecall (keccakf1600_4x_set_row_trace param_2 b_param param_1 (BArray160.init_arr (W8.of_int 255) 160) param_0 param). auto.
    ecall (keccakf1600_4x_rol_sum_trace param_7 (BArray800.init_arr (W8.of_int 255) 800) param_6 (BArray160.init_arr (W8.of_int 255) 160) param_5 param_4 param_3). auto .
    rewrite /is_init /valid /= => &m /> *.
    smt (all_cat and_iota BArray800.init_arrP BArray160.init_arrP).
  auto .
  ecall (keccakf1600_4x_theta_rol_trace param_10 (BArray160.init_arr (W8.of_int 255) 160) param_9 param_8).
  auto .
  ecall (keccakf1600_4x_theta_sum_trace param_11 (BArray800.init_arr (W8.of_int 255) 800)).
  auto .
  rewrite /is_init /valid /= .
  smt (all_cat BArray800.init_arrP BArray160.init_arrP).
qed .

lemma __keccakf1600_avx2x4_trace _a _b_a :
      hoare [M.__keccakf1600_avx2x4 :
      (((_b_a = b_a) /\ (_a = a)) /\ (is_init _b_a 0 800)) ==>
      ((is_init res.`2 0 800) /\ (valid res.`3))].
proof.
proc; auto .
while ((valid trace___keccakf1600_avx2x4) /\ is_init b_a 0 800 /\ 0 <=  c /\ ( c) %% 2 = 0).
auto .
ecall (_keccakf1600_4x_round_trace param_3 b_param_0 param_2 b_param param_1 
       param_0 param).
auto .
ecall (_keccakf1600_4x_round_trace param_8 b_param_1 param_7 (BArray800.init_arr (W8.of_int 255) 800)
       param_6 param_5 param_4).
auto .
rewrite /is_init /valid /swap_ /= => &m /> *. 
smt (all_cat BArray800.init_arrP).
auto . smt(BArray800.init_arrP).
qed .

lemma _keccakf1600_avx2x4_trace _a _b_a :
      hoare [M._keccakf1600_avx2x4 :
      (((_b_a = b_a) /\ (_a = a)) /\ (is_init _b_a 0 800)) ==>
      ((is_init res.`2 0 800) /\ (valid res.`3))].
proof.
proc; auto .
ecall (__keccakf1600_avx2x4_trace param (BArray800.init_arr (W8.of_int 255)
                                        800)).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray800.init_arrP).
qed .

lemma _keccakf1600_avx2x4__trace _a _b_a :
      hoare [M._keccakf1600_avx2x4_ :
      (((_b_a = b_a) /\ (_a = a)) /\ (is_init _b_a 0 800)) ==>
      ((is_init res.`2 0 800) /\ (valid res.`3))].
proof.
proc; auto .
ecall (_keccakf1600_avx2x4_trace param (BArray800.init_arr (W8.of_int 255)
                                       800)).
auto .
rewrite /is_init /valid /= .
smt (all_cat BArray800.init_arrP).
qed .



lemma __state_init_avx2x4_trace _st _b_st :
      hoare [M.__state_init_avx2x4 :
      (((_b_st = b_st) /\ (_st = st)) /\ true) ==>
      ((is_init res.`2 0 800) /\ (valid res.`3))].
proof.
proc; auto .
while ((valid trace___state_init_avx2x4) /\  ((((0 <= i) /\ (i <= 800)) /\
                                              ((i %% 32) = 0)) /\
                                             (is_init b_st 0 i))).
auto .
rewrite /is_init /valid /=.
smt (all_cat).
auto .
rewrite /is_init /valid /= .
smt (all_cat).
qed .

lemma __addratebit_avx2x4_trace _st _b_st _rATE8 :
      hoare [M.__addratebit_avx2x4 :
      (((_rATE8 = rATE8) /\ ((_b_st = b_st) /\ (_st = st))) /\
      (((is_init _b_st 0 800) /\ (0 < _rATE8)) /\ (_rATE8 < 200))) ==>
      ((is_init res.`2 0 800) /\ (valid res.`3))].
proof.
proc; auto .
rewrite /is_init /valid /= .
smt (all_cat BArray800.init_arrP).
qed .

lemma __u256x4_4u64x4_trace _x0 _x1 _x2 _x3 :
      hoare [M.__u256x4_4u64x4 :
      (((_x3 = x3) /\ ((_x2 = x2) /\ ((_x1 = x1) /\ (_x0 = x0)))) /\ true) ==>
      (true /\ (valid res.`5))].
proof.
by proc; auto .
qed .

lemma __4u64x4_u256x4_trace _y0 _y1 _y2 _y3 :
      hoare [M.__4u64x4_u256x4 :
      (((_y3 = y3) /\ ((_y2 = y2) /\ ((_y1 = y1) /\ (_y0 = y0)))) /\ true) ==>
      (true /\ (valid res.`5))].
proof.
by proc; auto .
qed .


lemma __addstate_bcast_imem_avx2x4_trace _st _b_st _aT _buf _lEN _tRAILB :
      hoare [M.__addstate_bcast_imem_avx2x4 :
      (((_tRAILB = tRAILB) /\
       ((_lEN = lEN) /\
       ((_buf = buf) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st)))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      ((((((0 <= _lEN) /\ (0 <= _aT)) /\ (_aT < 200)) /\
        (((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)) < 200)) /\
       (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
      (is_init _b_st 0 800)))))) ==>
      ((((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf + _lEN)) /\ ((_buf + _lEN) <= 18446744073709551615)) /\
       (((is_init res.`2 0 800) /\
        (res.`3 = ((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)))) /\
       (res.`4 = (_buf + _lEN)))))) /\
      (valid res.`5))].
proof.
  proc. auto. 
  seq 4: (#pre /\ valid trace___addstate_bcast_imem_avx2x4 ). by auto.
  seq 5: ( valid trace___addstate_bcast_imem_avx2x4 /\ 0<=lEN /\
           is_valid ptr_modulus Glob.mem_v buf lEN /\ aT + lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\
           is_valid ptr_modulus Glob.mem_v _buf _lEN /\  aT%%8 = 0 /\
           0 <= _tRAILB /\ _tRAILB < 256 /\
           (if 0<lO /\ lO + _lEN < 8 then true else aT + lEN = _aT + _lEN) /\
           0<=_aT /\ _aT < 200 /\
           at = (if 0 < lO /\ lO + _lEN < 8 then 32*(_aT%/8) else 32*(aT%/8)) /\
           tRAILB = (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\
           aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
           lO = _aT %% 8 /\ lEN <= _lEN  /\ buf + lEN = _buf + _lEN).
  + sp.
    if. 
    + if.
      + auto.
        ecall (__mread_bcast_4subu64_trace param_4 param_3 param_2). 
        auto. rewrite /valid /= => &m /> *. smt(all_cat).
      if. auto. rewrite /valid /= => &m /> *. smt(all_cat).
      auto.
      ecall(__mread_bcast_4subu64_trace param_7 param_6 param_5).
      auto.  rewrite /valid /= => &m /> *. smt(all_cat).
    auto. smt(all_cat).   
  seq 1: ( valid trace___addstate_bcast_imem_avx2x4 /\ 0<=at /\
             is_valid ptr_modulus Glob.mem_v buf (lEN%%8) /\ aT%%8 = 0
             /\ is_valid ptr_modulus Glob.mem_v _buf _lEN /\
           at + 32 <= 800 /\ buf = _buf + _lEN - lEN%%8 /\ 0 <= _tRAILB /\ _tRAILB < 256 /\
           tRAILB = (if 0 < _aT%%8 /\ _aT%%8 + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\
           lEN <= _lEN /\ 0<=lEN /\
           aLL = _aT + _lEN + (if 0 < _aT%%8 /\ _aT%%8 + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0)).
  + if. auto.
    + while (valid trace___addstate_bcast_imem_avx2x4  /\ 0<=at /\ 0 <= _tRAILB /\ _tRAILB < 256 /\
             is_valid ptr_modulus Glob.mem_v _buf _lEN /\ aT%%8 = 0 /\ 0<=lEN /\
             aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
             lO = _aT %% 8 /\ lEN <= _lEN /\  aT + lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\
             tRAILB = (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\
             buf = _buf + _lEN - ((32 * (aT %/ 8) + 32 * (lEN %/ 8) - at)%/4) - lEN%%8 /\ 0 <=(at - 32 * (aT %/ 8)) %/ 4 
             /\ at <= 32 * (aT %/ 8) + 32 * (lEN %/ 8) /\ at%%32 = 0).
      + auto. rewrite /valid /= => &m /> *. smt(all_cat). 
      auto. rewrite /valid /= => &m /> *. split. split; smt(all_cat).  smt().
  auto. rewrite /valid /= => &m /> *. smt().
  auto. sp. if.
  + auto. ecall (__mread_bcast_4subu64_trace param_1 param_0 param).
    auto. rewrite /valid /= => &m /> *.  smt(BArray800.init_arrP all_cat). 
  auto. rewrite /valid /= => &m /> *. smt(BArray800.init_arrP). 
qed .


       
lemma __absorb_bcast_imem_avx2x4_trace _st _b_st _aT _buf _lEN _rATE8 _tRAILB :
      hoare [M.__absorb_bcast_imem_avx2x4 :
      (((_tRAILB = tRAILB) /\
       ((_rATE8 = rATE8) /\
       ((_lEN = lEN) /\
       ((_buf = buf) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st))))))) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf) /\ (_buf <= 18446744073709551615)) /\
      ((((((((0 <= _lEN) /\ (0 <= _aT)) /\ (_aT < _rATE8)) /\
          (((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)) < 200)) /\
         (0 < _rATE8)) /\
        (_rATE8 < 200)) /\
       (is_valid ptr_modulus Glob.mem_v _buf _lEN)) /\
      (is_init _b_st 0 800)))))) ==>
      ((((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       ((is_init res.`2 0 800) /\
       (res.`3 = ((_aT + _lEN)%%_rATE8 + ((_tRAILB <> 0) ? 1 : 0))))) /\
      (valid res.`5))].
proof.
proc. rewrite /= .
  seq 28: (#pre /\ valid trace___absorb_bcast_imem_avx2x4) . by auto.
  sp.
  if .
  + seq 12:( valid trace___absorb_bcast_imem_avx2x4 /\ is_init b_st 0 224 /\ 0<rATE8 /\ rATE8 <200 /\ 0<=aT /\ aT < 200 /\ 0<=buf /\ buf < W64.modulus /\ aT = (_aT + _lEN)%%_rATE8 + if _tRAILB <> 0 then 1 else 0).
    + auto. ecall (__addstate_bcast_imem_avx2x4_trace param_5                                     
(BArray800.init_arr (W8.of_int 255) 800) param_4 param_3 param_2 param_1). auto.
      smt(all_cat BArray800.init_arrP).
    if. auto.
    + ecall(__addratebit_avx2x4_trace param_0 (BArray800.init_arr (W8.of_int 255) 800) param).
      auto. rewrite /is_init => &m /> *. smt(all_cat BArray800.init_arrP).
    auto. smt(all_cat BArray800.init_arrP).
  seq 18: ( valid trace___absorb_bcast_imem_avx2x4 /\ 
           aT = (_aT + _lEN)%%_rATE8 + (if _tRAILB <> 0 then 1 else 0) /\
  0<=buf /\ buf < W64.modulus /\ 0<rATE8 /\ rATE8 <200). auto. 
  + ecall( __addstate_bcast_imem_avx2x4_trace param_12 (BArray800.init_arr (W8.of_int 255) 800)
          param_11 param_10 param_9  param_8). auto. 
    while( valid trace___absorb_bcast_imem_avx2x4 /\  0<=buf /\ buf < W64.modulus /\
           0<rATE8 /\ rATE8 <200 /\ rATE8 * iTERS <= lEN /\
           iTERS = lEN %/rATE8 /\ 0<= i /\ i <= iTERS /\ _buf + _lEN < W64.modulus /\ lEN <= _lEN /\
           0<=tRAILB /\ tRAILB < 256 /\ _lEN < 200 /\
           is_valid ptr_modulus Glob.mem_v buf ((iTERS - i)*rATE8 +  aLL%%rATE8)).
    + auto. ecall(_keccakf1600_avx2x4_trace param_13 (BArray800.init_arr (W8.of_int 255) 800)).
      auto. ecall(__addstate_bcast_imem_avx2x4_trace param_18 (BArray800.init_arr (W8.of_int 255) 800) param_17 param_16 param_15 param_14). auto. 
      rewrite /valid /= => &m /> *.
      have ?: (rATE8{m} <= ((lEN{m} %/ rATE8{m} - i{m}) * rATE8{m} + aLL{m} %% rATE8{m})).
      have ?: (0 < (lEN{m} %/ rATE8{m} - i{m})). smt(). have ?:(rATE8{m} <=(lEN{m} %/ rATE8{m} - i{m}) * rATE8{m}); smt(). split. smt(BArray800.init_arrP all_cat). 
      move => *. rewrite !all_cat /=. split; smt().
    auto.
    if. 
    + auto. ecall(_keccakf1600_avx2x4_trace param_19 (BArray800.init_arr (W8.of_int 255) 800)). 
      auto. ecall(__addstate_bcast_imem_avx2x4_trace param_24                                      
(BArray800.init_arr (W8.of_int 255) 800) param_23 param_22 param_21 param_20). auto. 
      rewrite /valid => /= &m /> *. split. smt(BArray800.init_arrP). 
      move => /> *.
      have h1: ((lEN{m} - (rATE8{m} - aT{m})) %% rATE8{m} = (lEN{m} + aT{m} - rATE8{m}) %% rATE8{m}). smt().
      have h2:((lEN{m} + aT{m} - rATE8{m}) %% rATE8{m} = (lEN{m} + aT{m}) %% rATE8{m}). 
      have /= ? := modzMDr (-1) (lEN{m} + aT{m}) (rATE8{m}). smt().
      split. split. rewrite !all_cat /=. smt(). split. smt().  split. smt().  split. smt().  split. smt(). split.       smt(). split. rewrite divzE /=. move => ?.  move => ?.  rewrite h1 h2.  smt().
      rewrite divzE h1 h2. smt().
      move => *. split. smt().  move => *. split. smt(all_cat). smt().
    auto. move => /> *. smt(all_cat BArray800.init_arrP).
  auto. if.
  + auto. ecall(__addratebit_avx2x4_trace param_7 (BArray800.init_arr (W8.of_int 255) 800) param_6).
    auto. smt(BArray800.init_arrP all_cat).
  auto. smt(BArray800.init_arrP).
qed .

lemma __addstate_imem_avx2x4_trace _st _b_st _aT _buf0 _buf1 _buf2 _buf3 _lEN _tRAILB :
      hoare [M.__addstate_imem_avx2x4 :
      (((_tRAILB = tRAILB) /\
       ((_lEN = lEN) /\
       ((_buf3 = buf3) /\
       ((_buf2 = buf2) /\
       ((_buf1 = buf1) /\
       ((_buf0 = buf0) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st))))))))) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      (((((((((0 <= _lEN) /\ (0 <= _aT)) /\ (_aT < 200)) /\
           (((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)) < 200)) /\
          (is_valid ptr_modulus Glob.mem_v _buf0 _lEN)) /\
         (is_valid ptr_modulus Glob.mem_v _buf1 _lEN)) /\
        (is_valid ptr_modulus Glob.mem_v _buf2 _lEN)) /\
       (is_valid ptr_modulus Glob.mem_v _buf3 _lEN)) /\
      (is_init _b_st 0 800)))))))))))) ==>
      ((((0 <= res.`7) /\ (res.`7 <= 18446744073709551615)) /\
       (((0 <= res.`6) /\ (res.`6 <= 18446744073709551615)) /\
       (((0 <= res.`5) /\ (res.`5 <= 18446744073709551615)) /\
       (((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf0 + _lEN)) /\ ((_buf0 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf1 + _lEN)) /\ ((_buf1 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf2 + _lEN)) /\ ((_buf2 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf3 + _lEN)) /\ ((_buf3 + _lEN) <= 18446744073709551615)) /\
       ((((((is_init res.`2 0 800) /\
           (res.`3 = ((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)))) /\
          (res.`4 = (_buf0 + _lEN))) /\
         (res.`5 = (_buf1 + _lEN))) /\
        (res.`6 = (_buf2 + _lEN))) /\
       (res.`7 = (_buf3 + _lEN))))))))))))))) /\
      (valid res.`8))].
proof.
  proc; rewrite /=.
  seq 12: ( valid  trace___addstate_imem_avx2x4 /\ is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ is_valid ptr_modulus Glob.mem_v _buf2 _lEN
            /\ is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\ 0<=lEN /\ lEN<=_lEN /\
            aT%%8 = 0 /\  0 <= _tRAILB /\ _tRAILB < 256 /\
            aT + lEN + ((_tRAILB <> 0) ? 1 : 0) < 200 /\ 0<= _aT /\ _aT < 200 /\
            (if 0<lO /\ lO + _lEN < 8 then true else aT + lEN = _aT + _lEN) /\
            aT + lEN <= 200 /\ 0<=aT /\ aT < 200 /\
            at = (if 0 < lO /\ lO + _lEN < 8 then 4*(_aT%/8) else 4*(aT%/8)) /\
            tRAILB = (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\
            aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
            lO = _aT %% 8 /\
            buf0 = _buf0 + _lEN - lEN /\
            buf1 = _buf1 + _lEN - lEN /\
            buf2 = _buf2 + _lEN - lEN /\
            buf3 = _buf3 + _lEN - lEN). 
  + sp. if. 
    + if.
      + auto. ecall(__mread_subu64_trace param_17 param_16 param_15).
        auto. ecall(__mread_subu64_trace param_20 param_19 param_18).
        auto. ecall(__mread_subu64_trace param_23 param_22 param_21).
        auto. ecall(__mread_subu64_trace param_26 param_25 param_24).
        auto. rewrite /valid /= => &m /> *. split. move => *. split.  smt(). move => *.
        + split.  smt(). move => *. split. smt(). move => *.  split. smt(). move => *.  split. rewrite !all_cat /=. smt(). smt().
       move => *. split.  smt(). move => *.
       split.  smt(). move => *. split. smt(). move => *.  split. smt(). move => *.  split. rewrite !all_cat /=. smt(). smt().
      if. auto. rewrite /valid /= => &m /> *. smt(all_cat).
      auto.  ecall(__mread_subu64_trace param_29 param_28 param_27).
      auto. ecall(__mread_subu64_trace param_32 param_31 param_30).
      auto. ecall(__mread_subu64_trace param_35 param_34 param_33).
      auto. ecall(__mread_subu64_trace param_38 param_37 param_36).
      auto. rewrite /valid /= => &m /> *. split.  smt(). move => *. split. smt(). move => *. split. smt(). move => *. split. smt(). move => *. rewrite !all_cat /=. smt().
    auto. smt(all_cat).
  seq 2: (valid  trace___addstate_imem_avx2x4 /\ is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\
          is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ is_valid ptr_modulus Glob.mem_v _buf2 _lEN
          /\ is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\ 0<=lEN /\ lEN<=_lEN /\ 0<=at /\
          aT%%8 = 0 /\ lO = lEN /\ 
          at + 4 <= 100 /\ 0 <= _tRAILB /\ _tRAILB < 256 /\
          tRAILB = (if 0 < _aT%%8 /\ _aT%%8 + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\
          lEN < 8 /\
          aLL = _aT + _lEN + (if 0 < _aT%%8 /\ _aT%%8 + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
          buf0 = _buf0 + _lEN - lEN /\
          buf1 = _buf1 + _lEN - lEN /\
          buf2 = _buf2 + _lEN - lEN /\
          buf3 = _buf3 + _lEN - lEN).
  + if. auto.
    + while (valid  trace___addstate_imem_avx2x4 /\ is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\
          is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ is_valid ptr_modulus Glob.mem_v _buf2 _lEN
          /\ is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\ 0<=lEN /\ lEN<=_lEN /\ 0<=at /\
           0<=aT /\ 4 * (aT %/ 8) <= at /\
           aT%%8 = 0 /\ at%%4 = 0 /\  lO = _aT%%8 /\ at <=  4 * (aT %/ 8) + 4 * (lEN %/ 8) /\
           0 <= _tRAILB /\ _tRAILB < 256 /\ 
           tRAILB = (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\ 
           aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
            aT + lEN + ((_tRAILB <> 0) ? 1 : 0) <  200 /\
           buf0 = _buf0 + _lEN - ((4 * (aT %/ 8) + 4 * (lEN %/ 8) - at)* 2 + lEN%%8) /\
           buf1 = _buf1 + _lEN - ((4 * (aT %/ 8) + 4 * (lEN %/ 8) - at)* 2 + lEN%%8) /\ 
           buf2 = _buf2 + _lEN - ((4 * (aT %/ 8) + 4 * (lEN %/ 8) - at)* 2 + lEN%%8) /\
           buf3 = _buf3 + _lEN - ((4 * (aT %/ 8) + 4 * (lEN %/ 8) - at)* 2 + lEN%%8)
           ).
      + auto. rewrite /valid /= => &m /> *. smt(all_cat). auto.
      while (valid  trace___addstate_imem_avx2x4 /\ is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\
          is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ is_valid ptr_modulus Glob.mem_v _buf2 _lEN
          /\ is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\ 0<=lEN /\ lEN<=_lEN /\ 0<=at /\
           0<=aT /\ 4 * (aT %/ 8) <= at /\
           aT%%8 = 0 /\ (at - 4 * (aT %/ 8))%%16 = 0  /\ lO = _aT%%8 /\
           at <=  4 * (aT %/ 8) + 16 * (lEN %/ 32) /\
           0 <= _tRAILB /\ _tRAILB < 256 /\ 
           tRAILB = (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 0 else _tRAILB) /\ 
           aLL = _aT + _lEN + (if 0 < lO /\ lO + _lEN < 8 /\ _tRAILB <> 0 then 1 else 0) /\
           aT + lEN + ((_tRAILB <> 0) ? 1 : 0) <  200 /\
           buf0 = _buf0 + _lEN - ((4 * (aT %/ 8) + 16  * (lEN %/ 32) - at)*2 + lEN%%32) /\
           buf1 = _buf1 + _lEN - ((4 * (aT %/ 8) + 16  * (lEN %/ 32) - at)*2 + lEN%%32) /\ 
           buf2 = _buf2 + _lEN - ((4 * (aT %/ 8) + 16  * (lEN %/ 32) - at)*2 + lEN%%32) /\
           buf3 = _buf3 + _lEN - ((4 * (aT %/ 8) + 16  * (lEN %/ 32) - at)*2 + lEN%%32)
           ). auto. ecall(__4u64x4_u256x4_trace param_14 param_13 param_12 param_11). auto.
      + rewrite  /valid /= => &m /> *. split. move => *. rewrite !all_cat /=. smt(). smt().
      auto. rewrite  /valid /= => &m /> *. split. split; smt(all_cat).
      move => *. split. smt(all_cat). move => *. smt().
    auto.  rewrite /valid /= => &m /> *. smt().
  if.
  + auto. ecall(__mread_subu64_trace param_1 param_0 param).   
    auto. ecall(__mread_subu64_trace param_4 param_3 param_2).            
    auto. ecall(__mread_subu64_trace param_7 param_6 param_5).  
    auto. ecall(__mread_subu64_trace param_10 param_9 param_8).
    auto. rewrite /valid /= => &m /> *. split. smt(). move => *. split. smt(). move => *. split.  smt(). move => *.  split.  smt(). move => *. split. rewrite !all_cat /=. smt(BArray800.init_arrP). rewrite !all_cat /=. smt(BArray800.init_arrP).
  auto. rewrite  /valid /= => /> *.
  smt(all_cat BArray800.init_arrP).
qed.

            
lemma __absorb_imem_avx2x4_trace _st _b_st _aT _buf0 _buf1 _buf2 _buf3 _lEN _rATE8 _tRAILB :
      hoare [M.__absorb_imem_avx2x4 :
      (((_tRAILB = tRAILB) /\
       ((_rATE8 = rATE8) /\
       ((_lEN = lEN) /\
       ((_buf3 = buf3) /\
       ((_buf2 = buf2) /\
       ((_buf1 = buf1) /\
       ((_buf0 = buf0) /\ ((_aT = aT) /\ ((_b_st = b_st) /\ (_st = st)))))))))) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _tRAILB) /\ (_tRAILB < 256)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      (((((((((((0 <= _lEN) /\ (0 <= _aT)) /\ (_aT < _rATE8)) /\
             (0 < _rATE8)) /\
            (_rATE8 < 200)) /\
           (((_aT + _lEN) + ((_tRAILB <> 0) ? 1 : 0)) < 200)) /\
          (is_valid ptr_modulus Glob.mem_v _buf0 _lEN)) /\
         (is_valid ptr_modulus Glob.mem_v _buf1 _lEN)) /\
        (is_valid ptr_modulus Glob.mem_v _buf2 _lEN)) /\
       (is_valid ptr_modulus Glob.mem_v _buf3 _lEN)) /\
      (is_init _b_st 0 800)))))))))))) ==>
      ((((0 <= res.`7) /\ (res.`7 <= 18446744073709551615)) /\
       (((0 <= res.`6) /\ (res.`6 <= 18446744073709551615)) /\
       (((0 <= res.`5) /\ (res.`5 <= 18446744073709551615)) /\
       (((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       (is_init res.`2 0 800))))) /\
      (valid res.`8))].
proof.
  proc; rewrite /=.
  seq 31: (valid trace___absorb_imem_avx2x4 /\ #pre). by auto.
  sp. if.
  + seq 21: (valid trace___absorb_imem_avx2x4 /\ 0< rATE8 /\ rATE8 < 200 /\
             is_valid  ptr_modulus Glob.mem_v buf0 0 /\ is_valid  ptr_modulus Glob.mem_v buf1 0 /\
             is_valid  ptr_modulus Glob.mem_v buf2 0 /\is_valid  ptr_modulus Glob.mem_v buf3 0).
    + auto. ecall(__addstate_imem_avx2x4_trace param_8 (BArray800.init_arr (W8.of_int 255) 800)
                   param_7 param_6 param_5 param_4 param_3 param_2 param_1). auto.      
      rewrite /valid /= => &m /> *. smt(all_cat BArray800.init_arrP) .
    if. auto.
    + ecall(__addratebit_avx2x4_trace param_0 (BArray800.init_arr (W8.of_int 255) 800) param).
      auto.  rewrite /valid /= => &m /> *. smt(all_cat BArray800.init_arrP) .
    auto. smt(all_cat BArray800.init_arrP).
  seq 27: (valid trace___absorb_imem_avx2x4 /\ 0< rATE8 /\ rATE8 < 200 /\
           is_valid  ptr_modulus Glob.mem_v buf0 0 /\ is_valid  ptr_modulus Glob.mem_v buf1 0 /\
           is_valid  ptr_modulus Glob.mem_v buf2 0 /\is_valid  ptr_modulus Glob.mem_v buf3 0).
  + auto. ecall(__addstate_imem_avx2x4_trace param_18 (BArray800.init_arr (W8.of_int 255) 800)
                param_17 param_16 param_15 param_14 param_13 param_12 param_11).
    auto.
    while( valid trace___absorb_imem_avx2x4 /\ 0< rATE8 /\ rATE8 < 200 /\ 0<=i /\ i<=iTERS /\
           iTERS = lEN %/ rATE8 /\ rATE8 * iTERS <= lEN /\ aLL =_aT + _lEN /\ lEN <= _lEN /\
           lEN + (if tRAILB <> 0 then 1 else 0) < 200 /\ 0 <= lEN /\ 0<=tRAILB /\ tRAILB<256 /\
           is_valid ptr_modulus Glob.mem_v buf0 ((iTERS - i)*rATE8 +  aLL%%rATE8) /\
           is_valid ptr_modulus Glob.mem_v buf1 ((iTERS - i)*rATE8 +  aLL%%rATE8) /\
           is_valid ptr_modulus Glob.mem_v buf2 ((iTERS - i)*rATE8 +  aLL%%rATE8) /\
           is_valid ptr_modulus Glob.mem_v buf3 ((iTERS - i)*rATE8 +  aLL%%rATE8)).
    + auto. ecall(_keccakf1600_avx2x4_trace param_19 (BArray800.init_arr (W8.of_int 255) 800)).
      auto. ecall(__addstate_imem_avx2x4_trace param_27 (BArray800.init_arr (W8.of_int 255) 800)    
                  param_26 param_25 param_24 param_23 param_22 param_21 param_20). 
      auto. rewrite /valid  /= => &m /> *.
      have ?: (rATE8{m} <= (lEN{m} %/ rATE8{m} - i{m}) * rATE8{m} ). smt().
      split. smt(BArray800.init_arrP). move => *. rewrite !all_cat /=. smt(BArray800.init_arrP).
    if. 
    + auto. ecall(_keccakf1600_avx2x4_trace param_28 (BArray800.init_arr (W8.of_int 255) 800)).
      auto. ecall(__addstate_imem_avx2x4_trace param_36 (BArray800.init_arr (W8.of_int 255) 800)
                  param_35 param_34 param_33 param_32 param_31 param_30 param_29).
      auto. 
      rewrite /valid /= => &m /> *. split. smt(BArray800.init_arrP).
      move => *. 
      have: ((lEN{m} - (rATE8{m} - aT{m})) %/ rATE8{m} * rATE8{m} +
   (aT{m} + lEN{m}) %% rATE8{m} = lEN{m} - (rATE8{m} - aT{m}) ).
      + have h: ((lEN{m} - (rATE8{m} - aT{m})) %/ rATE8{m} * rATE8{m} = lEN{m} - (rATE8{m} - aT{m}) - (lEN{m} - (rATE8{m} - aT{m}))%%rATE8{m}). smt().  rewrite h.
        have h1: ((lEN{m} - (rATE8{m} - aT{m})) %% rATE8{m} = (lEN{m} + aT{m} - rATE8{m}) %% rATE8{m}). smt(). have h2:((lEN{m} + aT{m} - rATE8{m}) %% rATE8{m} = (lEN{m} + aT{m}) %% rATE8{m}). 
have /= ? := modzMDr (-1) (lEN{m} + aT{m}) (rATE8{m}). smt(). smt(). 
      move => *. split. rewrite !all_cat /=. smt(). move => *. split. smt(). move => *. split. rewrite !all_cat /=. smt(). smt().
    auto. rewrite /valid /= => &m /> *.  smt(all_cat BArray800.init_arrP). 
  auto. if.
  + auto.
    ecall(__addratebit_avx2x4_trace param_10 (BArray800.init_arr (W8.of_int 255) 800) param_9).
    auto. smt(all_cat BArray800.init_arrP).
  auto. smt(BArray800.init_arrP).
qed.
 
lemma __dumpstate_imem_avx2x4_trace _buf0 _buf1 _buf2 _buf3 _lEN _st _b_st :
      hoare [M.__dumpstate_imem_avx2x4 :
      (((_b_st = b_st) /\
       ((_st = st) /\
       ((_lEN = lEN) /\
       ((_buf3 = buf3) /\
       ((_buf2 = buf2) /\ ((_buf1 = buf1) /\ (_buf0 = buf0))))))) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\ lEN<= 200 /\
      ((((((0 <= _lEN) /\ (is_valid ptr_modulus Glob.mem_v _buf0 _lEN)) /\
         (is_valid ptr_modulus Glob.mem_v _buf1 _lEN)) /\
        (is_valid ptr_modulus Glob.mem_v _buf2 _lEN)) /\
       (is_valid ptr_modulus Glob.mem_v _buf3 _lEN)) /\
      (is_init _b_st 0 800))))))))))) ==>
      ((((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       (((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)) /\
       (((0 <= res.`2) /\ (res.`2 <= 18446744073709551615)) /\
       (((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf0 + _lEN)) /\ ((_buf0 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf1 + _lEN)) /\ ((_buf1 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf2 + _lEN)) /\ ((_buf2 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf3 + _lEN)) /\ ((_buf3 + _lEN) <= 18446744073709551615)) /\
       ((((res.`1 = (_buf0 + _lEN)) /\ (res.`2 = (_buf1 + _lEN))) /\
        (res.`3 = (_buf2 + _lEN))) /\
       (res.`4 = (_buf3 + _lEN))))))))))))))) /\
      (valid res.`5))].
proof.
  proc; rewrite /=.
  seq 11: ( valid trace___dumpstate_imem_avx2x4 /\ i = 8*(lEN %/ 8) /\ 0 <=_lEN /\
            is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\ lEN <= 200 /\
            is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ lEN = _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf2 _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\
            buf0 = _buf0 + _lEN - _lEN%%8 /\ buf1 = _buf1 + _lEN - _lEN%%8 /\
            buf2 = _buf2 + _lEN - _lEN%%8 /\ buf3 = _buf3 + _lEN - _lEN%%8).
  + auto. 
    while(valid trace___dumpstate_imem_avx2x4 /\ 0<=i /\ i<=8*(lEN %/ 8) /\ 0 <=_lEN /\
            is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\ lEN <= 200 /\
            is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ lEN = _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf2 _lEN /\  i%%8 = 0 /\
            is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\
            buf0 = _buf0 + i /\ buf1 = _buf1 + i /\
            buf2 = _buf2 + i /\ buf3 = _buf3 + i).
    + auto. rewrite /valid /=.  smt(all_cat).
    auto.
    while (valid trace___dumpstate_imem_avx2x4 /\ 0<=i /\ i<=32*(lEN %/ 32) /\ 0 <=_lEN /\
            is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\ lEN <= 200 /\
            is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ lEN = _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf2 _lEN /\  i%%32 = 0 /\
            is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\
            buf0 = _buf0 + i /\ buf1 = _buf1 + i /\
            buf2 = _buf2 + i /\ buf3 = _buf3 + i).
    + auto. ecall(__4u64x4_u256x4_trace param_14 param_13 param_12 param_11).
      auto. rewrite /valid /= => &m /> *. rewrite !all_cat /=. smt().
    auto. rewrite /valid /= => &m /> *. smt(all_cat).
  auto. if.
  + auto. ecall (__mwrite_subu64_trace param_1 param_0 param).
    auto. ecall (__mwrite_subu64_trace param_4 param_3 param_2).
    auto. ecall (__mwrite_subu64_trace param_7 param_6 param_5).
    auto. ecall (__mwrite_subu64_trace param_10 param_9 param_8).
    auto. rewrite /valid /= => &m /> *. smt(all_cat).
  auto. smt().
qed.

lemma __squeeze_imem_avx2x4_trace _buf0 _buf1 _buf2 _buf3 _lEN _st _b_st _rATE8 :
      hoare [M.__squeeze_imem_avx2x4 :
      (((_rATE8 = rATE8) /\
       ((_b_st = b_st) /\
       ((_st = st) /\
       ((_lEN = lEN) /\
       ((_buf3 = buf3) /\
       ((_buf2 = buf2) /\ ((_buf1 = buf1) /\ (_buf0 = buf0)))))))) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _buf0) /\ (_buf0 <= 18446744073709551615)) /\
      (((0 <= _buf1) /\ (_buf1 <= 18446744073709551615)) /\
      (((0 <= _buf2) /\ (_buf2 <= 18446744073709551615)) /\
      (((0 <= _buf3) /\ (_buf3 <= 18446744073709551615)) /\
      ((((((((0 <= _lEN) /\ (0 < _rATE8)) /\ (_rATE8 < 200)) /\
          (is_valid ptr_modulus Glob.mem_v _buf0 _lEN)) /\
         (is_valid ptr_modulus Glob.mem_v _buf1 _lEN)) /\
        (is_valid ptr_modulus Glob.mem_v _buf2 _lEN)) /\
       (is_valid ptr_modulus Glob.mem_v _buf3 _lEN)) /\
      (is_init _b_st 0 800))))))))))) ==>
      ((((0 <= res.`4) /\ (res.`4 <= 18446744073709551615)) /\
       (((0 <= res.`3) /\ (res.`3 <= 18446744073709551615)) /\
       (((0 <= res.`2) /\ (res.`2 <= 18446744073709551615)) /\
       (((0 <= res.`1) /\ (res.`1 <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf0 + _lEN)) /\ ((_buf0 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf1 + _lEN)) /\ ((_buf1 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf2 + _lEN)) /\ ((_buf2 + _lEN) <= 18446744073709551615)) /\
       (((0 <= _lEN) /\ (_lEN <= 18446744073709551615)) /\
       (((0 <= (_buf3 + _lEN)) /\ ((_buf3 + _lEN) <= 18446744073709551615)) /\
       (((((is_init res.`6 0 800) /\ (res.`1 = (_buf0 + _lEN))) /\
         (res.`2 = (_buf1 + _lEN))) /\
        (res.`3 = (_buf2 + _lEN))) /\
       (res.`4 = (_buf3 + _lEN))))))))))))))) /\
      (valid res.`7))].
proof.
  proc; rewrite /=.
  sp. if.
  + seq 1: (valid trace___squeeze_imem_avx2x4 /\ lO =_lEN%%rATE8 /\ 0<rATE8 /\ rATE8<200 /\
            is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\ 0 <= _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ lEN = _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf2 _lEN /\
            is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\
            buf0 = _buf0 + _lEN - lO /\ buf1 = _buf1 + _lEN - lO /\
            buf2 = _buf2 + _lEN - lO/\ buf3 = _buf3 + _lEN - lO).
    + auto. 
      if.
      + while(valid trace___squeeze_imem_avx2x4 /\ lO =_lEN%%rATE8 /\ 0<rATE8 /\ rATE8<200 /\
            is_valid ptr_modulus Glob.mem_v _buf0 _lEN /\ 0 <= _lEN /\ 
            is_valid ptr_modulus Glob.mem_v _buf1 _lEN /\ lEN = _lEN /\ iTERS = _lEN%/rATE8 /\ 
            is_valid ptr_modulus Glob.mem_v _buf2 _lEN /\ 0<=i /\ i<= iTERS /\
            is_valid ptr_modulus Glob.mem_v _buf3 _lEN /\ iTERS * rATE8 <= _lEN /\
            buf0 = _buf0 + i*rATE8 /\ buf1 = _buf1 + i*rATE8  /\
            buf2 = _buf2 +i*rATE8  /\ buf3 = _buf3 + i*rATE8).
        + auto. ecall(__dumpstate_imem_avx2x4_trace param_11 param_10 param_9 param_8 param_7
                       param_6 (BArray800.init_arr (W8.of_int 255) 800)). auto.
          ecall(_keccakf1600_avx2x4_trace param_12 (BArray800.init_arr (W8.of_int 255) 800)).
          auto. rewrite /valid /= => &m /> *. split. smt(BArray800.init_arrP). move => *.
          rewrite !mulrDl /= => /> *. split. smt(). move => *. split. rewrite !all_cat /=. smt(). smt().
        auto. rewrite /valid /= => &m /> *. smt().
      auto. rewrite /valid /= => &m /> *. smt().
    if.
    + auto.
      ecall(__dumpstate_imem_avx2x4_trace param_4 param_3 param_2 param_1 param_0 param
           (BArray800.init_arr (W8.of_int 255) 800)). auto.
      ecall(_keccakf1600_avx2x4_trace param_5 (BArray800.init_arr (W8.of_int 255) 800)). auto.
      rewrite /valid /= => &m /> *. smt(all_cat BArray800.init_arrP).
    auto. rewrite /valid /= => &m /> *. smt(BArray800.init_arrP).
  auto. rewrite /valid /= => &m /> *. smt(BArray800.init_arrP).
qed.
