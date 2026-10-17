import json, build
from cascade import B
M = json.load(open(build.HERE + "/common_manual.json"))
HDR = """(* -------------------------------------------------------------------- *)
(* Safety of the 4-way (u256[25] state) absorb/squeeze code: fixed-size
   memory and array absorb (4 buffers or broadcast) and squeeze, and the
   streaming (init/absorb/squeeze/finish "updstate") API.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety Keccakf1600x4_safety.
require import SBArray808_800.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.
"""
SUB = "SBArray808_800.is_init_cell_get SBArray808_800.is_init_cell_set"
WORDH = "and7_to_uint and7_nz int_shr3 int_shl3"
K4 = [0, 1, 2, 3]
def each(fmt): return " /\\ ".join(fmt.format(k=k) for k in K4)

# ---------- memory fixed-size ----------
def AS_BASE(tr, bufs):
    vb = " /\\ ".join(f"0 <= {b} /\\ is_valid ptr_modulus Glob.mem_v {b} __LEN" for b in bufs)
    return (f"valid {tr} /\\ 0 <= _LEN <= __LEN /\\ 0 <= _TRAILB < 256 /\\ 0 <= aT /\\ {vb}"
            f" /\\ aT + _LEN + {B('_TRAILB')} = _aT + __LEN + {B('__TRAILB')}"
            f" /\\ aT + _LEN + {B('_TRAILB')} <= 200 /\\ (aT %% 8 = 0 \\/ (_LEN = 0 /\\ _TRAILB = 0))")
ASMB = AS_BASE("trace___addstate_m_bcast_avx2x4", ["_buf"])
ASM4 = AS_BASE("trace___addstate_m_avx2x4", [f"_buf{k}" for k in K4])
def ABS_M(tr, bufs):
    vb = " /\\ ".join(f"0 <= {b} /\\ is_valid ptr_modulus Glob.mem_v {b} __LEN" for b in bufs)
    return (f"valid {tr} /\\ _RATE8 = __RATE8 /\\ _TRAILB = __TRAILB /\\ 0 < __RATE8 < 200"
            f" /\\ 0 <= __TRAILB < 256 /\\ 0 <= __LEN /\\ {vb}")
ABMB = ABS_M("trace___absorb_m_bcast_avx2x4", ["_buf"])
ABM4 = ABS_M("trace___absorb_m_avx2x4", [f"_buf{k}" for k in K4])
LOOPPOS = " /\\ 0 <= _aT < __RATE8 /\\ __RATE8 <= _aT + __LEN /\\ aT = 0 /\\ _LEN = __LEN - (__RATE8 - _aT) /\\ iTERS = _LEN %/ _RATE8 /\\ 0 <= i <= iTERS"
DSM4 = ("valid trace___dumpstate_m_avx2x4 /\\ _LEN = __LEN /\\ 0 <= __LEN <= 200 /\\ "
        + each("0 <= _buf{k} /\\ is_valid ptr_modulus Glob.mem_v _buf{k} __LEN"))
SQM4 = ("valid trace___squeeze_m_avx2x4 /\\ _LEN = __LEN /\\ _RATE8 = __RATE8 /\\ 0 <= __LEN /\\ 0 < __RATE8 < 200 /\\ "
        + each("0 <= _buf{k} /\\ is_valid ptr_modulus Glob.mem_v _buf{k} __LEN")
        + " /\\ iTERS = _LEN %/ _RATE8 /\\ lO = _LEN %% _RATE8 /\\ 0 <= i <= iTERS /\\ " + each("buf{k} = _buf{k} + _RATE8 * i"))

# ---------- array fixed-size ----------
def ASA_BASE(tr, bbufs):
    ib = " /\\ ".join(f"BArray999.is_init {b} _offset __LEN" for b in bbufs)
    return (f"valid {tr} /\\ 0 <= _LEN <= __LEN /\\ 0 <= _TRAILB < 256 /\\ 0 <= aT /\\ 0 <= _offset"
            f" /\\ _offset + __LEN <= 999 /\\ {ib}"
            f" /\\ aT + _LEN + {B('_TRAILB')} = _aT + __LEN + {B('__TRAILB')}"
            f" /\\ aT + _LEN + {B('_TRAILB')} <= 200 /\\ (aT %% 8 = 0 \\/ (_LEN = 0 /\\ _TRAILB = 0))")
ASAB = ASA_BASE("trace___addstate_bcast_avx2x4", ["b_buf"])
ASA4 = ASA_BASE("trace___addstate_avx2x4", [f"b_buf{k}" for k in K4])
def ABS_A(tr):
    return (f"valid {tr} /\\ _RATE8 = __RATE8 /\\ _TRAILB = __TRAILB /\\ 0 < __RATE8 < 200 /\\ 0 <= __TRAILB < 256")
LOOPPOSA = " /\\ 0 <= _aT < __RATE8 /\\ __RATE8 <= _aT + 999 /\\ aT = 0 /\\ _LEN = 999 - (__RATE8 - _aT) /\\ iTERS = _LEN %/ _RATE8 /\\ 0 <= i <= iTERS /\\ offset = (__RATE8 - _aT) + _RATE8 * i"
DSA4 = ("valid trace___dumpstate_avx2x4 /\\ _LEN = __LEN /\\ 0 <= __LEN <= 200 /\\ 0 <= _offset /\\ _offset + __LEN <= 999")
SQA4 = ("valid trace___squeeze_avx2x4 /\\ _LEN = 999 /\\ _RATE8 = __RATE8 /\\ 0 < __RATE8 < 200"
        " /\\ iTERS = _LEN %/ _RATE8 /\\ lO = _LEN %% _RATE8 /\\ 0 <= i <= iTERS /\\ offset = _RATE8 * i /\\ "
        + each("BArray999.is_init b_buf{k} 0 offset"))

# ---------- streaming ----------
def ADD_S(tr, bufs):
    vb = " /\\ ".join(f"0 <= _{b} /\\ is_valid ptr_modulus Glob.mem_v _{b} (_upto - _at) /\\ {b} = _{b} + (at - _at)" for b in bufs)
    return (f"valid {tr} /\\ upto = _upto /\\ 0 <= _at <= _upto <= 200 /\\ _at <= at <= upto"
            f" /\\ (at %% 8 = 0 \\/ at = upto) /\\ {vb} /\\ newat = at + 8")
def ADDA_S(tr, bbufs, outbuf=False):
    s = (f"valid {tr} /\\ upto = _upto /\\ 0 <= _at <= _upto <= 200 /\\ 0 <= _off /\\ _off + (_upto - _at) <= 999"
         f" /\\ _at <= at <= upto /\\ off = _off + (at - _at) /\\ (at %% 8 = 0 \\/ at = upto) /\\ newat = at + 8")
    for b in bbufs:
        s += (f" /\\ BArray999.is_init {b} 0 off" if outbuf else f" /\\ BArray999.is_init {b} _off (_upto - _at)")
    return s
def ABS_L(tr, bufs):
    vb = " /\\ ".join(f"0 <= _{b} <= {b} /\\ is_valid ptr_modulus Glob.mem_v _{b} _len /\\ {b} + (len - at) = _{b} + _len" for b in bufs)
    return (f"valid {tr} /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len /\\ {vb}"
            " /\\ BArray808.is_init b_st 0 808 /\\ BArray800.is_init b_stk 0 800")
def SQ_C(tr, bufs):
    vb = " /\\ ".join(f"{b} = _{b} /\\ 0 <= _{b} /\\ is_valid ptr_modulus Glob.mem_v _{b} _len" for b in bufs)
    return (f"valid {tr} /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ len = _len /\\ _len <= 18446744073709551360 /\\ {vb}"
            " /\\ BArray808.is_init b_st 0 808 /\\ BArray800.is_init b_stk 0 800")
def ABSA_L(tr, bbufs):
    ib = " /\\ ".join(f"BArray999.is_init {b} 0 _len" for b in bbufs)
    return (f"valid {tr} /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len /\\ 0 <= off /\\ off + (len - at) = _len"
            f" /\\ 0 <= _len <= 999 /\\ {ib} /\\ BArray808.is_init b_st 0 808 /\\ BArray800.is_init b_stk 0 800")
def SQA_C(tr):
    return (f"valid {tr} /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ len = _len /\\ 0 <= _len <= 999"
            " /\\ BArray808.is_init b_st 0 808 /\\ BArray800.is_init b_stk 0 800")
def SQA_L(tr, bbufs):
    ib = " /\\ ".join(f"BArray999.is_init {b} 0 off" for b in bbufs)
    return (f"valid {tr} /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len /\\ 0 <= off /\\ off + (len - at) = _len"
            f" /\\ 0 <= _len <= 999 /\\ {ib} /\\ BArray808.is_init b_st 0 808 /\\ BArray800.is_init b_stk 0 800")
B4 = [f"buf{k}" for k in K4]; BB4 = [f"b_buf{k}" for k in K4]

ANN = {
 # memory fixed-size
 "__addstate_m_bcast_avx2x4": {"INV1": ASMB + " /\\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\\ at %% 32 = 0"
                                 " /\\ 4 * (buf - (_buf + (__LEN - _LEN))) = at - 32 * (aT %/ 8)"},
 "__addstate_m_avx2x4": {"INV1": ASM4 + " /\\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\\ at %% 4 = 0 /\\ "
                           + each("buf{k} = _buf{k} + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8))")},
 "__absorb_m_bcast_avx2x4": {"INV1": ABMB + LOOPPOS + " /\\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i",
                             "CUT2": ABMB + f" /\\ aT = (_aT + __LEN) %% __RATE8 + {B('__TRAILB')}"},
 "__absorb_m_avx2x4": {"INV1": ABM4 + LOOPPOS + " /\\ " + each("buf{k} = _buf{k} + (__RATE8 - _aT) + _RATE8 * i"),
                       "CUT2": ABM4 + f" /\\ aT = (_aT + __LEN) %% __RATE8 + {B('__TRAILB')}"},
 "__dumpstate_m_avx2x4": {
   "INV1": DSM4 + " /\\ 0 <= i <= 32 * (_LEN %/ 32) /\\ i %% 32 = 0 /\\ " + each("buf{k} = _buf{k} + i"),
   "INV2": DSM4 + " /\\ 32 * (_LEN %/ 32) <= i <= 8 * (_LEN %/ 8) /\\ i %% 8 = 0 /\\ " + each("buf{k} = _buf{k} + i")},
 "__squeeze_m_avx2x4": {"INV1": SQM4},
 # array fixed-size
 "__addstate_bcast_avx2x4": {"INV1": ASAB + " /\\ 32 * (aT %/ 8) <= at <= 32 * (aT %/ 8 + _LEN %/ 8) /\\ at %% 32 = 0"
                               " /\\ 4 * (offset - (_offset + (__LEN - _LEN))) = at - 32 * (aT %/ 8)"},
 "__addstate_avx2x4": {"INV1": ASA4 + " /\\ 4 * (aT %/ 8) <= at <= 4 * (aT %/ 8) + 4 * (_LEN %/ 8) /\\ at %% 4 = 0"
                         " /\\ offset = _offset + (__LEN - _LEN) + 2 * (at - 4 * (aT %/ 8))"},
 "__absorb_bcast_avx2x4": {"INV1": ABS_A("trace___absorb_bcast_avx2x4") + LOOPPOSA,
                           "CUT2": ABS_A("trace___absorb_bcast_avx2x4") + f" /\\ aT = (_aT + 999) %% __RATE8 + {B('__TRAILB')}"},
 "__absorb_avx2x4": {"INV1": ABS_A("trace___absorb_avx2x4") + LOOPPOSA,
                     "CUT2": ABS_A("trace___absorb_avx2x4") + f" /\\ aT = (_aT + 999) %% __RATE8 + {B('__TRAILB')}"},
 "__dumpstate_avx2x4": {
   "INV1": DSA4 + " /\\ 0 <= i <= 32 * (_LEN %/ 32) /\\ i %% 32 = 0 /\\ offset = _offset + i /\\ " + each("BArray999.is_init b_buf{k} 0 offset"),
   "INV2": DSA4 + " /\\ 32 * (_LEN %/ 32) <= i <= 8 * (_LEN %/ 8) /\\ i %% 8 = 0 /\\ offset = _offset + i /\\ " + each("BArray999.is_init b_buf{k} 0 offset")},
 "__squeeze_avx2x4": {"INV1": SQA4},
 # streaming, memory
 "_init_updstate_avx2x4": {"SMT": SUB},
 "_add_m_bcast_updstate_avx2x4": {"SMT": WORDH, "INV1": ADD_S("trace__add_m_bcast_updstate_avx2x4", ["buf"])},
 "_add_m_updstate_avx2x4": {"SMT": WORDH, "INV1": ADD_S("trace__add_m_updstate_avx2x4", B4)},
 "_dump_m_updstate_avx2x4": {"SMT": WORDH, "INV1": ADD_S("trace__dump_m_updstate_avx2x4", B4)},
 "_absorb_m_bcast_updstate_avx2x4": {"SMT": SUB, "INV1": ABS_L("trace__absorb_m_bcast_updstate_avx2x4", ["buf"])},
 "_absorb_m_updstate_avx2x4": {"SMT": SUB, "INV1": ABS_L("trace__absorb_m_updstate_avx2x4", B4)},
 "_squeeze_m_updstate_avx2x4": {"SMT": SUB, "CUT1": SQ_C("trace__squeeze_m_updstate_avx2x4", B4),
                                "INV1": ABS_L("trace__squeeze_m_updstate_avx2x4", B4)},
 # streaming, array
 "_add_bcast_updstate_avx2x4": {"SMT": WORDH, "INV1": ADDA_S("trace__add_bcast_updstate_avx2x4", ["b_buf"])},
 "_add_updstate_avx2x4": {"SMT": WORDH, "INV1": ADDA_S("trace__add_updstate_avx2x4", BB4)},
 "_dump_updstate_avx2x4": {"SMT": WORDH, "INV1": ADDA_S("trace__dump_updstate_avx2x4", BB4, outbuf=True)},
 "_absorb_bcast_updstate_avx2x4": {"SMT": SUB, "INV1": ABSA_L("trace__absorb_bcast_updstate_avx2x4", ["b_buf"])},
 "_absorb_updstate_avx2x4": {"SMT": SUB, "INV1": ABSA_L("trace__absorb_updstate_avx2x4", BB4)},
 "_squeeze_updstate_avx2x4": {"SMT": SUB, "CUT1": SQA_C("trace__squeeze_updstate_avx2x4"),
                              "INV1": SQA_L("trace__squeeze_updstate_avx2x4", BB4)},
}
MANUAL = {"_ststatus_data_avx2x4": M["manual"]["_ststatus_data"]}
MEMFIX = ["__addstate_m_bcast_avx2x4","__absorb_m_bcast_avx2x4","__addstate_m_avx2x4","__absorb_m_avx2x4","__dumpstate_m_avx2x4","__squeeze_m_avx2x4"]
ARRFIX = ["__addstate_bcast_avx2x4","__absorb_bcast_avx2x4","__addstate_avx2x4","__absorb_avx2x4","__dumpstate_avx2x4","__squeeze_avx2x4"]
UPD = ["_init_updstate_avx2x4","_ststatus_data_avx2x4","_finish_updstate_avx2x4","ststatus_updstate_avx2x4","init_updstate_avx2x4","finish_updstate_avx2x4",
       "_add_m_bcast_updstate_avx2x4","_absorb_m_bcast_updstate_avx2x4","_add_m_updstate_avx2x4","_absorb_m_updstate_avx2x4",
       "_dump_m_updstate_avx2x4","_squeeze_m_updstate_avx2x4","absorb_m_bcast_updstate_avx2x4","absorb_m_updstate_avx2x4","squeeze_m_updstate_avx2x4"]
UPDA = ["_add_bcast_updstate_avx2x4","_absorb_bcast_updstate_avx2x4","_add_updstate_avx2x4","_absorb_updstate_avx2x4",
        "_dump_updstate_avx2x4","_squeeze_updstate_avx2x4","absorb_bcast_updstate_avx2x4","absorb_updstate_avx2x4","squeeze_updstate_avx2x4"]
items = [('raw', HDR), ('raw', "(* memory absorb/squeeze *)")] + [('gen', n) for n in MEMFIX]
items += [('raw', "(* memory streaming API *)")] + [('gen', n) for n in UPD]
items += [('theory', dict(name="KeccakArrayAvx2x4Safety", presets=["fixedsizes_avx2x4"],
                          check="Keccak1600_fixedsizes_avx2x4_checkXtr.ec")),
          ('theory', dict(name="KeccakUpdstateAvx2x4Safety", presets=["updstate_avx2x4"],
                          check="Keccak1600_updstate_avx2x4_checkXtr.ec"))]
if __name__ == '__main__':
    build.build(items, ANN, MANUAL, default_smt="divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp", out_path=build.ROOT + "/avx2x4/Keccak1600x4_safety.ec")
    print("built")
