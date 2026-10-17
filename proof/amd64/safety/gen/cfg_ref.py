import build
HDR = """(* -------------------------------------------------------------------- *)
(* Safety of the ref (1-way, u64[25] state) absorb/squeeze code:
   fixed-size memory/array absorb and squeeze, and the streaming
   (init/absorb/squeeze/finish "updstate") API.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety Keccakf1600_safety.
require import SBArray208_200.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.
"""
def B(t): return f"(if {t} <> 0 then 1 else 0)"
MAXL = "18446744073709551616"
SUB = "SBArray208_200.is_init_cell_get SBArray208_200.is_init_cell_set"
WORDH = "and7_to_uint and7_nz int_shr3 int_shl3"

# ---------------- memory fixed-size -----------------
AS_BASE = ("valid trace___addstate_m /\\ 0 <= _LEN <= __LEN /\\ 0 <= _TRAILB < 256 /\\ 0 <= aT /\\ 0 <= _buf"
           " /\\ is_valid ptr_modulus Glob.mem_v (_buf + (__LEN - _LEN)) _LEN"
           f" /\\ aT + _LEN + {B('_TRAILB')} = _aT + __LEN + {B('__TRAILB')}"
           f" /\\ aT + _LEN + {B('_TRAILB')} <= 200 /\\ (aT %% 8 = 0 \\/ (_LEN = 0 /\\ _TRAILB = 0))")
AB_COMMON = ("valid trace___absorb_m /\\ _RATE8 = __RATE8 /\\ _TRAILB = __TRAILB /\\ 0 < __RATE8 < 200"
             " /\\ 0 <= __TRAILB < 256 /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\\ 0 <= __LEN")
DS_COMMON = ("valid trace___dumpstate_m /\\ _LEN = __LEN /\\ 0 <= __LEN <= 200 /\\ 0 <= _buf"
             " /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN")
# ---------------- memory streaming -----------------
ADD_S = ("valid trace__add_m_updstate /\\ upto = _upto /\\ 0 <= _at <= _upto <= 200 /\\ 0 <= _buf"
         " /\\ is_valid ptr_modulus Glob.mem_v _buf (_upto - _at) /\\ _at <= at <= upto"
         " /\\ buf = _buf + (at - _at) /\\ (at %% 8 = 0 \\/ at = upto)")
DUMP_S = ADD_S.replace("trace__add_m_updstate", "trace__dump_m_updstate")
ABS_L = ("valid trace__absorb_m_updstate /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len"
         " /\\ 0 <= _buf <= buf /\\ is_valid ptr_modulus Glob.mem_v _buf _len /\\ buf + (len - at) = _buf + _len"
         " /\\ BArray208.is_init b_st 0 208 /\\ BArray200.is_init b_stk 0 200")
SQ_L = ("valid trace__squeeze_m_updstate /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len"
        " /\\ 0 <= _buf <= buf /\\ is_valid ptr_modulus Glob.mem_v _buf _len /\\ buf + (len - at) = _buf + _len"
        " /\\ BArray208.is_init b_st 0 208 /\\ BArray200.is_init b_stk 0 200")
SQ_C = ("valid trace__squeeze_m_updstate /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ buf = _buf /\\ len = _len"
        f" /\\ _len <= 18446744073709551360 /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf _len"
        " /\\ BArray208.is_init b_st 0 208 /\\ BArray200.is_init b_stk 0 200")

ANN = {
 "__state_init": {"INV1": "valid trace___state_init /\\ 0 <= i <= 25 /\\ BArray200.is_init b_st 0 (8 * i)"},
 "__addstate_m": {"SMT": "chunks8",
   "CUT2": AS_BASE + " /\\ buf = _buf + (__LEN - _LEN)",
   "INV1": AS_BASE + " /\\ inc = _LEN %/ 32 /\\ 0 <= i <= inc /\\ buf = _buf + (__LEN - _LEN) + 32 * i",
   "INV2": AS_BASE + " /\\ aT <= at <= aT + (_LEN %/ 8) * 8 /\\ (at - aT) %% 8 = 0 /\\ buf = _buf + (__LEN - _LEN) + (at - aT)"},
 "__absorb_m": {
   "INV1": AB_COMMON + " /\\ 0 <= _aT < __RATE8 /\\ __RATE8 <= _aT + __LEN /\\ aT = 0 /\\ _LEN = __LEN - (__RATE8 - _aT)"
           " /\\ iTERS = _LEN %/ _RATE8 /\\ 0 <= i <= iTERS /\\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i",
   "CUT2": AB_COMMON + f" /\\ aT = (_aT + __LEN) %% __RATE8 + {B('__TRAILB')} /\\ buf = _buf + __LEN"},
 "__dumpstate_m": {"SMT": "chunks8",
   "INV1": DS_COMMON + " /\\ inc = _LEN %/ 32 /\\ 0 <= j <= inc /\\ buf = _buf + 32 * j",
   "INV2": DS_COMMON + " /\\ 0 <= i <= _LEN %/ 8 /\\ buf = _buf + 8 * i"},
 "__squeeze_m": {
   "INV1": ("valid trace___squeeze_m /\\ _LEN = __LEN /\\ _RATE8 = __RATE8 /\\ 0 <= __LEN /\\ 0 < __RATE8 < 200"
            " /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\\ 0 <= i <= _LEN %/ _RATE8 /\\ buf = _buf + _RATE8 * i")},
 "_init_updstate": {"SMT": SUB},
 "_finish_updstate": {},
 "_add_m_updstate": {"SMT": WORDH, "CUT3": ADD_S + " /\\ newat = at",
                     "INV1": ADD_S + " /\\ newat = at + 32", "INV2": ADD_S + " /\\ newat = at + 8"},
 "_dump_m_updstate": {"SMT": WORDH, "CUT3": DUMP_S + " /\\ newat = at",
                      "INV1": DUMP_S + " /\\ newat = at + 32", "INV2": DUMP_S + " /\\ newat = at + 8"},
 "_absorb_m_updstate": {"SMT": SUB, "INV1": ABS_L},
 "_squeeze_m_updstate": {"SMT": SUB, "CUT1": SQ_C, "INV1": SQ_L},
}

# ---------------- array fixed-size (_ASIZE = 999) -----------------
ASA_BASE = ("valid trace___addstate /\\ 0 <= _LEN <= __LEN /\\ 0 <= _TRAILB < 256 /\\ 0 <= aT /\\ 0 <= _offset"
            " /\\ _offset + __LEN <= 999 /\\ BArray999.is_init b_buf _offset __LEN"
            f" /\\ aT + _LEN + {B('_TRAILB')} = _aT + __LEN + {B('__TRAILB')}"
            f" /\\ aT + _LEN + {B('_TRAILB')} <= 200 /\\ (aT %% 8 = 0 \\/ (_LEN = 0 /\\ _TRAILB = 0))")
ABA_COMMON = ("valid trace___absorb /\\ _RATE8 = __RATE8 /\\ _TRAILB = __TRAILB /\\ 0 < __RATE8 < 200"
              " /\\ 0 <= __TRAILB < 256")
DSA_COMMON = ("valid trace___dumpstate /\\ _LEN = __LEN /\\ 0 <= __LEN <= 200 /\\ 0 <= _offset /\\ _offset + __LEN <= 999")
ADDA_S = ("valid trace__add_updstate /\\ upto = _upto /\\ 0 <= _at <= _upto <= 200 /\\ 0 <= _off"
          " /\\ _off + (_upto - _at) <= 999 /\\ BArray999.is_init b_buf _off (_upto - _at) /\\ _at <= at <= upto"
          " /\\ off = _off + (at - _at) /\\ (at %% 8 = 0 \\/ at = upto)")
DUMPA_S = ("valid trace__dump_updstate /\\ upto = _upto /\\ 0 <= _at <= _upto <= 200 /\\ 0 <= _off"
           " /\\ _off + (_upto - _at) <= 999 /\\ _at <= at <= upto"
           " /\\ off = _off + (at - _at) /\\ (at %% 8 = 0 \\/ at = upto) /\\ BArray999.is_init b_buf 0 off")
ABSA_L = ("valid trace__absorb_updstate /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len /\\ 0 <= off"
          " /\\ off + (len - at) = _len /\\ 0 <= _len <= 999 /\\ BArray999.is_init b_buf 0 _len"
          " /\\ BArray208.is_init b_st 0 208 /\\ BArray200.is_init b_stk 0 200")
SQA_C = ("valid trace__squeeze_updstate /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ len = _len /\\ 0 <= _len <= 999"
         " /\\ BArray208.is_init b_st 0 208 /\\ BArray200.is_init b_stk 0 200")
SQA_L = ("valid trace__squeeze_updstate /\\ 0 < r8 <= 200 /\\ 0 <= at < r8 /\\ at <= len /\\ 0 <= off"
         " /\\ off + (len - at) = _len /\\ 0 <= _len <= 999 /\\ BArray999.is_init b_buf 0 off"
         " /\\ BArray208.is_init b_st 0 208 /\\ BArray200.is_init b_stk 0 200")
ANN.update({
 "__addstate": {"SMT": "chunks8",
   "CUT2": ASA_BASE + " /\\ offset = _offset /\\ dELTA = __LEN - _LEN",
   "INV1": ASA_BASE + " /\\ offset = _offset /\\ inc = _LEN %/ 32 /\\ 0 <= i <= inc /\\ dELTA = __LEN - _LEN + 32 * i",
   "INV2": ASA_BASE + " /\\ dELTA = 0 /\\ aT %/ 8 <= at <= aT %/ 8 + _LEN %/ 8 /\\ offset = _offset + (__LEN - _LEN) + 8 * (at - aT %/ 8)"},
 "__absorb": {
   "INV1": ABA_COMMON + " /\\ 0 <= _aT < __RATE8 /\\ __RATE8 <= _aT + 999 /\\ aT = 0 /\\ _LEN = 999 - (__RATE8 - _aT)"
           " /\\ iTERS = _LEN %/ _RATE8 /\\ 0 <= i <= iTERS /\\ offset = (__RATE8 - _aT) + _RATE8 * i",
   "CUT2": ABA_COMMON + f" /\\ aT = (_aT + 999) %% __RATE8 + {B('__TRAILB')}"},
 "__dumpstate": {"SMT": "chunks8",
   "INV1": DSA_COMMON + " /\\ offset = _offset /\\ inc = _LEN %/ 32 /\\ 0 <= j <= inc /\\ dELTA = 32 * j /\\ BArray999.is_init b_buf 0 (_offset + dELTA)",
   "INV2": DSA_COMMON + " /\\ dELTA = 0 /\\ 0 <= i <= _LEN %/ 8 /\\ offset = _offset + 8 * i /\\ BArray999.is_init b_buf 0 offset"},
 "__squeeze": {
   "INV1": ("valid trace___squeeze /\\ _RATE8 = __RATE8 /\\ 0 < __RATE8 < 200 /\\ 0 <= i <= 999 %/ _RATE8"
            " /\\ offset = _RATE8 * i /\\ BArray999.is_init b_buf 0 offset")},
 "_add_updstate": {"SMT": WORDH, "CUT3": ADDA_S + " /\\ newat = at",
                   "INV1": ADDA_S + " /\\ newat = at + 32", "INV2": ADDA_S + " /\\ newat = at + 8"},
 "_dump_updstate": {"SMT": WORDH, "CUT3": DUMPA_S + " /\\ newat = at",
                    "INV1": DUMPA_S + " /\\ newat = at + 32", "INV2": DUMPA_S + " /\\ newat = at + 8"},
 "_absorb_updstate": {"SMT": SUB, "INV1": ABSA_L},
 "_squeeze_updstate": {"SMT": SUB, "CUT1": SQA_C, "INV1": SQA_L},
})

MEM = ["__state_init","__addratebit","__addstate_m","__absorb_m","__dumpstate_m","__squeeze_m",
       "_init_updstate","_finish_updstate","ststatus_updstate","init_updstate","finish_updstate",
       "_add_m_updstate","_absorb_m_updstate","_dump_m_updstate","_squeeze_m_updstate","absorb_m_updstate","squeeze_m_updstate"]
ARR = ["__addstate","__absorb","__dumpstate","__squeeze",
       "_add_updstate","_absorb_updstate","_dump_updstate","_squeeze_updstate","absorb_updstate","squeeze_updstate"]
items = [('raw', HDR), ('raw', "(* state init, rate bit, memory absorb/squeeze *)")]
items += [('gen', n) for n in MEM[:6]]
items += [('raw', "(* memory streaming API *)")] + [('gen', n) for n in MEM[6:]]
items += [('theory', dict(name="KeccakArrayRefSafety", presets=["fixedsizes_ref"],
                          check="Keccak1600_fixedsizes_ref_checkXtr.ec")),
          ('theory', dict(name="KeccakUpdstateRefSafety", presets=["updstate_ref"],
                          check="Keccak1600_updstate_ref_checkXtr.ec"))]
MANUAL = {}
if __name__ == '__main__':
    build.build(items, ANN, MANUAL, default_smt="divz_eq modzDr modz_ge0 ltz_pmod W8.to_uint_cmp W64.to_uint_cmp", out_path=build.ROOT + "/ref/Keccak1600_safety.ec")
    print("built")
