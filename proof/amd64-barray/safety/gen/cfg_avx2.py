import build
from cascade import B, J, W
HDR = """(* -------------------------------------------------------------------- *)
(* Safety of the 1-way AVX2 (u256[7] state) absorb/squeeze code: state
   helpers, fixed-size memory and array absorb/squeeze.
   Model: ../extracted/Keccak1600_Jazz_safety.ec (jasmin2ec -m safety).   *)
(* -------------------------------------------------------------------- *)
require import AllCore IntDiv CoreMap List Distr.
require import Keccak1600_Jazz_safety Keccak1600_common_safety Keccakf1600_safety.
from Jasmin require import JModel_x86 Jcheck JSafety JByte_array.
import JWord JUtils.
"""
# --- memory absorb cascade
AM_F = ("valid trace___addstate_m_avx2 /\\ 0 <= _aT /\\ 0 <= __LEN /\\ 0 <= __TRAILB < 256"
        f" /\\ _aT + __LEN + {B('__TRAILB')} <= 200 /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN")
def AM(c, last=False): return AM_F + " /\\ " + (J(c, ln=None, tr=None, ptr="buf", p0="_buf") if last else J(c, ptr="buf", p0="_buf"))
# --- array absorb cascade
AA_F = ("valid trace___addstate_avx2 /\\ 0 <= _aT /\\ 0 <= __LEN /\\ 0 <= __TRAILB < 256"
        f" /\\ _aT + __LEN + {B('__TRAILB')} <= 200 /\\ 0 <= _offset /\\ _offset + __LEN <= 999"
        " /\\ BArray999.is_init b_buf _offset __LEN /\\ offset = _offset")
def AA(c, last=False): return AA_F + " /\\ " + (J(c, ln=None, tr=None, delta="dELTA") if last else J(c, delta="dELTA"))
# --- memory squeeze cascade
DM_F = "valid trace___dumpstate_m_avx2 /\\ 0 <= __LEN <= 200 /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN"
def DM(k): return DM_F + " /\\ " + W(k, ptr="buf", p0="_buf")
DA_F = ("valid trace___dumpstate_avx2 /\\ 0 <= __LEN <= 200 /\\ 0 <= _offset /\\ _offset + __LEN <= 999 /\\ offset = _offset")
def DA(k): return DA_F + " /\\ " + W(k, delta="dELTA") + f" /\\ BArray999.is_init b_buf 0 (_offset + dELTA)"

# cascade positions
RD_CUT = {"CUT2": 8, "CUT3": 40, "CUT4": 48}
RD_BEFORE = {"BEFORE5": 80, "BEFORE6": 88, "BEFORE7": 120, "BEFORE8": 128, "BEFORE9": 160, "BEFORE10": 168, "BEFORE11": 200}
WR_CUT = {"CUT2": 40, "CUT3": 48, "CUT4": 80, "CUT5": 88, "CUT6": 120, "CUT7": 128, "CUT8": 160, "CUT9": 168}

AB_M = ("valid trace___absorb_m_avx2 /\\ _RATE8 = __RATE8 /\\ _TRAILB = __TRAILB /\\ 0 < __RATE8 < 200"
        " /\\ 0 <= __TRAILB < 256 /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\\ 0 <= __LEN")
AB_A = ("valid trace___absorb_avx2 /\\ _RATE8 = __RATE8 /\\ _TRAILB = __TRAILB /\\ 0 < __RATE8 < 200"
        " /\\ 0 <= __TRAILB < 256")
ANN = {
 "__state_init_avx2": {"INV1": "valid trace___state_init_avx2 /\\ 0 <= i <= 7 /\\ BArray224.is_init b_st 0 (32 * i)"},
 # the last sub-read (at 168) does not assign the remaining length and trail byte (dead)
 "__addstate_m_avx2": dict([(k, AM(c, k == "BEFORE11")) for k, c in list(RD_CUT.items()) + list(RD_BEFORE.items())]),
 "__addstate_avx2": dict([(k, AA(c, k == "BEFORE11")) for k, c in list(RD_CUT.items()) + list(RD_BEFORE.items())]),
 # MERGE1: the join of the first conditional (both branches write 8 bytes) is before the
 # reg1 write, so it is not one of the cuts: W(8)
 "__dumpstate_m_avx2": dict([(k, DM(c)) for k, c in WR_CUT.items()] + [("MERGE1", DM(8))]),
 "__dumpstate_avx2": dict([(k, DA(c)) for k, c in WR_CUT.items()] + [("MERGE1", DA(8))]),
 "__absorb_m_avx2": {
   "INV1": AB_M + " /\\ 0 <= _aT < __RATE8 /\\ __RATE8 <= _aT + __LEN /\\ aT = 0 /\\ _LEN = __LEN - (__RATE8 - _aT)"
           " /\\ iTERS = _LEN %/ _RATE8 /\\ 0 <= i <= iTERS /\\ buf = _buf + (__RATE8 - _aT) + _RATE8 * i",
   "CUT2": AB_M + f" /\\ aT = (_aT + __LEN) %% __RATE8 + {B('__TRAILB')}"},
 "__absorb_avx2": {
   "INV1": AB_A + " /\\ 0 <= _aT < __RATE8 /\\ __RATE8 <= _aT + 999 /\\ aT = 0 /\\ _LEN = 999 - (__RATE8 - _aT)"
           " /\\ iTERS = _LEN %/ _RATE8 /\\ 0 <= i <= iTERS /\\ offset = (__RATE8 - _aT) + _RATE8 * i",
   "CUT2": AB_A + f" /\\ aT = (_aT + 999) %% __RATE8 + {B('__TRAILB')}"},
 "__squeeze_m_avx2": {
   "INV1": ("valid trace___squeeze_m_avx2 /\\ _LEN = __LEN /\\ _RATE8 = __RATE8 /\\ 0 <= __LEN /\\ 0 < __RATE8 < 200"
            " /\\ 0 <= _buf /\\ is_valid ptr_modulus Glob.mem_v _buf __LEN /\\ iTERS = _LEN %/ _RATE8 /\\ lO = _LEN %% _RATE8"
            " /\\ 0 <= i <= iTERS /\\ buf = _buf + _RATE8 * i")},
 "__squeeze_avx2": {
   "INV1": ("valid trace___squeeze_avx2 /\\ _LEN = 999 /\\ _RATE8 = __RATE8 /\\ 0 < __RATE8 < 200"
            " /\\ iTERS = _LEN %/ _RATE8 /\\ lO = _LEN %% _RATE8 /\\ 0 <= i <= iTERS /\\ offset = _RATE8 * i"
            " /\\ BArray999.is_init b_buf 0 offset")},
}
items = [('raw', HDR), ('raw', "(* AVX2 state helpers *)")]
items += [('gen', n) for n in ["__u64_to_u256","__state_init_avx2","__perm_reg3456_avx2","__unperm_reg3456_avx2",
                               "__addstate_r3456_avx2","__stavx2_pos_avx2","__addratebit_avx2"]]
items += [('raw', "(* memory absorb/squeeze *)")]
items += [('gen', n) for n in ["__addstate_m_avx2","__absorb_m_avx2","__dumpstate_m_avx2","__squeeze_m_avx2"]]
items += [('theory', dict(name="KeccakArrayAvx2Safety", presets=["fixedsizes_avx2"],
                          check="Keccak1600_fixedsizes_avx2_checkXtr.ec"))]
MANUAL = {}
if __name__ == '__main__':
    build.build(items, ANN, MANUAL, default_smt="divz_eq modzDr modz_ge0 ltz_pmod", out_path=build.ROOT + "/avx2/Keccak1600_avx2_safety.ec")
    print("built")
