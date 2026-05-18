#include "jms_bbl_roundtrip.h"

uint64_t JmsBblRoundtrip::addr12_of_nat(uint64_t n) {
  return (UINT64_C(4096) ? n % UINT64_C(4096) : n);
}

JmsBblRoundtrip::state
JmsBblRoundtrip::execute_jms(const JmsBblRoundtrip::state &s, uint64_t addr) {
  return state{addr12_of_nat(addr), addr12_of_nat((s.pc + UINT64_C(2))), true};
}

JmsBblRoundtrip::state JmsBblRoundtrip::execute_bbl(JmsBblRoundtrip::state s) {
  if (s.has_ret) {
    return state{s.ret, s.ret, false};
  } else {
    return s;
  }
}
