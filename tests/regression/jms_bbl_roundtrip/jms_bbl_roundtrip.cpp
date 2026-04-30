#include <jms_bbl_roundtrip.h>

unsigned int JmsBblRoundtrip::addr12_of_nat(const unsigned int &n) {
  return (4096u ? n % 4096u : n);
}

JmsBblRoundtrip::state
JmsBblRoundtrip::execute_jms(const JmsBblRoundtrip::state &s,
                             const unsigned int &addr) {
  return state{addr12_of_nat(addr), addr12_of_nat((s.pc + 2u)), true};
}

JmsBblRoundtrip::state JmsBblRoundtrip::execute_bbl(JmsBblRoundtrip::state s) {
  if (s.has_ret) {
    return state{s.ret, s.ret, false};
  } else {
    return s;
  }
}
