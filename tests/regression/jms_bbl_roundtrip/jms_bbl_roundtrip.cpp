#include <jms_bbl_roundtrip.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
JmsBblRoundtrip::addr12_of_nat(const unsigned int &n) {
  return (4096u ? n % 4096u : n);
}

__attribute__((pure)) JmsBblRoundtrip::state
JmsBblRoundtrip::execute_jms(const JmsBblRoundtrip::state &s,
                             const unsigned int &addr) {
  return state{addr12_of_nat(addr), addr12_of_nat((s.pc + 2u)), true};
}

__attribute__((pure)) JmsBblRoundtrip::state
JmsBblRoundtrip::execute_bbl(JmsBblRoundtrip::state s) {
  if (s.has_ret) {
    return state{s.ret, s.ret, false};
  } else {
    return s;
  }
}
