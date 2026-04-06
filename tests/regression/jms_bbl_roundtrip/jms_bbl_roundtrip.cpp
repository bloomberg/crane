#include <jms_bbl_roundtrip.h>

#include <memory>
#include <type_traits>
#include <utility>

__attribute__((pure)) unsigned int
JmsBblRoundtrip::addr12_of_nat(const unsigned int n) {
  return (4096u ? n % 4096u : n);
}

std::shared_ptr<JmsBblRoundtrip::state>
JmsBblRoundtrip::execute_jms(std::shared_ptr<JmsBblRoundtrip::state> s,
                             const unsigned int addr) {
  return std::make_shared<JmsBblRoundtrip::state>(
      state{addr12_of_nat(addr), addr12_of_nat((s->pc + 2u)), true});
}

std::shared_ptr<JmsBblRoundtrip::state>
JmsBblRoundtrip::execute_bbl(std::shared_ptr<JmsBblRoundtrip::state> s) {
  if (s->has_ret) {
    return std::make_shared<JmsBblRoundtrip::state>(
        state{s->ret, s->ret, false});
  } else {
    return std::move(s);
  }
}
