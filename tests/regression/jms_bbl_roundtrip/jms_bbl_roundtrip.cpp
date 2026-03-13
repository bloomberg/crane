#include <jms_bbl_roundtrip.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
JmsBblRoundtrip::addr12_of_nat(const unsigned int n) {
  return (n % 4096u);
}

std::shared_ptr<JmsBblRoundtrip::state>
JmsBblRoundtrip::execute_jms(std::shared_ptr<JmsBblRoundtrip::state> s,
                             const unsigned int addr) {
  return std::make_shared<JmsBblRoundtrip::state>(
      state{addr12_of_nat(std::move(addr)),
            addr12_of_nat((std::move(s)->pc + 2u)), true});
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
