#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <set_cur_bank_modulo.h>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

unsigned int
SetCurBankModulo::cur_bank(const std::shared_ptr<SetCurBankModulo::state> &s) {
  return s->cur_bank;
}

unsigned int
SetCurBankModulo::acc(const std::shared_ptr<SetCurBankModulo::state> &s) {
  return s->acc;
}

std::shared_ptr<SetCurBankModulo::state>
SetCurBankModulo::set_cur_bank(std::shared_ptr<SetCurBankModulo::state> s,
                               const unsigned int b) {
  return std::make_shared<SetCurBankModulo::state>(
      state{(std::move(b) % NBANKS), std::move(s)->acc});
}
