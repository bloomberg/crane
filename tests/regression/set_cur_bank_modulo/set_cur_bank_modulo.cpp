#include <set_cur_bank_modulo.h>

#include <memory>
#include <type_traits>
#include <utility>

std::shared_ptr<SetCurBankModulo::state>
SetCurBankModulo::set_cur_bank(std::shared_ptr<SetCurBankModulo::state> s,
                               const unsigned int b) {
  return std::make_shared<SetCurBankModulo::state>(state{(b % NBANKS), s->acc});
}
