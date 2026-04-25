#include <set_cur_bank_modulo.h>

#include <memory>
#include <type_traits>
#include <utility>

__attribute__((pure)) SetCurBankModulo::state
SetCurBankModulo::set_cur_bank(const SetCurBankModulo::state &s,
                               const unsigned int &b) {
  return state{(NBANKS ? b % NBANKS : b), s.acc};
}
