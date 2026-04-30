#include <set_cur_bank_modulo.h>

SetCurBankModulo::state
SetCurBankModulo::set_cur_bank(const SetCurBankModulo::state &s,
                               const unsigned int &b) {
  return state{(NBANKS ? b % NBANKS : b), s.acc};
}
