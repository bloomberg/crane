#include "set_cur_bank_modulo.h"

SetCurBankModulo::state
SetCurBankModulo::set_cur_bank(const SetCurBankModulo::state &s, uint64_t b) {
  return state{(NBANKS ? b % NBANKS : b), s.acc};
}
