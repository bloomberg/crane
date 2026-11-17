#include "set_cur_bank_modulo.h"

SetCurBankModulo::state
SetCurBankModulo::set_cur_bank(const SetCurBankModulo::state &s, uint64_t b) {
  auto &&_once1 = NBANKS;
  return state{(_once1 ? b % _once1 : b), s.acc};
}
