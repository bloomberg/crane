#ifndef INCLUDED_SET_CUR_BANK_MODULO
#define INCLUDED_SET_CUR_BANK_MODULO

#include <utility>

struct SetCurBankModulo {
  static inline const uint64_t NBANKS = UINT64_C(4);

  struct state {
    uint64_t cur_bank;
    uint64_t acc;
  };

  static state set_cur_bank(const state &s, uint64_t b);
  static inline const uint64_t t =
      set_cur_bank(state{UINT64_C(0), UINT64_C(9)}, UINT64_C(7)).cur_bank;
};

#endif // INCLUDED_SET_CUR_BANK_MODULO
