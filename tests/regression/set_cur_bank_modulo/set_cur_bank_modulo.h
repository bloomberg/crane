#ifndef INCLUDED_SET_CUR_BANK_MODULO
#define INCLUDED_SET_CUR_BANK_MODULO

#include <cstdint>
#include <utility>

struct SetCurBankModulo {
  static constexpr uint64_t NBANKS = UINT64_C(4);

  struct state {
    uint64_t cur_bank;
    uint64_t acc;
  };

  static state set_cur_bank(const state &s, uint64_t b);
  static constexpr uint64_t t = UINT64_C(3);
};

#endif // INCLUDED_SET_CUR_BANK_MODULO
