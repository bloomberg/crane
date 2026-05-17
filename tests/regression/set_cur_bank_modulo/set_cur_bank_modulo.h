#ifndef INCLUDED_SET_CUR_BANK_MODULO
#define INCLUDED_SET_CUR_BANK_MODULO

#include <utility>

struct SetCurBankModulo {
  static inline const unsigned int NBANKS = 4u;

  struct state {
    unsigned int cur_bank;
    unsigned int acc;

    // ACCESSORS
    state clone() const { return state{(*this).cur_bank, (*this).acc}; }
  };

  static state set_cur_bank(const state &s, unsigned int b);
  static inline const unsigned int t = set_cur_bank(state{0u, 9u}, 7u).cur_bank;
};

#endif // INCLUDED_SET_CUR_BANK_MODULO
