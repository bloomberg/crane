#ifndef INCLUDED_SET_CUR_BANK_MODULO
#define INCLUDED_SET_CUR_BANK_MODULO

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct SetCurBankModulo {
  static inline const unsigned int NBANKS = 4u;

  struct state {
    unsigned int cur_bank;
    unsigned int acc;

    // ACCESSORS
    __attribute__((pure)) state clone() const {
      return state{(*(this)).cur_bank, (*(this)).acc};
    }
  };

  __attribute__((pure)) static state set_cur_bank(const state &s,
                                                  const unsigned int &b);
  static inline const unsigned int t = set_cur_bank(state{0u, 9u}, 7u).cur_bank;
};

#endif // INCLUDED_SET_CUR_BANK_MODULO
