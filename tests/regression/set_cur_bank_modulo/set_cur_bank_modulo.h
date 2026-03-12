#ifndef INCLUDED_SET_CUR_BANK_MODULO
#define INCLUDED_SET_CUR_BANK_MODULO

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct SetCurBankModulo {
  static inline const unsigned int NBANKS = 4u;

  struct state {
    unsigned int cur_bank;
    unsigned int acc;
  };

  static std::shared_ptr<state> set_cur_bank(std::shared_ptr<state> s,
                                             const unsigned int b);
  static inline const unsigned int t =
      set_cur_bank(std::make_shared<state>(state{0u, 9u}), 7u)->cur_bank;
};

#endif // INCLUDED_SET_CUR_BANK_MODULO
