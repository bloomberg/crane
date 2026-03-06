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
  static inline const unsigned int NBANKS = ((((0 + 1) + 1) + 1) + 1);

  struct state {
    unsigned int cur_bank;
    unsigned int acc;
  };

  static unsigned int cur_bank(const std::shared_ptr<state> &s);

  static unsigned int acc(const std::shared_ptr<state> &s);

  static std::shared_ptr<state> set_cur_bank(std::shared_ptr<state> s,
                                             const unsigned int b);

  static inline const unsigned int t =
      set_cur_bank(
          std::make_shared<state>(state{
              0, (((((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1) + 1)}),
          (((((((0 + 1) + 1) + 1) + 1) + 1) + 1) + 1))
          ->cur_bank;
};
