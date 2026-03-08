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

struct Nat {
  static unsigned int pow(const unsigned int n, const unsigned int m);
};

struct PcInc1WrapModulo {
  struct state {
    unsigned int pc;
  };

  static unsigned int addr12_of_nat(const unsigned int n);

  static unsigned int pc_inc1(const std::shared_ptr<state> &s);

  static inline const unsigned int max_addr = ((
      (Nat::pow(2u, 12u) - 1u) > Nat::pow(2u, 12u) ? 0
                                                   : (Nat::pow(2u, 12u) - 1u)));

  static inline const unsigned int t =
      pc_inc1(std::make_shared<state>(state{max_addr}));
};
