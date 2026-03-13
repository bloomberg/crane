#ifndef INCLUDED_MODULO_WRAP
#define INCLUDED_MODULO_WRAP

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
  __attribute__((pure)) static unsigned int pow(const unsigned int n,
                                                const unsigned int m);
};

struct ModuloWrap {
  __attribute__((pure)) static unsigned int addr12_of_nat(const unsigned int n);
  static inline const unsigned int test_addr12_wrap =
      addr12_of_nat((Nat::pow(2u, 12u) + 5u));
  __attribute__((pure)) static unsigned int byte_of_nat(const unsigned int n);
  static inline const unsigned int test_byte_wrap = byte_of_nat(263u);
  __attribute__((pure)) static unsigned int nibble_of_nat(const unsigned int n);
  static inline const unsigned int test_nibble_wrap = nibble_of_nat(19u);
  static inline const std::pair<std::pair<unsigned int, unsigned int>,
                                unsigned int>
      t = std::make_pair(std::make_pair(test_addr12_wrap, test_byte_wrap),
                         test_nibble_wrap);
};

#endif // INCLUDED_MODULO_WRAP
