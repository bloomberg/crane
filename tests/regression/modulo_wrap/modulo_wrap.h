#ifndef INCLUDED_MODULO_WRAP
#define INCLUDED_MODULO_WRAP

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct Nat {
  static unsigned int pow(const unsigned int &n, const unsigned int &m);
};

struct ModuloWrap {
  static unsigned int addr12_of_nat(const unsigned int &n);
  static inline const unsigned int test_addr12_wrap =
      addr12_of_nat((Nat::pow(2u, 12u) + 5u));
  static unsigned int byte_of_nat(const unsigned int &n);
  static inline const unsigned int test_byte_wrap = byte_of_nat(263u);
  static unsigned int nibble_of_nat(const unsigned int &n);
  static inline const unsigned int test_nibble_wrap = nibble_of_nat(19u);
  static inline const std::pair<std::pair<unsigned int, unsigned int>,
                                unsigned int>
      t = std::make_pair(std::make_pair(test_addr12_wrap, test_byte_wrap),
                         test_nibble_wrap);
};

#endif // INCLUDED_MODULO_WRAP
