#ifndef INCLUDED_MODULO_WRAP
#define INCLUDED_MODULO_WRAP

#include <utility>

struct Nat {
  static uint64_t pow(uint64_t n, uint64_t m);
};

struct ModuloWrap {
  static uint64_t addr12_of_nat(uint64_t n);
  static inline const uint64_t test_addr12_wrap =
      addr12_of_nat((Nat::pow(UINT64_C(2), UINT64_C(12)) + UINT64_C(5)));
  static uint64_t byte_of_nat(uint64_t n);
  static inline const uint64_t test_byte_wrap = byte_of_nat(UINT64_C(263));
  static uint64_t nibble_of_nat(uint64_t n);
  static inline const uint64_t test_nibble_wrap = nibble_of_nat(UINT64_C(19));
  static inline const std::pair<std::pair<uint64_t, uint64_t>, uint64_t> t =
      std::make_pair(std::make_pair(test_addr12_wrap, test_byte_wrap),
                     test_nibble_wrap);
};

#endif // INCLUDED_MODULO_WRAP
