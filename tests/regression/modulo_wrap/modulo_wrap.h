#ifndef INCLUDED_MODULO_WRAP
#define INCLUDED_MODULO_WRAP

#include <cstdint>
#include <utility>

struct Nat {
  static uint64_t pow(uint64_t n, uint64_t m);
};

struct ModuloWrap {
  static uint64_t addr12_of_nat(uint64_t n);
  static constexpr uint64_t test_addr12_wrap = UINT64_C(5);
  static uint64_t byte_of_nat(uint64_t n);
  static constexpr uint64_t test_byte_wrap = UINT64_C(7);
  static uint64_t nibble_of_nat(uint64_t n);
  static constexpr uint64_t test_nibble_wrap = UINT64_C(3);
  static inline const std::pair<std::pair<uint64_t, uint64_t>, uint64_t> t =
      std::make_pair(std::make_pair(test_addr12_wrap, test_byte_wrap),
                     test_nibble_wrap);
};

#endif // INCLUDED_MODULO_WRAP
