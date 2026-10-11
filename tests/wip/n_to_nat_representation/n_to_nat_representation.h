#ifndef INCLUDED_N_TO_NAT_REPRESENTATION
#define INCLUDED_N_TO_NAT_REPRESENTATION

#include <algorithm>
#include <cstdint>

struct Nat {};

struct N {};

struct NToNatRepresentation {
  static constexpr unsigned int n = 300u;
  static inline const uint64_t larger =
      std::max(static_cast<unsigned int>(n), UINT64_C(5));
  static inline const uint64_t smaller =
      std::min(UINT64_C(7), static_cast<unsigned int>(n));
  static inline const uint64_t big = static_cast<unsigned int>(
      static_cast<unsigned int>(UINT64_C(5000000000)));
};

#endif // INCLUDED_N_TO_NAT_REPRESENTATION
