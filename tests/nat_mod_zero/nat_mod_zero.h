#ifndef INCLUDED_NAT_MOD_ZERO
#define INCLUDED_NAT_MOD_ZERO

#include <utility>

struct NatModZero {
  static uint64_t my_mod(uint64_t _x0, uint64_t _x1);
  static std::pair<uint64_t, uint64_t> divmod(uint64_t a, uint64_t b);
};

#endif // INCLUDED_NAT_MOD_ZERO
