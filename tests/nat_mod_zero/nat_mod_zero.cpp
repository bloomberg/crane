#include "nat_mod_zero.h"

uint64_t NatModZero::my_mod(uint64_t _x0, uint64_t _x1) {
  return (_x1 ? _x0 % _x1 : _x0);
}

std::pair<uint64_t, uint64_t> NatModZero::divmod(uint64_t a, uint64_t b) {
  return std::make_pair((b ? a / b : 0), (b ? a % b : a));
}
