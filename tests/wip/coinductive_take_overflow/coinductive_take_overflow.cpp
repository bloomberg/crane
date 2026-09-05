#include "coinductive_take_overflow.h"

CoinductiveTakeOverflow::stream<uint64_t>
CoinductiveTakeOverflow::from(uint64_t n) {
  return stream<uint64_t>::lazy_(
      [=]() mutable -> CoinductiveTakeOverflow::stream<uint64_t> {
        return stream<uint64_t>::cons(n, from((n + 1)));
      });
}
