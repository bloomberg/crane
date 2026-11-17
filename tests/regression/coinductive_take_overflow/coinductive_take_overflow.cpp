#include "coinductive_take_overflow.h"

CoinductiveTakeOverflow::stream<uint64_t>
CoinductiveTakeOverflow::from(uint64_t n) {
  return stream<uint64_t>::lazy_(
      [=]() -> typename CoinductiveTakeOverflow::stream<uint64_t>::Cons {
        return {n, from((n + 1))};
      });
}
