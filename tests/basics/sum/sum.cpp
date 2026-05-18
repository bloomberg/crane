#include "sum.h"

uint64_t Sum::either_to_nat(const Sum::either<uint64_t, uint64_t> &e) {
  if (std::holds_alternative<typename Sum::either<uint64_t, uint64_t>::Left>(
          e.v())) {
    const auto &[a0] =
        std::get<typename Sum::either<uint64_t, uint64_t>::Left>(e.v());
    return a0;
  } else {
    const auto &[a0] =
        std::get<typename Sum::either<uint64_t, uint64_t>::Right>(e.v());
    return a0;
  }
}
