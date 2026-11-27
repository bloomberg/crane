#include "non_uniform_pair_nest.h"

uint64_t NonUniformPairNest::size(const NonUniformPairNest::nest &n) {
  if (std::holds_alternative<typename NonUniformPairNest::nest::NZ>(n.v())) {
    return UINT64_C(1);
  } else {
    const auto &[a0] = std::get<typename NonUniformPairNest::nest::NS>(n.v());
    return (UINT64_C(2) * size(*a0));
  }
}
