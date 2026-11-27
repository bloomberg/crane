#include "non_uniform_list_nest.h"

uint64_t NonUniformListNest::depth(const NonUniformListNest::n2 &x) {
  if (std::holds_alternative<typename NonUniformListNest::n2::Z2>(x.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<typename NonUniformListNest::n2::S2>(x.v());
    return (depth(*a0) + 1);
  }
}
