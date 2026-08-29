#include "double_option_nest.h"

DoubleOptionNest::t DoubleOptionNest::wrap(uint64_t k,
                                           DoubleOptionNest::t acc) {
  return t::node(k,
                 std::make_optional<std::optional<DoubleOptionNest::t>>(
                     std::make_optional<DoubleOptionNest::t>(std::move(acc))));
}

uint64_t DoubleOptionNest::peek(const DoubleOptionNest::t &x) {
  const auto &[a0, a1] = std::get<typename DoubleOptionNest::t::Node>(x.v());
  if ((*a1).has_value()) {
    const std::optional<DoubleOptionNest::t> &i = *(*a1);
    if (i.has_value()) {
      const DoubleOptionNest::t &u = *i;
      const auto &[a00, a10] =
          std::get<typename DoubleOptionNest::t::Node>(u.v());
      return (a0 + a00);
    } else {
      return (a0 + UINT64_C(1));
    }
  } else {
    return a0;
  }
}
