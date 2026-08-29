#include "recursive_under_option.h"

RecursiveUnderOption::c RecursiveUnderOption::build(uint64_t n) {
  if (n <= 0) {
    return c::n(std::optional<RecursiveUnderOption::c>());
  } else {
    uint64_t m = n - 1;
    return c::n(std::make_optional<RecursiveUnderOption::c>(build(m)));
  }
}

uint64_t RecursiveUnderOption::depth(const RecursiveUnderOption::c &x) {
  const auto &[a0] = std::get<typename RecursiveUnderOption::c::N>(x.v());
  if ((*a0).has_value()) {
    const RecursiveUnderOption::c &y = *(*a0);
    return (depth(y) + 1);
  } else {
    return UINT64_C(0);
  }
}
