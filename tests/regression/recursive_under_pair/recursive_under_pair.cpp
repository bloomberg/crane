#include "recursive_under_pair.h"

/// A constructor field holding the inductive under a pair
/// (N : (nat * c) -> c) is stored as shared_ptr<pair<uint64_t, c>>.  The
/// pattern match must dereference the pointer before projecting .second.
RecursiveUnderPair::c RecursiveUnderPair::build(uint64_t n) {
  if (n <= 0) {
    return c::stop();
  } else {
    uint64_t m = n - 1;
    return c::n(std::make_pair(n, build(m)));
  }
}

uint64_t RecursiveUnderPair::depth(const RecursiveUnderPair::c &x) {
  if (std::holds_alternative<typename RecursiveUnderPair::c::Stop>(x.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0] = std::get<typename RecursiveUnderPair::c::N>(x.v());
    return (depth((*a0).second) + 1);
  }
}
