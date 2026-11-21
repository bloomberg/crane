#include "immortal_global_constant.h"

ImmortalGlobalConstant::tree ImmortalGlobalConstant::full(uint64_t d) {
  if (d <= 0) {
    return tree::leaf();
  } else {
    uint64_t k = d - 1;
    return tree::node(full(k), d, full(k));
  }
}

uint64_t ImmortalGlobalConstant::size(const ImmortalGlobalConstant::tree &t) {
  if (crane::holds_alternative<typename ImmortalGlobalConstant::tree::Leaf>(
          t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, _, a2] =
        crane::get<typename ImmortalGlobalConstant::tree::Node>(t.v());
    return ((size(*a0) + size(*a2)) + 1);
  }
}

List<uint64_t> ImmortalGlobalConstant::upto(uint64_t n, List<uint64_t> acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t k = n - 1;
    return upto(k, List<uint64_t>::cons(n, std::move(acc)));
  }
}

/// Built at run time: counted.
ImmortalGlobalConstant::tree ImmortalGlobalConstant::fresh(uint64_t x0_) {
  return full(x0_);
}

/// A copy of the global per call.
uint64_t ImmortalGlobalConstant::sizes(uint64_t n) {
  return upto(n, List<uint64_t>::nil()).template fold_left<uint64_t>(
      [](uint64_t acc, uint64_t) { return (acc + size(table)); }, UINT64_C(0));
}
