#include "immortal_sticky_count.h"

ImmortalStickyCount::tree ImmortalStickyCount::full(uint64_t d) {
  if (d <= 0) {
    return tree::leaf();
  } else {
    uint64_t k = d - 1;
    return tree::node(full(k), d, full(k));
  }
}

uint64_t ImmortalStickyCount::size(const ImmortalStickyCount::tree &t) {
  if (crane::holds_alternative<typename ImmortalStickyCount::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, _, a2] =
        crane::get<typename ImmortalStickyCount::tree::Node>(t.v());
    return ((size(*a0) + size(*a2)) + 1);
  }
}

/// Built at run time: counted.
ImmortalStickyCount::tree ImmortalStickyCount::fresh(uint64_t x0_) {
  return full(x0_);
}

/// n uses of the global, each a copy.
uint64_t ImmortalStickyCount::sizes(uint64_t n, uint64_t acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t k = n - 1;
    return sizes(k, (acc + size(table)));
  }
}
