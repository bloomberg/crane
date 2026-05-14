#include "mem_safety_probe19.h"

unsigned int
MemSafetyProbe19::option_fn(const MemSafetyProbe19::tree &t,
                            const MemSafetyProbe19::myopt<unsigned int> &o,
                            const unsigned int n) {
  if (std::holds_alternative<
          typename MemSafetyProbe19::myopt<unsigned int>::Mynone>(o.v())) {
    return n;
  } else {
    const auto &[d_a0] =
        std::get<typename MemSafetyProbe19::myopt<unsigned int>::Mysome>(o.v());
    return ((t.tree_sum() + d_a0) + n);
  }
}

unsigned int MemSafetyProbe19::choice_fn(const MemSafetyProbe19::tree &t,
                                         const MemSafetyProbe19::Choice c,
                                         const unsigned int n) {
  switch (c) {
  case Choice::e_CLEFT: {
    return (t.tree_sum() + n);
  }
  case Choice::e_CRIGHT: {
    return n;
  }
  case Choice::e_CBOTH: {
    return ((t.tree_sum() + t.tree_sum()) + n);
  }
  default:
    std::unreachable();
  }
}

/// TEST 4: Closure returned from if, capturing a locally-built tree.
/// The let-bound tree is on the stack. If the returned lambda
/// captures by &, it holds a reference to the dead stack frame.
unsigned int MemSafetyProbe19::make_adder(const unsigned int n, const bool b,
                                          const unsigned int _x0) {
  return [=]() mutable {
    MemSafetyProbe19::tree t = tree::node(tree::leaf(), n, tree::leaf());
    return [=](const unsigned int m) mutable {
      if (b) {
        return (t.tree_sum() + m);
      } else {
        return m;
      }
    };
  }()(_x0);
}
