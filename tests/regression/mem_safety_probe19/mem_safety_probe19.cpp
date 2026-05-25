#include "mem_safety_probe19.h"

uint64_t MemSafetyProbe19::option_fn(const MemSafetyProbe19::tree &t,
                                     const MemSafetyProbe19::myopt<uint64_t> &o,
                                     uint64_t n) {
  if (std::holds_alternative<
          typename MemSafetyProbe19::myopt<uint64_t>::Mynone>(o.v())) {
    return n;
  } else {
    const auto &[a0] =
        std::get<typename MemSafetyProbe19::myopt<uint64_t>::Mysome>(o.v());
    return ((t.tree_sum() + a0) + n);
  }
}

uint64_t MemSafetyProbe19::choice_fn(const MemSafetyProbe19::tree &t,
                                     MemSafetyProbe19::Choice c, uint64_t n) {
  switch (c) {
  case Choice::CLEFT: {
    return (t.tree_sum() + n);
  } break;
  case Choice::CRIGHT: {
    return n;
  } break;
  case Choice::CBOTH: {
    return ((t.tree_sum() + t.tree_sum()) + n);
  } break;
  default:
    std::unreachable();
  }
}

/// TEST 4: Closure returned from if, capturing a locally-built tree.
/// The let-bound tree is on the stack. If the returned lambda
/// captures by &, it holds a reference to the dead stack frame.
uint64_t MemSafetyProbe19::make_adder(uint64_t n, bool b, uint64_t _x0) {
  return [=]() mutable {
    MemSafetyProbe19::tree t = tree::node(tree::leaf(), n, tree::leaf());
    return [=](uint64_t m) mutable {
      if (b) {
        return (t.tree_sum() + m);
      } else {
        return m;
      }
    };
  }()(_x0);
}
