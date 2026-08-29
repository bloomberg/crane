#include "guard_compare_label_collision.h"

Comparison OK::compare(const Nat &x, const Nat &y) {
  if (&y == &x) {
    return Comparison::EQ;
  }
  if (std::holds_alternative<typename Nat::O>(x.v())) {
    if (std::holds_alternative<typename Nat::O>(y.v())) {
      return Comparison::EQ;
    } else {
      return Comparison::LT;
    }
  } else {
    const auto &[a0] = std::get<typename Nat::S>(x.v());
    if (std::holds_alternative<typename Nat::O>(y.v())) {
      return Comparison::GT;
    } else {
      const auto &[a00] = std::get<typename Nat::S>(y.v());
      return compare(*a0, *a00);
    }
  }
}

Compare<Ordered::T> Ordered::compare(Ordered::T x, Ordered::T y) {
  switch (x) {
  case T::A: {
    switch (y) {
    case T::A: {
      return Compare<Ordered::T>::eq();
    }
    case T::B: {
      return Compare<Ordered::T>::lt();
    }
    default:
      std::unreachable();
    }
    break;
  }
  case T::B: {
    switch (y) {
    case T::A: {
      return Compare<Ordered::T>::gt();
    }
    case T::B: {
      return Compare<Ordered::T>::eq();
    }
    default:
      std::unreachable();
    }
    break;
  }
  default:
    std::unreachable();
  }
}
