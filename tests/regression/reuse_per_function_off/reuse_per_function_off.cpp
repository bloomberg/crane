#include "reuse_per_function_off.h"

ReusePerFunctionOff::lst
ReusePerFunctionOff::incr_reused(ReusePerFunctionOff::lst l) {
  // Reuse the matched cell in place when this is its only owner; otherwise
  // rebuild.
  if (l.v().index() == 1) {
    if (std::get<typename ReusePerFunctionOff::lst::Cons>(l.v_mut()).a1.use_count() ==
        1) {
      uint64_t x = std::move(
          std::get<typename ReusePerFunctionOff::lst::Cons>(l.v_mut()).a0);
      ReusePerFunctionOff::lst xs = std::move(
          *std::get<typename ReusePerFunctionOff::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(std::move(
          std::get<typename ReusePerFunctionOff::lst::Cons>(l.v_mut()).a1),
                                   (x + 1), incr_reused(std::move(xs)));
    } else {
      if (std::holds_alternative<typename ReusePerFunctionOff::lst::Nil>(
              l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename ReusePerFunctionOff::lst::Cons>(l.v_mut());
        return lst::cons((std::move(a0) + 1), incr_reused(*a1));
      }
    }
  } else {
    if (std::holds_alternative<typename ReusePerFunctionOff::lst::Nil>(
            l.v_mut())) {
      return lst::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename ReusePerFunctionOff::lst::Cons>(l.v_mut());
      return lst::cons((std::move(a0) + 1), incr_reused(*a1));
    }
  }
}

ReusePerFunctionOff::lst
ReusePerFunctionOff::incr_fresh(const ReusePerFunctionOff::lst &l) {
  if (std::holds_alternative<typename ReusePerFunctionOff::lst::Nil>(l.v())) {
    return lst::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename ReusePerFunctionOff::lst::Cons>(l.v());
    return lst::cons(((a0 + 1) + 1), incr_fresh(*a1));
  }
}

ReusePerFunctionOff::lst ReusePerFunctionOff::upto(uint64_t n) {
  if (n <= 0) {
    return lst::nil();
  } else {
    uint64_t m = n - 1;
    return lst::cons(n, upto(m));
  }
}

uint64_t ReusePerFunctionOff::sum(const ReusePerFunctionOff::lst &l) {
  if (std::holds_alternative<typename ReusePerFunctionOff::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReusePerFunctionOff::lst::Cons>(l.v());
    return a0 + sum(*a1);
  }
}
