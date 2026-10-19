#include "reuse_arm_field_order.h"

ReuseArmFieldOrder::lst
ReuseArmFieldOrder::zero_heads(ReuseArmFieldOrder::lst l) {
  if (l.v().index() == 1) {
    if (std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v_mut())
            .a1.use_count() == 1) {
      ReuseArmFieldOrder::lst xs = std::move(
          *std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(
          std::move(
              std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v_mut()).a1),
          UINT64_C(0), zero_heads(std::move(xs)));
    } else {
      if (std::holds_alternative<typename ReuseArmFieldOrder::lst::Nil>(
              l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v_mut());
        return lst::cons(UINT64_C(0), zero_heads(*a1));
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseArmFieldOrder::lst::Nil>(
            l.v_mut())) {
      return lst::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v_mut());
      return lst::cons(UINT64_C(0), zero_heads(*a1));
    }
  }
}

ReuseArmFieldOrder::lst
ReuseArmFieldOrder::keep_head(ReuseArmFieldOrder::lst l) {
  if (std::holds_alternative<typename ReuseArmFieldOrder::lst::Nil>(
          l.v_mut())) {
    return lst::nil();
  } else {
    auto &[a0, a1] =
        std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v_mut());
    return lst::cons(std::move(a0), lst::nil());
  }
}

uint64_t ReuseArmFieldOrder::sum(const ReuseArmFieldOrder::lst &l) {
  if (std::holds_alternative<typename ReuseArmFieldOrder::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v());
    return (a0 + sum(*a1));
  }
}

uint64_t ReuseArmFieldOrder::len(const ReuseArmFieldOrder::lst &l) {
  if (std::holds_alternative<typename ReuseArmFieldOrder::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseArmFieldOrder::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}
