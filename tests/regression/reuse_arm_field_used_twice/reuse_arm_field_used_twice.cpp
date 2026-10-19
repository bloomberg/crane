#include "reuse_arm_field_used_twice.h"

uint64_t ReuseArmFieldUsedTwice::len(const ReuseArmFieldUsedTwice::lst &l) {
  if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}

ReuseArmFieldUsedTwice::lst
ReuseArmFieldUsedTwice::app2(ReuseArmFieldUsedTwice::lst a,
                             ReuseArmFieldUsedTwice::lst b) {
  if (a.v().index() == 1) {
    if (std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(a.v_mut())
            .a1.use_count() == 1) {
      uint64_t x = std::move(
          std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(a.v_mut()).a0);
      ReuseArmFieldUsedTwice::lst xs = std::move(
          *std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(a.v_mut()).a1);
      return lst::cons_crane_reuse(
          std::move(
              std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(a.v_mut())
                  .a1),
          std::move(x), app2(std::move(xs), std::move(b)));
    } else {
      if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
              a.v_mut())) {
        return b;
      } else {
        auto &[a0, a1] =
            std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(a.v_mut());
        return lst::cons(std::move(a0), app2(*a1, std::move(b)));
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
            a.v_mut())) {
      return b;
    } else {
      auto &[a0, a1] =
          std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(a.v_mut());
      return lst::cons(std::move(a0), app2(*a1, std::move(b)));
    }
  }
}

ReuseArmFieldUsedTwice::lst
ReuseArmFieldUsedTwice::dbl(ReuseArmFieldUsedTwice::lst l) {
  if (l.v().index() == 1) {
    if (std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut())
            .a1.use_count() == 1) {
      uint64_t x = std::move(
          std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut()).a0);
      ReuseArmFieldUsedTwice::lst xs = std::move(
          *std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(
          std::move(
              std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut())
                  .a1),
          std::move(x), app2(xs, xs));
    } else {
      if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
              l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut());
        return lst::cons(std::move(a0), app2(*a1, *a1));
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
            l.v_mut())) {
      return lst::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut());
      return lst::cons(std::move(a0), app2(*a1, *a1));
    }
  }
}

ReuseArmFieldUsedTwice::lst
ReuseArmFieldUsedTwice::pairs(ReuseArmFieldUsedTwice::lst l) {
  if (l.v().index() == 1) {
    if (std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut())
            .a1.use_count() == 1) {
      uint64_t x = std::move(
          std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut()).a0);
      ReuseArmFieldUsedTwice::lst xs = std::move(
          *std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut()).a1);
      return lst::cons_crane_reuse(
          std::move(
              std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut())
                  .a1),
          (std::move(x) + len(xs)), pairs(xs));
    } else {
      if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
              l.v_mut())) {
        return lst::nil();
      } else {
        auto &[a0, a1] =
            std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut());
        return lst::cons((std::move(a0) + len(*a1)), pairs(*a1));
      }
    }
  } else {
    if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
            l.v_mut())) {
      return lst::nil();
    } else {
      auto &[a0, a1] =
          std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v_mut());
      return lst::cons((std::move(a0) + len(*a1)), pairs(*a1));
    }
  }
}

uint64_t ReuseArmFieldUsedTwice::sum(const ReuseArmFieldUsedTwice::lst &l) {
  if (std::holds_alternative<typename ReuseArmFieldUsedTwice::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseArmFieldUsedTwice::lst::Cons>(l.v());
    return (a0 + sum(*a1));
  }
}
