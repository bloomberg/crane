#include "name_clash_return_this.h"

/// Inner match returns shape in all branches, one branch returns the
/// argument itself. The function takes shape as input, so it gets
/// methodified. In the Blue branch, `s` becomes `this`.
NameClashReturnThis::shape
NameClashReturnThis::maybe_transform(bool flag, NameClashReturnThis::shape s) {
  if (flag) {
    if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
            s.v_mut())) {
      auto &[a0] =
          std::get<typename NameClashReturnThis::shape::Circle>(s.v_mut());
      return shape::square(a0, a0);
    } else {
      auto &[a0, a1] =
          std::get<typename NameClashReturnThis::shape::Square>(s.v_mut());
      return shape::circle((std::move(a0) + std::move(a1)));
    }
  } else {
    return s;
  }
}

/// Match on shape where one branch returns the same shape unchanged.
NameClashReturnThis::shape
NameClashReturnThis::identity_or_double(const NameClashReturnThis::shape &s) {
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          s.v())) {
    const auto &[a0] =
        std::get<typename NameClashReturnThis::shape::Circle>(s.v());
    return shape::circle((a0 * 2u));
  } else {
    const auto &[a0, a1] =
        std::get<typename NameClashReturnThis::shape::Square>(s.v());
    return shape::square(a0, a1);
  }
}

/// Two shapes, return one of them based on a match on the other.
NameClashReturnThis::shape
NameClashReturnThis::pick_shape(NameClashReturnThis::shape s1,
                                NameClashReturnThis::shape s2) {
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          s1.v_mut())) {
    return s2;
  } else {
    return s1;
  }
}

/// Nested: match on result of a function that may return this
unsigned int
NameClashReturnThis::nested_this(const NameClashReturnThis::shape &s) {
  auto &&_sv = identity_or_double(s);
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          _sv.v())) {
    const auto &[a0] =
        std::get<typename NameClashReturnThis::shape::Circle>(_sv.v());
    return a0;
  } else {
    const auto &[a0, a1] =
        std::get<typename NameClashReturnThis::shape::Square>(_sv.v());
    return (a0 + a1);
  }
}
