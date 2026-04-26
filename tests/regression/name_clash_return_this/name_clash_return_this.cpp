#include <name_clash_return_this.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Inner match returns shape in all branches, one branch returns the
/// argument itself. The function takes shape as input, so it gets
/// methodified. In the Blue branch, `s` becomes `this`.
__attribute__((pure)) NameClashReturnThis::shape
NameClashReturnThis::maybe_transform(const bool &flag,
                                     NameClashReturnThis::shape s) {
  if (flag) {
    if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
            s.v())) {
      const auto &[d_a0] =
          std::get<typename NameClashReturnThis::shape::Circle>(s.v());
      return shape::square(d_a0, d_a0);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename NameClashReturnThis::shape::Square>(s.v());
      return shape::circle((d_a0 + d_a1));
    }
  } else {
    return s;
  }
}

/// Match on shape where one branch returns the same shape unchanged.
__attribute__((pure)) NameClashReturnThis::shape
NameClashReturnThis::identity_or_double(const NameClashReturnThis::shape &s) {
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          s.v())) {
    const auto &[d_a0] =
        std::get<typename NameClashReturnThis::shape::Circle>(s.v());
    return shape::circle((d_a0 * 2u));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashReturnThis::shape::Square>(s.v());
    return shape::square(d_a0, d_a1);
  }
}

/// Two shapes, return one of them based on a match on the other.
__attribute__((pure)) NameClashReturnThis::shape
NameClashReturnThis::pick_shape(NameClashReturnThis::shape s1,
                                NameClashReturnThis::shape s2) {
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          s1.v())) {
    return s2;
  } else {
    return s1;
  }
}

/// Nested: match on result of a function that may return this
__attribute__((pure)) unsigned int
NameClashReturnThis::nested_this(const NameClashReturnThis::shape &s) {
  auto &&_sv = identity_or_double(s);
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          _sv.v())) {
    const auto &[d_a0] =
        std::get<typename NameClashReturnThis::shape::Circle>(_sv.v());
    return d_a0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashReturnThis::shape::Square>(_sv.v());
    return (d_a0 + d_a1);
  }
}
