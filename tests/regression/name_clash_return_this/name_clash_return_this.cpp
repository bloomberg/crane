#include <name_clash_return_this.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Inner match returns shape in all branches, one branch returns the
/// argument itself. The function takes shape as input, so it gets
/// methodified. In the Blue branch, `s` becomes `this`.
std::shared_ptr<NameClashReturnThis::shape>
NameClashReturnThis::maybe_transform(
    const bool flag, std::shared_ptr<NameClashReturnThis::shape> s) {
  if (flag) {
    if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
            s->v())) {
      const auto &[d_a0] =
          std::get<typename NameClashReturnThis::shape::Circle>(s->v());
      return shape::square(d_a0, d_a0);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename NameClashReturnThis::shape::Square>(s->v());
      return shape::circle((d_a0 + d_a1));
    }
  } else {
    return s;
  }
}

/// Match on shape where one branch returns the same shape unchanged.
std::shared_ptr<NameClashReturnThis::shape>
NameClashReturnThis::identity_or_double(
    const std::shared_ptr<NameClashReturnThis::shape> &s) {
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          s->v())) {
    const auto &[d_a0] =
        std::get<typename NameClashReturnThis::shape::Circle>(s->v());
    return shape::circle((d_a0 * 2u));
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashReturnThis::shape::Square>(s->v());
    return shape::square(d_a0, d_a1);
  }
}

/// Two shapes, return one of them based on a match on the other.
std::shared_ptr<NameClashReturnThis::shape> NameClashReturnThis::pick_shape(
    std::shared_ptr<NameClashReturnThis::shape> s1,
    std::shared_ptr<NameClashReturnThis::shape> s2) {
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          s1->v())) {
    return s2;
  } else {
    return s1;
  }
}

/// Nested: match on result of a function that may return this
__attribute__((pure)) unsigned int NameClashReturnThis::nested_this(
    const std::shared_ptr<NameClashReturnThis::shape> &s) {
  auto &&_sv = identity_or_double(s);
  if (std::holds_alternative<typename NameClashReturnThis::shape::Circle>(
          _sv->v())) {
    const auto &[d_a0] =
        std::get<typename NameClashReturnThis::shape::Circle>(_sv->v());
    return d_a0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename NameClashReturnThis::shape::Square>(_sv->v());
    return (d_a0 + d_a1);
  }
}
