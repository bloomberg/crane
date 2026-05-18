#include "fix_escape_match.h"

/// A local fixpoint inside a match branch capturing a pattern variable.
/// The pattern variable h is a structured binding reference into the
/// shared_ptr's data. The fixpoint captures it by &, then escapes
/// through an option constructor. After the match IIFE returns,
/// h is destroyed — invoking the closure is use-after-free.
std::optional<std::function<uint64_t(uint64_t)>>
FixEscapeMatch::make_fn_from_head(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::optional<std::function<uint64_t(uint64_t)>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    auto add_impl = [=](auto &_self_add, uint64_t x) mutable -> uint64_t {
      if (x <= 0) {
        return a0;
      } else {
        uint64_t x_ = x - 1;
        return (_self_add(_self_add, x_) + 1);
      }
    };
    auto add = [=](uint64_t x) mutable -> uint64_t {
      return add_impl(add_impl, x);
    };
    return std::make_optional<std::function<uint64_t(uint64_t)>>(add);
  }
}

/// Variant: fixpoint captures TWO pattern variables from the match.
std::optional<std::function<uint64_t(uint64_t)>>
FixEscapeMatch::make_fn_from_pair(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return std::optional<std::function<uint64_t(uint64_t)>>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(a1_value.v())) {
      return std::optional<std::function<uint64_t(uint64_t)>>();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(a1_value.v());
      auto combine_impl = [=](auto &_self_combine,
                              uint64_t x) mutable -> uint64_t {
        if (x <= 0) {
          return (a0 + a00);
        } else {
          uint64_t x_ = x - 1;
          return (_self_combine(_self_combine, x_) + 1);
        }
      };
      auto combine = [=](uint64_t x) mutable -> uint64_t {
        return combine_impl(combine_impl, x);
      };
      return std::make_optional<std::function<uint64_t(uint64_t)>>(combine);
    }
  }
}
