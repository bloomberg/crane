#include <fix_escape_match.h>

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// A local fixpoint inside a match branch capturing a pattern variable.
/// The pattern variable h is a structured binding reference into the
/// shared_ptr's data. The fixpoint captures it by &, then escapes
/// through an option constructor. After the match IIFE returns,
/// h is destroyed — invoking the closure is use-after-free.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
FixEscapeMatch::make_fn_from_head(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    auto add = std::make_shared<std::function<unsigned int(unsigned int)>>();
    *add = [=](unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return d_a0;
      } else {
        unsigned int x_ = x - 1;
        return ((*add)(x_) + 1);
      }
    };
    return std::make_optional<std::function<unsigned int(unsigned int)>>(
        (*add));
  }
}

/// Variant: fixpoint captures TWO pattern variables from the match.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
FixEscapeMatch::make_fn_from_pair(const List<unsigned int> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l.v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l.v());
    List<unsigned int> d_a1_value = List<unsigned int>(*(d_a1));
    if (std::holds_alternative<typename List<unsigned int>::Nil>(
            d_a1_value.v())) {
      return std::optional<std::function<unsigned int(unsigned int)>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(d_a1_value.v());
      auto combine =
          std::make_shared<std::function<unsigned int(unsigned int)>>();
      *combine = [=](unsigned int x) mutable -> unsigned int {
        if (x <= 0) {
          return (d_a0 + d_a00);
        } else {
          unsigned int x_ = x - 1;
          return ((*combine)(x_) + 1);
        }
      };
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          (*combine));
    }
  }
}
