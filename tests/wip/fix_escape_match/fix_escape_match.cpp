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
FixEscapeMatch::make_fn_from_head(
    const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    std::function<unsigned int(unsigned int)> add;
    add = [&](unsigned int x) -> unsigned int {
      if (x <= 0) {
        return d_a0;
      } else {
        unsigned int x_ = x - 1;
        return (add(x_) + 1);
      }
    };
    return std::make_optional<std::function<unsigned int(unsigned int)>>(add);
  }
}

/// Variant: fixpoint captures TWO pattern variables from the match.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
FixEscapeMatch::make_fn_from_pair(
    const std::shared_ptr<List<unsigned int>> &l) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(l->v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(l->v());
    if (std::holds_alternative<typename List<unsigned int>::Nil>(d_a1->v())) {
      return std::optional<std::function<unsigned int(unsigned int)>>();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(d_a1->v());
      std::function<unsigned int(unsigned int)> combine;
      combine = [&](unsigned int x) -> unsigned int {
        if (x <= 0) {
          return (d_a0 + d_a00);
        } else {
          unsigned int x_ = x - 1;
          return (combine(x_) + 1);
        }
      };
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          combine);
    }
  }
}
