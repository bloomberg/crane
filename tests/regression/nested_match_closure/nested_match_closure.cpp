#include <nested_match_closure.h>

__attribute__((pure)) unsigned int
NestedMatchClosure::tree_sum(const NestedMatchClosure::tree &t) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    return ((tree_sum(*(d_a0)) + d_a1) + tree_sum(*(d_a2)));
  }
}

/// Pattern 1: Nested match creating a closure that captures from both levels.
/// The fixpoint go captures outer_val from outer match and
/// inner_val from inner match. Both are structured binding refs.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
NestedMatchClosure::make_combiner(const NestedMatchClosure::tree &t) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    NestedMatchClosure::tree d_a0_value = *(d_a0);
    if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(
            d_a0_value.v())) {
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          [=](const unsigned int &x) mutable { return (d_a1 + x); });
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename NestedMatchClosure::tree::Node>(d_a0_value.v());
      unsigned int combined = (d_a1 + d_a10);
      auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
      *go = [=](unsigned int x) mutable -> unsigned int {
        if (x <= 0) {
          return combined;
        } else {
          unsigned int x_ = x - 1;
          return ((*go)(x_) + 1);
        }
      };
      return std::make_optional<std::function<unsigned int(unsigned int)>>(
          (*go));
    }
  }
}

/// Pattern 2: Triple nesting
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
NestedMatchClosure::make_deep_combiner(const NestedMatchClosure::tree &t) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    NestedMatchClosure::tree d_a0_value = *(d_a0);
    if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(
            d_a0_value.v())) {
      return std::optional<std::function<unsigned int(unsigned int)>>();
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename NestedMatchClosure::tree::Node>(d_a0_value.v());
      NestedMatchClosure::tree d_a00_value = *(d_a00);
      if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(
              d_a00_value.v())) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        const auto &[d_a01, d_a11, d_a21] =
            std::get<typename NestedMatchClosure::tree::Node>(d_a00_value.v());
        unsigned int total = ((d_a1 + d_a10) + d_a11);
        auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
        *go = [=](unsigned int x) mutable -> unsigned int {
          if (x <= 0) {
            return total;
          } else {
            unsigned int x_ = x - 1;
            return ((*go)(x_) + 1);
          }
        };
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            (*go));
      }
    }
  }
}

/// Pattern 3: Closure capturing variables from match AND function param.
/// The fixpoint captures BOTH pattern variables AND the function parameter.
/// After the function returns, BOTH the pattern variables AND the
/// function parameter are dead.
__attribute__((pure)) std::optional<std::function<unsigned int(unsigned int)>>
NestedMatchClosure::make_param_combiner(const NestedMatchClosure::tree &t,
                                        unsigned int base) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return std::optional<std::function<unsigned int(unsigned int)>>();
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    NestedMatchClosure::tree d_a0_value = *(d_a0);
    NestedMatchClosure::tree d_a2_value = *(d_a2);
    auto go = std::make_shared<std::function<unsigned int(unsigned int)>>();
    *go = [=](unsigned int x) mutable -> unsigned int {
      if (x <= 0) {
        return (((base + d_a1) + tree_sum(d_a0_value)) + tree_sum(d_a2_value));
      } else {
        unsigned int x_ = x - 1;
        return ((*go)(x_) + 1);
      }
    };
    return std::make_optional<std::function<unsigned int(unsigned int)>>((*go));
  }
}
