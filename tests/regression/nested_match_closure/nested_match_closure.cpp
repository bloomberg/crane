#include "nested_match_closure.h"

uint64_t NestedMatchClosure::tree_sum(const NestedMatchClosure::tree &t) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    return ((tree_sum(*a0) + a1) + tree_sum(*a2));
  }
}

/// Pattern 1: Nested match creating a closure that captures from both levels.
/// The fixpoint go captures outer_val from outer match and
/// inner_val from inner match. Both are structured binding refs.
std::optional<std::function<uint64_t(uint64_t)>>
NestedMatchClosure::make_combiner(const NestedMatchClosure::tree &t) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return std::optional<std::function<uint64_t(uint64_t)>>();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    const NestedMatchClosure::tree &a0_value = *a0;
    if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(
            a0_value.v())) {
      return std::make_optional<std::function<uint64_t(uint64_t)>>(
          [=](uint64_t x) mutable { return (a1 + x); });
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename NestedMatchClosure::tree::Node>(a0_value.v());
      uint64_t combined = (a1 + a10);
      auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
        if (x <= 0) {
          return combined;
        } else {
          uint64_t x_ = x - 1;
          return (_self_go(_self_go, x_) + 1);
        }
      };
      auto go = [=](uint64_t x) mutable -> uint64_t {
        return go_impl(go_impl, x);
      };
      return std::make_optional<std::function<uint64_t(uint64_t)>>(go);
    }
  }
}

/// Pattern 2: Triple nesting
std::optional<std::function<uint64_t(uint64_t)>>
NestedMatchClosure::make_deep_combiner(const NestedMatchClosure::tree &t) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return std::optional<std::function<uint64_t(uint64_t)>>();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    const NestedMatchClosure::tree &a0_value = *a0;
    if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(
            a0_value.v())) {
      return std::optional<std::function<uint64_t(uint64_t)>>();
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename NestedMatchClosure::tree::Node>(a0_value.v());
      const NestedMatchClosure::tree &a00_value = *a00;
      if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(
              a00_value.v())) {
        return std::optional<std::function<uint64_t(uint64_t)>>();
      } else {
        const auto &[a01, a11, a21] =
            std::get<typename NestedMatchClosure::tree::Node>(a00_value.v());
        uint64_t total = ((a1 + a10) + a11);
        auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
          if (x <= 0) {
            return total;
          } else {
            uint64_t x_ = x - 1;
            return (_self_go(_self_go, x_) + 1);
          }
        };
        auto go = [=](uint64_t x) mutable -> uint64_t {
          return go_impl(go_impl, x);
        };
        return std::make_optional<std::function<uint64_t(uint64_t)>>(go);
      }
    }
  }
}

/// Pattern 3: Closure capturing variables from match AND function param.
/// The fixpoint captures BOTH pattern variables AND the function parameter.
/// After the function returns, BOTH the pattern variables AND the
/// function parameter are dead.
std::optional<std::function<uint64_t(uint64_t)>>
NestedMatchClosure::make_param_combiner(const NestedMatchClosure::tree &t,
                                        uint64_t base) {
  if (std::holds_alternative<typename NestedMatchClosure::tree::Leaf>(t.v())) {
    return std::optional<std::function<uint64_t(uint64_t)>>();
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename NestedMatchClosure::tree::Node>(t.v());
    const NestedMatchClosure::tree &a0_value = *a0;
    const NestedMatchClosure::tree &a2_value = *a2;
    auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
      if (x <= 0) {
        return (((base + a1) + tree_sum(a0_value)) + tree_sum(a2_value));
      } else {
        uint64_t x_ = x - 1;
        return (_self_go(_self_go, x_) + 1);
      }
    };
    auto go = [=](uint64_t x) mutable -> uint64_t {
      return go_impl(go_impl, x);
    };
    return std::make_optional<std::function<uint64_t(uint64_t)>>(go);
  }
}
