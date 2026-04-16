#include <reuse_scrutinee.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Extract the value from the left subtree.
/// This accesses the Node's d_a0 field (left subtree).
__attribute__((pure)) unsigned int
ReuseScrutinee::left_val(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseScrutinee::tree::Node>(t->v());
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(
            d_a0->v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename ReuseScrutinee::tree::Node>(d_a0->v());
      return d_a10;
    }
  }
}

/// Extract the value from the right subtree.
__attribute__((pure)) unsigned int
ReuseScrutinee::right_val(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseScrutinee::tree::Node>(t->v());
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(
            d_a2->v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename ReuseScrutinee::tree::Node>(d_a2->v());
      return d_a10;
    }
  }
}

/// Sum of left and right subtree values.
__attribute__((pure)) unsigned int
ReuseScrutinee::subtree_sum(const std::shared_ptr<ReuseScrutinee::tree> &t) {
  return (left_val(t) + right_val(t));
}
