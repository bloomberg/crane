#include <reuse_scrutinee.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// Extract the value from the left subtree.
/// This accesses the Node's d_a0 field (left subtree).
__attribute__((pure)) unsigned int
ReuseScrutinee::left_val(const ReuseScrutinee::tree &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseScrutinee::tree::Node>(t.v());
    auto &&_sv0 = *(d_a0);
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(_sv0.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename ReuseScrutinee::tree::Node>(_sv0.v());
      return d_a10;
    }
  }
}

/// Extract the value from the right subtree.
__attribute__((pure)) unsigned int
ReuseScrutinee::right_val(const ReuseScrutinee::tree &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseScrutinee::tree::Node>(t.v());
    auto &&_sv0 = *(d_a2);
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(_sv0.v())) {
      return 0u;
    } else {
      const auto &[d_a00, d_a10, d_a20] =
          std::get<typename ReuseScrutinee::tree::Node>(_sv0.v());
      return d_a10;
    }
  }
}

/// Sum of left and right subtree values.
__attribute__((pure)) unsigned int
ReuseScrutinee::subtree_sum(const ReuseScrutinee::tree &t) {
  return (left_val(t) + right_val(t));
}
