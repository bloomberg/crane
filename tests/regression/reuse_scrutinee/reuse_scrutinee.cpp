#include "reuse_scrutinee.h"

/// Extract the value from the left subtree.
/// This accesses the Node's d_a0 field (left subtree).
unsigned int ReuseScrutinee::left_val(const ReuseScrutinee::tree &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename ReuseScrutinee::tree::Node>(t.v());
    auto &&_sv0 = *a0;
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(_sv0.v())) {
      return 0u;
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename ReuseScrutinee::tree::Node>(_sv0.v());
      return a10;
    }
  }
}

/// Extract the value from the right subtree.
unsigned int ReuseScrutinee::right_val(const ReuseScrutinee::tree &t) {
  if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(t.v())) {
    return 0u;
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename ReuseScrutinee::tree::Node>(t.v());
    auto &&_sv0 = *a2;
    if (std::holds_alternative<typename ReuseScrutinee::tree::Leaf>(_sv0.v())) {
      return 0u;
    } else {
      const auto &[a00, a10, a20] =
          std::get<typename ReuseScrutinee::tree::Node>(_sv0.v());
      return a10;
    }
  }
}

/// Sum of left and right subtree values.
unsigned int ReuseScrutinee::subtree_sum(const ReuseScrutinee::tree &t) {
  return (left_val(t) + right_val(t));
}
