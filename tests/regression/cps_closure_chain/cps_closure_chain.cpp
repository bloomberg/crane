#include "cps_closure_chain.h"

/// CPS-style tree traversal that builds a deep chain of continuations.
///
/// BUG HYPOTHESIS: Each recursive call creates a closure that captures
/// n (from the pattern match on the current node) and k (the
/// continuation from the caller). The chain of closures forms a
/// linked-list-like structure on the heap via std::function copies.
/// When the chain is finally invoked, each closure needs its captured
/// n to still be valid.
///
/// Unlike the fixpoint-escape tests in wip/, these are SIMPLE lambdas
/// (not local fixpoints), so they should use = capture. The question
/// is whether the = capture correctly copies all pattern variables,
/// especially when the pattern match is on a shared_ptr type and the
/// structured bindings are references.
uint64_t CpsClosureChain::tree_sum_cps(const CpsClosureChain::tree &t,
                                       const crane::fn<uint64_t(uint64_t)> &k) {
  if (std::holds_alternative<typename CpsClosureChain::tree::Leaf>(t.v())) {
    return k(UINT64_C(0));
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename CpsClosureChain::tree::Node>(t.v());
    const CpsClosureChain::tree &a0_value = *a0;
    const CpsClosureChain::tree &a2_value = *a2;
    return tree_sum_cps(
        a0_value, [=, a2_value = a2_value, k = k](uint64_t left_sum) {
          return tree_sum_cps(a2_value, [=, k = k](uint64_t right_sum) {
            return k(left_sum + a1 + right_sum);
          });
        });
  }
}

uint64_t CpsClosureChain::tree_sum(const CpsClosureChain::tree &t) {
  return tree_sum_cps(t, [](uint64_t x) { return x; });
}

/// Build a deep tree to stress the closure chain.
CpsClosureChain::tree CpsClosureChain::build_left(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t n_ = n - 1;
    return tree::node(build_left(n_), n, tree::leaf());
  }
}

CpsClosureChain::tree CpsClosureChain::build_right(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t n_ = n - 1;
    return tree::node(tree::leaf(), n, build_right(n_));
  }
}

CpsClosureChain::tree CpsClosureChain::build_balanced(uint64_t n) {
  if (n <= 0) {
    return tree::leaf();
  } else {
    uint64_t n_ = n - 1;
    return tree::node(build_balanced(n_), n, build_balanced(n_));
  }
}

/// CPS fold: accumulates results through continuation chain.
/// This creates closures that capture BOTH a pattern variable
/// AND the accumulator function.
uint64_t CpsClosureChain::tree_fold_cps(
    const CpsClosureChain::tree &t, uint64_t base,
    const crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)> &combine,
    const crane::fn<uint64_t(uint64_t)> &k) {
  if (std::holds_alternative<typename CpsClosureChain::tree::Leaf>(t.v())) {
    return k(base);
  } else {
    const auto &[a0, a1, a2] =
        std::get<typename CpsClosureChain::tree::Node>(t.v());
    const CpsClosureChain::tree &a0_value = *a0;
    const CpsClosureChain::tree &a2_value = *a2;
    return tree_fold_cps(a0_value, base, combine,
                         [=, a2_value = a2_value, combine = combine, k = k](
                             uint64_t left_result) {
                           return tree_fold_cps(
                               a2_value, base, combine,
                               [=, combine = combine, k = k](
                                   uint64_t right_result) {
                                 return k(
                                     combine(left_result, a1, right_result));
                               });
                         });
  }
}
