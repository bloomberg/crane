#include "reuse_move_shadow.h"

uint64_t ReuseMoveShadow::tree_sum(const ReuseMoveShadow::tree &t) {
  if (std::holds_alternative<typename ReuseMoveShadow::tree::Node>(t.v())) {
    const auto &[a0, a1, a2] =
        std::get<typename ReuseMoveShadow::tree::Node>(t.v());
    return ((a0 + tree_sum(*a1)) + tree_sum(*a2));
  } else {
    return UINT64_C(0);
  }
}

/// BUG: The reuse branch does not shift move_dead_after or
/// move_owned_vars when pushing pattern variables.
///
/// In dup_left, the parameter t is at de Bruijn index 2, and is owned
/// (escapes in the else branch).  After pushing 3 pattern variables
/// (v at 1, l at 2, r at 3), the pattern variable l lands at index 2 —
/// colliding with the un-shifted index for t in move_dead_after and
/// move_owned_vars.
///
/// The non-reuse path correctly calls with_shifted_move_tracking which
/// shifts both sets by n_pat_vars and clears move_dead_after.  But the
/// reuse path (lines ~4537-4602 in translation.ml) calls
/// process_match_pattern_vars WITHOUT shifting.
///
/// Since l appears TWICE in the body (node v l l), the assign loop
/// generates gen_expr body_env (MLrel 2) for each.  Both checks hit
/// move_dead_after and move_owned_vars at index 2 (thinking it refers to
/// the dead/owned t), so both emit std::move(l):
///
/// _rf.d_a1 = std::move(l);   // l moved, now null
/// _rf.d_a2 = std::move(l);   // l is null!  assigns null
///
/// The returned tree has d_a2 = nullptr.  Traversing the right subtree
/// crashes with a null-pointer dereference.
ReuseMoveShadow::tree ReuseMoveShadow::dup_left(ReuseMoveShadow::tree t,
                                                bool b) {
  if (b) {
    if (std::holds_alternative<typename ReuseMoveShadow::tree::Node>(
            t.v_mut())) {
      auto &[a0, a1, a2] =
          std::get<typename ReuseMoveShadow::tree::Node>(t.v_mut());
      return tree::node(std::move(a0), *a1, *a1);
    } else {
      return tree::leaf();
    }
  } else {
    return t;
  }
}
