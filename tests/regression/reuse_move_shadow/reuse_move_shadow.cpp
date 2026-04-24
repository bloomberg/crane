#include <reuse_move_shadow.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
ReuseMoveShadow::tree_sum(const ReuseMoveShadow::tree &t) {
  if (std::holds_alternative<typename ReuseMoveShadow::tree::Node>(t.v())) {
    const auto &[d_a0, d_a1, d_a2] =
        std::get<typename ReuseMoveShadow::tree::Node>(t.v());
    return ((d_a0 + tree_sum(*(d_a1))) + tree_sum(*(d_a2)));
  } else {
    return 0u;
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
__attribute__((pure)) ReuseMoveShadow::tree
ReuseMoveShadow::dup_left(ReuseMoveShadow::tree t, const bool &b) {
  if (b) {
    if (std::holds_alternative<typename ReuseMoveShadow::tree::Node>(t.v())) {
      const auto &[d_a0, d_a1, d_a2] =
          std::get<typename ReuseMoveShadow::tree::Node>(t.v());
      return tree::node(d_a0, *(d_a1), *(d_a1));
    } else {
      return tree::leaf();
    }
  } else {
    return t;
  }
}
