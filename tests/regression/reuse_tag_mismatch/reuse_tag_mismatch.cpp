#include <reuse_tag_mismatch.h>

/// The 'else d' branch causes d to escape (returned in tail position).
/// This makes d "owned" (infer_owned_params marks it).
/// The 'then' branch's match has reuse candidates because:
/// - GoUp/GoDown are the same inductive (direction)
/// - Both have arity 1
/// But GoUp and GoDown are DIFFERENT constructors.
__attribute__((pure)) ReuseTagMismatch::direction
ReuseTagMismatch::id_or_flip(ReuseTagMismatch::direction d,
                             const bool &flip_flag) {
  if (flip_flag) {
    if (std::holds_alternative<typename ReuseTagMismatch::direction::GoUp>(
            d.v_mut())) {
      auto &[d_a0] =
          std::get<typename ReuseTagMismatch::direction::GoUp>(d.v_mut());
      return direction::godown(d_a0);
    } else {
      auto &[d_a0] =
          std::get<typename ReuseTagMismatch::direction::GoDown>(d.v_mut());
      return direction::goup(d_a0);
    }
  } else {
    return d;
  }
}
