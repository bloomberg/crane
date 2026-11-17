#include "reuse_tag_mismatch.h"

/// The 'else d' branch causes d to escape (returned in tail position).
/// This makes d "owned" (infer_owned_params marks it).
/// The 'then' branch's match has reuse candidates because:
/// - GoUp/GoDown are the same inductive (direction)
/// - Both have arity 1
/// But GoUp and GoDown are DIFFERENT constructors.
ReuseTagMismatch::direction
ReuseTagMismatch::id_or_flip(const ReuseTagMismatch::direction &d,
                             bool flip_flag) {
  if (flip_flag) {
    if (std::holds_alternative<typename ReuseTagMismatch::direction::GoUp>(
            d.v())) {
      const auto &[a0] =
          std::get<typename ReuseTagMismatch::direction::GoUp>(d.v());
      return direction::godown(a0);
    } else {
      const auto &[a0] =
          std::get<typename ReuseTagMismatch::direction::GoDown>(d.v());
      return direction::goup(a0);
    }
  } else {
    return d;
  }
}
