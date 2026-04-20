#include <reuse_tag_mismatch.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// The 'else d' branch causes d to escape (returned in tail position).
/// This makes d "owned" (infer_owned_params marks it).
/// The 'then' branch's match has reuse candidates because:
/// - GoUp/GoDown are the same inductive (direction)
/// - Both have arity 1
/// But GoUp and GoDown are DIFFERENT constructors.
std::shared_ptr<ReuseTagMismatch::direction>
ReuseTagMismatch::id_or_flip(std::shared_ptr<ReuseTagMismatch::direction> d,
                             const bool flip_flag) {
  if (flip_flag) {
    if (std::holds_alternative<typename ReuseTagMismatch::direction::GoUp>(
            d->v())) {
      if (d.use_count() == 1) {
        auto &_rf =
            std::get<typename ReuseTagMismatch::direction::GoUp>(d->v_mut());
        unsigned int n = std::move(_rf.d_a0);
        _rf.d_a0 = n;
        return d;
      } else {
        const auto &[d_a0] =
            std::get<typename ReuseTagMismatch::direction::GoUp>(d->v());
        return direction::godown(d_a0);
      }

    } else {
      const auto &[d_a0] =
          std::get<typename ReuseTagMismatch::direction::GoDown>(d->v());
      return direction::goup(d_a0);
    }
  } else {
    return d;
  }
}
