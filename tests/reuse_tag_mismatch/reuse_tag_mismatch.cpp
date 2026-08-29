#include "reuse_tag_mismatch.h"

ReuseTagMismatch::direction
ReuseTagMismatch::id_or_flip(ReuseTagMismatch::direction d, bool flip_flag) {
  if (flip_flag) {
    if (std::holds_alternative<typename ReuseTagMismatch::direction::GoUp>(
            d.v_mut())) {
      auto &[a0] =
          std::get<typename ReuseTagMismatch::direction::GoUp>(d.v_mut());
      return direction::godown(std::move(a0));
    } else {
      auto &[a0] =
          std::get<typename ReuseTagMismatch::direction::GoDown>(d.v_mut());
      return direction::goup(std::move(a0));
    }
  } else {
    return d;
  }
}
