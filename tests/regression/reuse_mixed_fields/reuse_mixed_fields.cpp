#include "reuse_mixed_fields.h"

/// Forces d to be owned through the else branch.
/// The match branch has reuse candidates: both AsNat and AsPair
/// have arity 2.
ReuseMixedFields::payload
ReuseMixedFields::swap_tag_or_id(ReuseMixedFields::payload p, bool do_swap) {
  if (do_swap) {
    if (std::holds_alternative<typename ReuseMixedFields::payload::AsNat>(
            p.v_mut())) {
      auto &[d_a0, d_a1] =
          std::get<typename ReuseMixedFields::payload::AsNat>(p.v_mut());
      return payload::aspair(std::move(d_a1), std::move(d_a0));
    } else {
      auto &[d_a0, d_a1] =
          std::get<typename ReuseMixedFields::payload::AsPair>(p.v_mut());
      return payload::asnat(std::move(d_a1), std::move(d_a0));
    }
  } else {
    return p;
  }
}
