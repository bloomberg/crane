#include <reuse_mixed_fields.h>

/// Forces d to be owned through the else branch.
/// The match branch has reuse candidates: both AsNat and AsPair
/// have arity 2.
__attribute__((pure)) ReuseMixedFields::payload
ReuseMixedFields::swap_tag_or_id(ReuseMixedFields::payload p,
                                 const bool &do_swap) {
  if (do_swap) {
    if (std::holds_alternative<typename ReuseMixedFields::payload::AsNat>(
            p.v())) {
      const auto &[d_a0, d_a1] =
          std::get<typename ReuseMixedFields::payload::AsNat>(p.v());
      return payload::aspair(d_a1, d_a0);
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename ReuseMixedFields::payload::AsPair>(p.v());
      return payload::asnat(d_a1, d_a0);
    }
  } else {
    return p;
  }
}
