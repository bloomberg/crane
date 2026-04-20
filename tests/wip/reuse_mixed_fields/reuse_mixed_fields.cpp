#include <reuse_mixed_fields.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Forces d to be owned through the else branch.
/// The match branch has reuse candidates: both AsNat and AsPair
/// have arity 2.
std::shared_ptr<ReuseMixedFields::payload>
ReuseMixedFields::swap_tag_or_id(std::shared_ptr<ReuseMixedFields::payload> p,
                                 const bool do_swap) {
  if (do_swap) {
    if (std::holds_alternative<typename ReuseMixedFields::payload::AsNat>(
            p->v())) {
      if (p.use_count() == 1) {
        auto &_rf =
            std::get<typename ReuseMixedFields::payload::AsNat>(p->v_mut());
        unsigned int a = std::move(_rf.d_a0);
        unsigned int b = std::move(_rf.d_a1);
        _rf.d_a0 = b;
        _rf.d_a1 = std::move(a);
        return p;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename ReuseMixedFields::payload::AsNat>(p->v());
        return payload::aspair(d_a1, d_a0);
      }

    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename ReuseMixedFields::payload::AsPair>(p->v());
      return payload::asnat(d_a1, d_a0);
    }
  } else {
    return p;
  }
}
