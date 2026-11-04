#include "fast_variant_assign_from_own_child.h"

uint64_t FastVariantAssignFromOwnChild::total(
    const FastVariantAssignFromOwnChild::chain &c) {
  if (crane::holds_alternative<
          typename FastVariantAssignFromOwnChild::chain::Last>(c.v())) {
    const auto &[a0] =
        crane::get<typename FastVariantAssignFromOwnChild::chain::Last>(c.v());
    return a0;
  } else {
    const auto &[a0, a1] =
        crane::get<typename FastVariantAssignFromOwnChild::chain::Link>(c.v());
    return (a0 + total(*a1));
  }
}
