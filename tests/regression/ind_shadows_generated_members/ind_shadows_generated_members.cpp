#include "ind_shadows_generated_members.h"

/// Every generated inductive carries a variant_t alias and v / v_mut
/// accessors.  An inductive that is itself named variant_t, with
/// constructors named v_mut and v_, redeclares them, and the pattern match
/// then calls std::get_if against the constructor rather than the alias.
uint64_t IndShadowsGeneratedMembers::depth(
    const IndShadowsGeneratedMembers::variant_t &x) {
  if (std::holds_alternative<
          typename IndShadowsGeneratedMembers::variant_t::V_mut>(x.v())) {
    const auto &[a0] =
        std::get<typename IndShadowsGeneratedMembers::variant_t::V_mut>(x.v());
    return a0;
  } else {
    const auto &[a0] =
        std::get<typename IndShadowsGeneratedMembers::variant_t::V_>(x.v());
    return (depth(*a0) + 1);
  }
}
