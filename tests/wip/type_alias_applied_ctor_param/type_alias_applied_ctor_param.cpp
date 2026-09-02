#include "type_alias_applied_ctor_param.h"

std::optional<Nat> TypeAliasAppliedCtorParam::get(
    const TypeAliasAppliedCtorParam::holder<std::optional<std::any>> &h) {
  const auto &[a0] = h;
  return a0;
}
