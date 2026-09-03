#include <type_alias_applied_ctor_param.h>
#include <cassert>

int main() {
  assert(TypeAliasAppliedCtorParam::get(TypeAliasAppliedCtorParam::mk).has_value());
  return 0;
}
