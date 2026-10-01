#include "nested_custom_ctor_field_type.h"

std::shared_ptr<ITree<Sum<exc<typename natParams::ptr>, Nat>>>
NestedCustomCtorFieldType::run() {
  return run_exc<natParams, Nat>(itree_ret(Nat::s(Nat::s(Nat::s(Nat::o())))));
}
