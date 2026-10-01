#include "event_family_only_in_return_type.h"

std::shared_ptr<ITree<Nat>> EventFamilyOnlyInReturnType::run() {
  return raiseUB<UBE, Nat>();
}

std::shared_ptr<ITree<Nat>> EventFamilyOnlyInReturnType::run_sum() {
  return raiseUB<void, Nat>();
}
