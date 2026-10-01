#include "skipped_dict_family_unconstrained.h"

std::shared_ptr<ITree<Nat>> SkippedDictFamilyUnconstrained::run() {
  return raiseUB<UBE, Nat>();
}
