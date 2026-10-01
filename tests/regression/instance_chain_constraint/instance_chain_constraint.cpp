#include "instance_chain_constraint.h"

bool InstanceChainConstraint::no_overlap(const Nat &a1, const Nat &sz1,
                                         const Nat &a2, const Nat &sz2) {
  return !(overlaps_ptoi<InstanceChainConstraint::provNat,
                         InstanceChainConstraint::ptrNat,
                         InstanceChainConstraint::piNat>::overlaps(a1, sz1, a2,
                                                                   sz2));
}
