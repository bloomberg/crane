#include "instance_used_before_defined.h"

EOU<Nat> InstanceUsedBeforeDefined::use(const Nat &n) {
  return Ops::Arith_nat.madd(n, n);
}
