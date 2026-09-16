#include "instance_in_record_literal.h"

EOU<Nat> InstanceInRecordLiteral::use(const Nat &n) {
  return Ops_nat::madd(n, n);
}
