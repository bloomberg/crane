#include "instance_as_value.h"

InstanceAsValue::Monoid<uint64_t> InstanceAsValue::mkDict(uint64_t base) {
  return Monoid<uint64_t>{
      base, [](uint64_t _x0, uint64_t _x1) -> uint64_t { return (_x0 + _x1); }};
}

uint64_t InstanceAsValue::method(uint64_t _x0, uint64_t _x1) {
  return MNat.op(_x0, _x1);
}
