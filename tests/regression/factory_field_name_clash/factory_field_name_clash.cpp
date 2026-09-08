#include "factory_field_name_clash.h"

/// A constructor's factory method is named by lowercasing the constructor.  For
/// A : nat -> a that collides with the type name a, so it is renamed to
/// a0 -- which is exactly the default name given to the constructor's first
/// field.  The struct then declares uint64_t a0 and static a a0(uint64_t).
uint64_t FactoryFieldNameClash::get(const FactoryFieldNameClash::a &x) {
  const auto &[a0] = x;
  return a0;
}
