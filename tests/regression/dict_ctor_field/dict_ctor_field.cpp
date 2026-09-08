#include "dict_ctor_field.h"

/// A type class becomes a C++ concept, so a constructor field whose Rocq type
/// is a class applied to a concrete type has no C++ type to be given.  Crane
/// writes the concept's name where a type belongs, producing
/// Sz a0; as a data member and passing the instance SzNat as a value.
uint64_t DictCtorField::run(const DictCtorField::box &b) {
  const auto &[a0, a1] = b;
  return a0.sz(a1);
}
