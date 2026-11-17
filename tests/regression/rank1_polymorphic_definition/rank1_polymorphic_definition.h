#ifndef INCLUDED_RANK1_POLYMORPHIC_DEFINITION
#define INCLUDED_RANK1_POLYMORPHIC_DEFINITION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <cstdint>

struct Rank1PolymorphicDefinition {
  /// A top-level definition whose type is forall A, ... erases its whole
  /// signature to std::any, but the call sites pass concrete types unboxed.
  using church =
      crane::fn<crane::obj(crane::fn<crane::obj(crane::obj)>, crane::obj)>;
  static crane::obj three(const crane::fn<crane::obj(crane::obj)> &f,
                          crane::obj x);
  static uint64_t to_nat(church c);
  static bool to_bool(church c);
  static inline const uint64_t total =
      (to_nat(crane_erase_global<three, crane::obj>()) +
       (to_bool(crane_erase_global<three, crane::obj>()) ? UINT64_C(10)
                                                         : UINT64_C(20)));
};

#endif // INCLUDED_RANK1_POLYMORPHIC_DEFINITION
