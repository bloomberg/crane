#ifndef INCLUDED_TYPE_LEVEL_FIXPOINT_CALL
#define INCLUDED_TYPE_LEVEL_FIXPOINT_CALL

#include <any>

/// WIP: A `Fixpoint` returning `Type` erases to `std::any`; a value of type `ty
/// 1` is then applied as a function, and `std::any` provides no call operator.
struct TypeLevelFixpointCall {
  using ty = std::any;
  static inline const ty v1 = [](uint64_t n) { return (n + UINT64_C(1)); };
  static inline const uint64_t go = std::any_cast<uint64_t>(v1()(UINT64_C(4)));
};

#endif // INCLUDED_TYPE_LEVEL_FIXPOINT_CALL
