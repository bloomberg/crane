#include "erased_index_fun_type.h"

/// A type-indexed inductive whose index can be a function type.  dflt is
/// declared as returning std::any, and the call site then applies the result
/// directly: "type 'std::any' does not provide a call operator".
Nat ErasedIndexFunType::ex(const Nat &x0_) {
  static const auto dflt_1 =
      crane::immortal(dflt<crane::fn<Nat(Nat)>>(ty::tf(ty::tn(), ty::tn())));
  return crane::any_cast<Nat>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(dflt_1)(
          crane::obj(x0_)));
}
