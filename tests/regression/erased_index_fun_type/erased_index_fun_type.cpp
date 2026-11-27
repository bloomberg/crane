#include "erased_index_fun_type.h"

/// A type-indexed inductive whose index can be a function type.  dflt is
/// declared as returning std::any, and the call site then applies the result
/// directly: "type 'std::any' does not provide a call operator".
crane::obj ErasedIndexFunType::dflt(const ErasedIndexFunType::ty &t) {
  if (std::holds_alternative<typename ErasedIndexFunType::ty::TN>(t.v())) {
    return Nat::o();
  } else {
    const auto &[_, b0] = std::get<typename ErasedIndexFunType::ty::TF>(t.v());
    return crane_erase_fn([=, b0 = b0](const auto &) { return dflt(*b0); });
  }
}

Nat ErasedIndexFunType::ex(const Nat &x0_) {
  // Built on the first call and immortal: every thread reads it without
  // touching its counts.
  static const auto dflt_1 = crane::immortal(dflt(ty::tf(ty::tn(), ty::tn())));
  return crane::any_cast<Nat>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(dflt_1)(
          crane::obj(x0_)));
}
