#include "ctor_family_index_any.h"

std::optional<Nat> CtorFamilyIndexAny::run(
    const Nat &fuel, CtorFamilyIndexAny::tree<CtorFamilyIndexAny::noE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = observe<CtorFamilyIndexAny::noE, Nat>(t);
      if (std::holds_alternative<typename CtorFamilyIndexAny::treeF<
              CtorFamilyIndexAny::noE, Nat,
              CtorFamilyIndexAny::tree<CtorFamilyIndexAny::noE, Nat>>::RetF>(
              _sv0.v())) {
        const auto &[r0] = std::get<typename CtorFamilyIndexAny::treeF<
            CtorFamilyIndexAny::noE, Nat,
            CtorFamilyIndexAny::tree<CtorFamilyIndexAny::noE, Nat>>::RetF>(
            _sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<typename CtorFamilyIndexAny::treeF<
                     CtorFamilyIndexAny::noE, Nat,
                     CtorFamilyIndexAny::tree<CtorFamilyIndexAny::noE,
                                              Nat>>::TauF>(_sv0.v())) {
        const auto &[t2] = std::get<typename CtorFamilyIndexAny::treeF<
            CtorFamilyIndexAny::noE, Nat,
            CtorFamilyIndexAny::tree<CtorFamilyIndexAny::noE, Nat>>::TauF>(
            _sv0.v());
        return run(*a0, t2);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}
