#include "coind_family_param.h"

CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat>
CoindFamilyParam::count(const Nat &n, const Nat &acc) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return tree<CoindFamilyParam::voidE, Nat>::go(
        treeF<CoindFamilyParam::voidE, Nat,
              CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat>>::retf(acc));
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    const Nat &a0_value = *a0;
    return tree<CoindFamilyParam::voidE, Nat>::lazy_(
        [=]() -> CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat> {
          return tree<CoindFamilyParam::voidE, Nat>::go(
              treeF<CoindFamilyParam::voidE, Nat,
                    CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat>>::
                  tauf(count(a0_value, Nat::s(acc))));
        });
  }
}

std::optional<Nat>
CoindFamilyParam::run(const Nat &fuel,
                      CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = observe<CoindFamilyParam::voidE, Nat>(t);
      if (std::holds_alternative<typename CoindFamilyParam::treeF<
              CoindFamilyParam::voidE, Nat,
              CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat>>::RetF>(
              _sv0.v())) {
        const auto &[r0] = std::get<typename CoindFamilyParam::treeF<
            CoindFamilyParam::voidE, Nat,
            CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat>>::RetF>(
            _sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<typename CoindFamilyParam::treeF<
                     CoindFamilyParam::voidE, Nat,
                     CoindFamilyParam::tree<CoindFamilyParam::voidE,
                                            Nat>>::TauF>(_sv0.v())) {
        const auto &[t0] = std::get<typename CoindFamilyParam::treeF<
            CoindFamilyParam::voidE, Nat,
            CoindFamilyParam::tree<CoindFamilyParam::voidE, Nat>>::TauF>(
            _sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}
