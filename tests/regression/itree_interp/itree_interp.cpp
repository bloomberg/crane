#include "itree_interp.h"

std::optional<Nat> ItreeInterp::run(const Nat &fuel,
                                    Itree<ItreeInterp::noE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = t.observe();
      if (std::holds_alternative<typename ItreeF<
              ItreeInterp::noE, Nat, Itree<ItreeInterp::noE, Nat>>::RetF>(
              _sv0.v())) {
        const auto &[r0] =
            std::get<typename ItreeF<ItreeInterp::noE, Nat,
                                     Itree<ItreeInterp::noE, Nat>>::RetF>(
                _sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<
                     typename ItreeF<ItreeInterp::noE, Nat,
                                     Itree<ItreeInterp::noE, Nat>>::TauF>(
                     _sv0.v())) {
        const auto &[t0] =
            std::get<typename ItreeF<ItreeInterp::noE, Nat,
                                     Itree<ItreeInterp::noE, Nat>>::TauF>(
                _sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }
