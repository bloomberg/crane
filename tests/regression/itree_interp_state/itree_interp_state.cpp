#include "itree_interp_state.h"

std::optional<std::pair<Nat, Nat>>
ItreeInterpState::run(const Nat &fuel,
                      Itree<ItreeInterpState::noE, std::pair<Nat, Nat>> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<std::pair<Nat, Nat>>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = t.observe();
      if (std::holds_alternative<typename ItreeF<
              ItreeInterpState::noE, std::pair<Nat, Nat>,
              Itree<ItreeInterpState::noE, std::pair<Nat, Nat>>>::RetF>(
              _sv0.v())) {
        const auto &[r0] = std::get<typename ItreeF<
            ItreeInterpState::noE, std::pair<Nat, Nat>,
            Itree<ItreeInterpState::noE, std::pair<Nat, Nat>>>::RetF>(_sv0.v());
        return std::make_optional<std::pair<Nat, Nat>>(r0);
      } else if (std::holds_alternative<typename ItreeF<
                     ItreeInterpState::noE, std::pair<Nat, Nat>,
                     Itree<ItreeInterpState::noE, std::pair<Nat, Nat>>>::TauF>(
                     _sv0.v())) {
        const auto &[t0] = std::get<typename ItreeF<
            ItreeInterpState::noE, std::pair<Nat, Nat>,
            Itree<ItreeInterpState::noE, std::pair<Nat, Nat>>>::TauF>(_sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }
