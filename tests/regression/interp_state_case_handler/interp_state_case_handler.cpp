#include "interp_state_case_handler.h"

std::optional<std::pair<Nat, Nat>> InterpStateCaseHandler::run(
    const Nat &fuel,
    const Itree<InterpStateCaseHandler::noE, std::pair<Nat, Nat>> &t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<std::pair<Nat, Nat>>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = t.observe();
      if (std::holds_alternative<typename ItreeF<
              InterpStateCaseHandler::noE, std::pair<Nat, Nat>,
              Itree<InterpStateCaseHandler::noE, std::pair<Nat, Nat>>>::RetF>(
              _sv0.v())) {
        const auto &[r0] = std::get<typename ItreeF<
            InterpStateCaseHandler::noE, std::pair<Nat, Nat>,
            Itree<InterpStateCaseHandler::noE, std::pair<Nat, Nat>>>::RetF>(
            _sv0.v());
        return std::make_optional<std::pair<Nat, Nat>>(r0);
      } else if (std::holds_alternative<typename ItreeF<
                     InterpStateCaseHandler::noE, std::pair<Nat, Nat>,
                     Itree<InterpStateCaseHandler::noE,
                           std::pair<Nat, Nat>>>::TauF>(_sv0.v())) {
        const auto &[t0] = std::get<typename ItreeF<
            InterpStateCaseHandler::noE, std::pair<Nat, Nat>,
            Itree<InterpStateCaseHandler::noE, std::pair<Nat, Nat>>>::TauF>(
            _sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }

crane::obj Function::Cat_IFun(IFun<crane::obj, crane::obj> f1,
                              IFun<crane::obj, crane::obj> f2, crane::obj e) {
  return f2(f1(e));
}

crane::obj Function::Case_sum1(IFun<crane::obj, crane::obj> x,
                               IFun<crane::obj, crane::obj> x0, crane::obj x1) {
  return Function::case_sum1(
      std::move(x), std::move(x0),
      crane::any_cast<Sum1<crane::obj, crane::obj, crane::obj>>(x1));
}

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}

crane::obj Function::Inr_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inr1(x);
}
