#include "interp_state_after_interp.h"

std::optional<Nat> InterpStateAfterInterp::first_out(
    const Nat &fuel, Itree<Sum1<InterpStateAfterInterp::outE,
                                InterpStateAfterInterp::noE, crane::obj>,
                           std::pair<Nat, Nat>>
                         t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    auto &&_sv0 = t.observe();
    if (std::holds_alternative<
            typename ItreeF<Sum1<InterpStateAfterInterp::outE,
                                 InterpStateAfterInterp::noE, crane::obj>,
                            std::pair<Nat, Nat>,
                            Itree<Sum1<InterpStateAfterInterp::outE,
                                       InterpStateAfterInterp::noE, crane::obj>,
                                  std::pair<Nat, Nat>>>::RetF>(_sv0.v())) {
      return std::optional<Nat>();
    } else if (std::holds_alternative<typename ItreeF<
                   Sum1<InterpStateAfterInterp::outE,
                        InterpStateAfterInterp::noE, crane::obj>,
                   std::pair<Nat, Nat>,
                   Itree<Sum1<InterpStateAfterInterp::outE,
                              InterpStateAfterInterp::noE, crane::obj>,
                         std::pair<Nat, Nat>>>::TauF>(_sv0.v())) {
      const auto &[t0] = std::get<
          typename ItreeF<Sum1<InterpStateAfterInterp::outE,
                               InterpStateAfterInterp::noE, crane::obj>,
                          std::pair<Nat, Nat>,
                          Itree<Sum1<InterpStateAfterInterp::outE,
                                     InterpStateAfterInterp::noE, crane::obj>,
                                std::pair<Nat, Nat>>>::TauF>(_sv0.v());
      return first_out(*a0, t0);
    } else {
      const auto &[x0, e0] = std::get<
          typename ItreeF<Sum1<InterpStateAfterInterp::outE,
                               InterpStateAfterInterp::noE, crane::obj>,
                          std::pair<Nat, Nat>,
                          Itree<Sum1<InterpStateAfterInterp::outE,
                                     InterpStateAfterInterp::noE, crane::obj>,
                                std::pair<Nat, Nat>>>::VisF>(_sv0.v());
      return [&]() {
        if (std::holds_alternative<
                typename Sum1<InterpStateAfterInterp::outE,
                              InterpStateAfterInterp::noE, crane::obj>::Inl1>(
                x0.v())) {
          const auto &[a01] = std::get<
              typename Sum1<InterpStateAfterInterp::outE,
                            InterpStateAfterInterp::noE, crane::obj>::Inl1>(
              x0.v());
          const auto &[a02] = a01;
          return std::make_optional<Nat>(a02);
        } else {
          throw std::logic_error("absurd case");
        }
      }();
    }
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
