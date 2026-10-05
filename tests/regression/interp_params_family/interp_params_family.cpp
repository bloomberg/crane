#include "interp_params_family.h"

Itree<crane::obj, crane::obj>
Case_sum1_Handler(Handler<crane::obj, crane::obj> x,
                  Handler<crane::obj, crane::obj> x0, crane::obj x1) {
  return Handler_Mod::template case_<crane::obj, crane::obj, crane::obj,
                                     crane::obj>(
      std::move(x), std::move(x0),
      crane::any_cast<Sum1<crane::obj, crane::obj, crane::obj>>(x1));
}

std::optional<Nat> InterpParamsFamily::run(
    const Nat &fuel,
    const Itree<Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                     InterpParamsFamily::noE, crane::obj>,
                Nat> &t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    auto &&_sv0 = t.observe();
    if (std::holds_alternative<typename ItreeF<
            Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                 InterpParamsFamily::noE, crane::obj>,
            Nat,
            Itree<Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                       InterpParamsFamily::noE, crane::obj>,
                  Nat>>::RetF>(_sv0.v())) {
      const auto &[r0] = std::get<typename ItreeF<
          Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
               InterpParamsFamily::noE, crane::obj>,
          Nat,
          Itree<Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                     InterpParamsFamily::noE, crane::obj>,
                Nat>>::RetF>(_sv0.v());
      return std::make_optional<Nat>(r0);
    } else if (std::holds_alternative<typename ItreeF<
                   Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                        InterpParamsFamily::noE, crane::obj>,
                   Nat,
                   Itree<Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                              InterpParamsFamily::noE, crane::obj>,
                         Nat>>::TauF>(_sv0.v())) {
      const auto &[t0] = std::get<typename ItreeF<
          Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
               InterpParamsFamily::noE, crane::obj>,
          Nat,
          Itree<Sum1<InterpParamsFamily::putE<InterpParamsFamily::ptr>,
                     InterpParamsFamily::noE, crane::obj>,
                Nat>>::TauF>(_sv0.v());
      return run(*a0, t0);
    } else {
      return std::optional<Nat>();
    }
  }
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }

crane::obj Function::Cat_IFun(IFun<crane::obj, crane::obj> f1,
                              IFun<crane::obj, crane::obj> f2, crane::obj e) {
  return f2(f1(e));
}

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}
