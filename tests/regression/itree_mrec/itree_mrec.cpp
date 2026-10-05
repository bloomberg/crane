#include "itree_mrec.h"

Itree<ItreeMrec::noE, Nat> ItreeMrec::sum_to(const Nat &n) {
  return Recursion::template mrec<ItreeMrec::callE, ItreeMrec::noE, Nat>(
      [](const ItreeMrec::callE &a0)
          -> Itree<Sum1<ItreeMrec::callE, ItreeMrec::noE, crane::obj>,
                   crane::obj> {
        return body<crane::obj>(crane_convert<ItreeMrec::callE>(a0));
      },
      callE::call(n));
}

std::optional<Nat> ItreeMrec::run(const Nat &fuel,
                                  const Itree<ItreeMrec::noE, Nat> &t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = t.observe();
      if (std::holds_alternative<typename ItreeF<
              ItreeMrec::noE, Nat, Itree<ItreeMrec::noE, Nat>>::RetF>(
              _sv0.v())) {
        const auto &[r0] = std::get<typename ItreeF<
            ItreeMrec::noE, Nat, Itree<ItreeMrec::noE, Nat>>::RetF>(_sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<typename ItreeF<
                     ItreeMrec::noE, Nat, Itree<ItreeMrec::noE, Nat>>::TauF>(
                     _sv0.v())) {
        const auto &[t0] = std::get<typename ItreeF<
            ItreeMrec::noE, Nat, Itree<ItreeMrec::noE, Nat>>::TauF>(_sv0.v());
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

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}
