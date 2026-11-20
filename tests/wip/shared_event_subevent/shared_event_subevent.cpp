#include "shared_event_subevent.h"

Itree<crane::obj, crane::obj>
Case_sum1_Handler(const Handler<crane::obj, crane::obj> &x,
                  const Handler<crane::obj, crane::obj> &x0, crane::obj x1) {
  return Handler_Mod::template case_<crane::obj, crane::obj, crane::obj,
                                     crane::obj>(
      x, x0, crane::any_cast<Sum1<crane::obj, crane::obj, crane::obj>>(x1));
}

/// run with at most n silent steps taken.
std::optional<Nat> SharedEventSubevent::burn(const Nat &n,
                                             const Itree<crane::obj, Nat> &t) {
  if (crane::holds_alternative<typename Nat::O>(n.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = crane::get<typename Nat::S>(n.v());
    auto &&_sv0 = t.observe();
    if (crane::holds_alternative<
            typename ItreeF<crane::obj, Nat, Itree<crane::obj, Nat>>::RetF>(
            _sv0.v())) {
      const auto &[r0] = crane::get<
          typename ItreeF<crane::obj, Nat, Itree<crane::obj, Nat>>::RetF>(
          _sv0.v());
      return std::make_optional<Nat>(r0);
    } else if (
        crane::holds_alternative<
            typename ItreeF<crane::obj, Nat, Itree<crane::obj, Nat>>::TauF>(
            _sv0.v())) {
      const auto &[t0] = crane::get<
          typename ItreeF<crane::obj, Nat, Itree<crane::obj, Nat>>::TauF>(
          _sv0.v());
      return burn(*a0, t0);
    } else {
      throw std::logic_error("absurd case");
    }
  }
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }

crane::obj Function::Cat_IFun(const IFun<crane::obj, crane::obj> &f1,
                              const IFun<crane::obj, crane::obj> &f2,
                              crane::obj e) {
  return f2(f1(e));
}

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}

crane::obj Function::Inr_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inr1(x);
}
