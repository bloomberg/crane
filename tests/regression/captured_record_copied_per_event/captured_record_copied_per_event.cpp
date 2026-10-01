#include "captured_record_copied_per_event.h"

CapturedRecordCopiedPerEvent::leaf
CapturedRecordCopiedPerEvent::lf(const Nat &n) {
  return leaf{List<Nat>::cons(n, List<Nat>::nil()),
              List<Nat>::cons(n, List<Nat>::nil()),
              List<Nat>::cons(n, List<Nat>::nil()),
              List<Nat>::cons(n, List<Nat>::nil())};
}

CapturedRecordCopiedPerEvent::mid
CapturedRecordCopiedPerEvent::md(const Nat &n) {
  return mid{lf(n), lf(n), lf(n), lf(n)};
}

CapturedRecordCopiedPerEvent::blk
CapturedRecordCopiedPerEvent::mk(const Nat &n) {
  return blk{md(n), md(n), md(n), md(n), n};
}

Itree<CapturedRecordCopiedPerEvent::TickE, std::monostate>
CapturedRecordCopiedPerEvent::ticks(const Nat &k) {
  if (std::holds_alternative<typename Nat::O>(k.v())) {
    return Itree<CapturedRecordCopiedPerEvent::TickE, std::monostate>::go(
        ItreeF<CapturedRecordCopiedPerEvent::TickE, std::monostate,
               Itree<CapturedRecordCopiedPerEvent::TickE,
                     std::monostate>>::retf(std::monostate{}));
  } else {
    const auto &[a0] = std::get<typename Nat::S>(k.v());
    const Nat &a0_value = *a0;
    return ITree::template bind<CapturedRecordCopiedPerEvent::TickE,
                                std::monostate, std::monostate>(
        ITree::template trigger<CapturedRecordCopiedPerEvent::TickE,
                                std::monostate>(
            Subevent::template subevent<CapturedRecordCopiedPerEvent::TickE,
                                        CapturedRecordCopiedPerEvent::TickE,
                                        std::monostate>(
                CategoryOps::template ReSum_id<
                    crane::obj, crane::fn<crane::obj(crane::obj)>>(
                    [](crane::obj) {
                      return crane_erase_fn<crane::obj>(Function::Id_IFun);
                    },
                    crane::obj()),
                TickE::TICK)),
        [=](std::monostate) { return ticks(a0_value); });
  }
}

Itree<CapturedRecordCopiedPerEvent::TickE, Nat>
CapturedRecordCopiedPerEvent::step(const CapturedRecordCopiedPerEvent::blk &b,
                                   const Nat &k) {
  return ITree::template bind<CapturedRecordCopiedPerEvent::TickE,
                              std::monostate, Nat>(
      ticks(k), [=](std::monostate) {
        return Itree<CapturedRecordCopiedPerEvent::TickE, Nat>::lazy_(
            [=]() -> Itree<CapturedRecordCopiedPerEvent::TickE, Nat> {
              return Itree<CapturedRecordCopiedPerEvent::TickE, Nat>::go(
                  ItreeF<CapturedRecordCopiedPerEvent::TickE, Nat,
                         Itree<CapturedRecordCopiedPerEvent::TickE,
                               Nat>>::retf(b.tag));
            });
      });
}

Itree<CapturedRecordCopiedPerEvent::TickE, Nat>
CapturedRecordCopiedPerEvent::steps(const Nat &n, const Nat &k,
                                    const CapturedRecordCopiedPerEvent::blk &b,
                                    const Nat &acc) {
  if (std::holds_alternative<typename Nat::O>(n.v())) {
    return Itree<CapturedRecordCopiedPerEvent::TickE, Nat>::go(
        ItreeF<CapturedRecordCopiedPerEvent::TickE, Nat,
               Itree<CapturedRecordCopiedPerEvent::TickE, Nat>>::retf(acc));
  } else {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    const Nat &a0_value = *a0;
    return ITree::template bind<CapturedRecordCopiedPerEvent::TickE, Nat, Nat>(
        step(b, k),
        [=](const Nat &x) { return steps(a0_value, k, b, acc.add(x)); });
  }
}

std::optional<Nat> CapturedRecordCopiedPerEvent::run(
    const Nat &fuel, Itree<CapturedRecordCopiedPerEvent::TickE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    auto &&_sv0 = t.observe();
    if (std::holds_alternative<typename ItreeF<
            CapturedRecordCopiedPerEvent::TickE, Nat,
            Itree<CapturedRecordCopiedPerEvent::TickE, Nat>>::RetF>(_sv0.v())) {
      const auto &[r0] = std::get<typename ItreeF<
          CapturedRecordCopiedPerEvent::TickE, Nat,
          Itree<CapturedRecordCopiedPerEvent::TickE, Nat>>::RetF>(_sv0.v());
      return std::make_optional<Nat>(r0);
    } else if (std::holds_alternative<typename ItreeF<
                   CapturedRecordCopiedPerEvent::TickE, Nat,
                   Itree<CapturedRecordCopiedPerEvent::TickE, Nat>>::TauF>(
                   _sv0.v())) {
      const auto &[t0] = std::get<typename ItreeF<
          CapturedRecordCopiedPerEvent::TickE, Nat,
          Itree<CapturedRecordCopiedPerEvent::TickE, Nat>>::TauF>(_sv0.v());
      return run(*a0, t0);
    } else {
      const auto &[x0, e0] = std::get<typename ItreeF<
          CapturedRecordCopiedPerEvent::TickE, Nat,
          Itree<CapturedRecordCopiedPerEvent::TickE, Nat>>::VisF>(_sv0.v());
      return run(*a0, e0(std::monostate{}));
    }
  }
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }
