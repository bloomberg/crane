#include "interp_chain_perf.h"

Itree<InterpChainPerf::TopE<crane::obj>, Nat>
InterpChainPerf::prog(const Nat &n) {
  static const auto resum_inl = crane::immortal(
      CategoryOps::template ReSum_inl<crane::obj,
                                      crane::fn<crane::obj(crane::obj)>>(
          [](const auto &, const auto &) { return crane::obj(); },
          [](crane::obj, crane::obj, crane::obj, const auto &x,
             crane::fn<crane::obj(crane::obj)> x0) {
            return [=](crane::obj _x0) -> crane::obj {
              return Function::Cat_IFun(
                  x, crane::any_cast<IFun<crane::obj, crane::obj>>(x0), _x0);
            };
          },
          [](crane::obj, crane::obj) {
            return crane_erase_global<Function::Inl_sum1, crane::obj>();
          },
          crane::obj(), crane::obj(), crane::obj(),
          CategoryOps::template ReSum_id<crane::obj,
                                         crane::fn<crane::obj(crane::obj)>>(
              [](crane::obj) {
                return crane_erase_global<Function::Id_IFun, crane::obj>();
              },
              crane::obj())));
  return ITree::template iter<InterpChainPerf::TopE<crane::obj>, Nat,
                              std::pair<Nat, Nat>>(
      [=](std::pair<Nat, Nat> pat) -> Itree<InterpChainPerf::TopE<crane::obj>,
                                            Sum<std::pair<Nat, Nat>, Nat>> {
        const auto &[i, acc] = pat;
        if (i.eqb(n)) {
          return Itree<InterpChainPerf::TopE<crane::obj>,
                       Sum<std::pair<Nat, Nat>, Nat>>::
              go(ItreeF<InterpChainPerf::TopE<crane::obj>,
                        Sum<std::pair<Nat, Nat>, Nat>,
                        Itree<InterpChainPerf::TopE<crane::obj>,
                              Sum<std::pair<Nat, Nat>, Nat>>>::
                     retf(Sum<std::pair<Nat, Nat>, Nat>::inr(acc)));
        } else {
          return ITree::template bind<InterpChainPerf::TopE<crane::obj>, Nat,
                                      Sum<std::pair<Nat, Nat>, Nat>>(
              ITree::template trigger<InterpChainPerf::TopE<crane::obj>, Nat>(
                  Subevent::template subevent<
                      InterpChainPerf::GetE,
                      Sum1<InterpChainPerf::GetE, InterpChainPerf::outE,
                           crane::obj>,
                      Nat>(resum_inl, GetE::GET)),
              [=](Nat x) {
                return Itree<InterpChainPerf::TopE<crane::obj>,
                             Sum<std::pair<Nat, Nat>, Nat>>::
                    go(ItreeF<InterpChainPerf::TopE<crane::obj>,
                              Sum<std::pair<Nat, Nat>, Nat>,
                              Itree<InterpChainPerf::TopE<crane::obj>,
                                    Sum<std::pair<Nat, Nat>, Nat>>>::
                           retf(Sum<std::pair<Nat, Nat>, Nat>::inl(
                               std::make_pair(Nat::s(i), acc.add(x)))));
              });
        }
      },
      std::make_pair(Nat::o(), Nat::o()));
}

template <typename CraneTcArg>
using crane_carrier_tc_556dca13c30ca6b8 =
    Itree<InterpChainPerf::BotE<crane::obj>, CraneTcArg>;

Itree<InterpChainPerf::BotE<crane::obj>, std::pair<Nat, Nat>>
InterpChainPerf::run_n(const Nat &n) {
  return State::template interp_state<
      MonadIter_itree<InterpChainPerf::BotE<crane::obj>>,
      Monad_itree<InterpChainPerf::BotE<crane::obj>>,
      Functor_itree<InterpChainPerf::BotE<crane::obj>>,
      InterpChainPerf::TopE<crane::obj>, Nat, Nat>(
      [](const auto &a0)
          -> Monads::template stateT<Nat, crane_carrier_tc_556dca13c30ca6b8,
                                     crane::obj> {
        return h<crane::obj>(
            crane_convert<InterpChainPerf::TopE<crane::obj>>(a0));
      },
      Interp::template interp<
          MonadIter_itree<InterpChainPerf::TopE<crane::obj>>,
          Monad_itree<InterpChainPerf::TopE<crane::obj>>,
          Functor_itree<InterpChainPerf::TopE<crane::obj>>>(
          [](const auto &a0)
              -> Itree<InterpChainPerf::TopE<crane::obj>, crane::obj> {
            return intr<crane::obj>(
                crane_convert<InterpChainPerf::TopE<crane::obj>>(a0));
          },
          prog(n)))(Nat::o());
}

std::optional<Nat> InterpChainPerf::drive(
    const Nat &fuel,
    const Itree<Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
                std::pair<Nat, Nat>> &t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    auto &&_sv0 = t.observe();
    if (std::holds_alternative<typename ItreeF<
            Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
            std::pair<Nat, Nat>,
            Itree<Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
                  std::pair<Nat, Nat>>>::RetF>(_sv0.v())) {
      const auto &[r1] = std::get<typename ItreeF<
          Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
          std::pair<Nat, Nat>,
          Itree<Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
                std::pair<Nat, Nat>>>::RetF>(_sv0.v());
      const auto &[_x, r] = r1;
      return std::make_optional<Nat>(r);
    } else if (
        std::holds_alternative<typename ItreeF<
            Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
            std::pair<Nat, Nat>,
            Itree<Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
                  std::pair<Nat, Nat>>>::TauF>(_sv0.v())) {
      const auto &[t0] = std::get<typename ItreeF<
          Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
          std::pair<Nat, Nat>,
          Itree<Sum1<InterpChainPerf::outE, InterpChainPerf::noE, crane::obj>,
                std::pair<Nat, Nat>>>::TauF>(_sv0.v());
      return drive(*a0, t0);
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

crane::obj Function::Case_sum1(IFun<crane::obj, crane::obj> x,
                               IFun<crane::obj, crane::obj> x0, crane::obj x1) {
  return Function::case_sum1(
      std::move(x), std::move(x0),
      crane::any_cast<Sum1<crane::obj, crane::obj, crane::obj>>(x1));
}

crane::obj Function::Inl_sum1(crane::obj x) {
  return Sum1<crane::obj, crane::obj, crane::obj>::inl1(x);
}
