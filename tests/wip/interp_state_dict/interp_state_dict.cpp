#include "interp_state_dict.h"

template <typename CraneTcArg>
using crane_carrier_tc_6f2a644abca70cfd = Itree<crane::obj, CraneTcArg>;

/// A counter interpreted through coq-itree's interp_state.  Known issue:
/// the call writes State::interp_state<Monad_itree, Functor_itree, ...>,
/// and clang rejects Monad_itree as the argument for the Monad-concept
/// parameter ("invalid explicitly-specified argument for template parameter
/// '_tcI0'").
Itree<InterpStateDict::Cnt, std::monostate> InterpStateDict::ticks(uint64_t n) {
  static const auto resum_id = crane::immortal(
      CategoryOps::template ReSum_id<crane::obj,
                                     crane::fn<crane::obj(crane::obj)>>(
          [](crane::obj) {
            return crane_erase_global<Function::Id_IFun, crane::obj>();
          },
          crane::obj()));
  if (n <= 0) {
    return Itree<InterpStateDict::Cnt, std::monostate>::go(
        ItreeF<InterpStateDict::Cnt, std::monostate,
               Itree<InterpStateDict::Cnt,
                     std::monostate>>::retf(std::monostate{}));
  } else {
    uint64_t m = n - 1;
    return ITree::template bind<InterpStateDict::Cnt, std::monostate,
                                std::monostate>(
        ITree::template trigger<InterpStateDict::Cnt, std::monostate>(
            Subevent::template subevent<InterpStateDict::Cnt,
                                        InterpStateDict::Cnt, std::monostate>(
                resum_id, Cnt::TICK)),
        [=](std::monostate) { return ticks(m); });
  }
}

Itree<InterpStateDict::Cnt, uint64_t> InterpStateDict::prog(uint64_t n) {
  static const auto resum_id = crane::immortal(
      CategoryOps::template ReSum_id<crane::obj,
                                     crane::fn<crane::obj(crane::obj)>>(
          [](crane::obj) {
            return crane_erase_global<Function::Id_IFun, crane::obj>();
          },
          crane::obj()));
  return ITree::template bind<InterpStateDict::Cnt, std::monostate, uint64_t>(
      ticks(n), [=](std::monostate) {
        return ITree::template trigger<InterpStateDict::Cnt, uint64_t>(
            Subevent::template subevent<InterpStateDict::Cnt,
                                        InterpStateDict::Cnt, uint64_t>(
                resum_id, Cnt::GET));
      });
}

Itree<crane::obj, std::pair<uint64_t, uint64_t>>
InterpStateDict::run(uint64_t n) {
  return State::template interp_state<MonadIter_itree, Monad_itree,
                                      Functor_itree, InterpStateDict::Cnt,
                                      uint64_t, uint64_t>(
      [](const InterpStateDict::Cnt &a0)
          -> Monads::template stateT<
              uint64_t, crane_carrier_tc_6f2a644abca70cfd, crane::obj> {
        return handle<crane::obj>(crane_convert<InterpStateDict::Cnt>(a0));
      },
      prog(n))(UINT64_C(0));
}

crane::obj Function::Id_IFun(crane::obj e) { return e; }
