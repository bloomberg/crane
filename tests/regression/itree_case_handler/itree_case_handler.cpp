#include "itree_case_handler.h"

Itree<crane::obj, crane::obj>
Case_sum1_Handler(Handler<crane::obj, crane::obj> x,
                  Handler<crane::obj, crane::obj> x0, crane::obj x1) {
  return Handler_Mod::template case_<crane::obj, crane::obj, crane::obj,
                                     crane::obj>(
      std::move(x), std::move(x0),
      crane::any_cast<Sum1<crane::obj, crane::obj, crane::obj>>(x1));
}

std::optional<Nat> ItreeCaseHandler::run(const Nat &fuel,
                                         Itree<ItreeCaseHandler::noE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = t.observe();
      if (std::holds_alternative<
              typename ItreeF<ItreeCaseHandler::noE, Nat,
                              Itree<ItreeCaseHandler::noE, Nat>>::RetF>(
              _sv0.v())) {
        const auto &[r0] =
            std::get<typename ItreeF<ItreeCaseHandler::noE, Nat,
                                     Itree<ItreeCaseHandler::noE, Nat>>::RetF>(
                _sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<
                     typename ItreeF<ItreeCaseHandler::noE, Nat,
                                     Itree<ItreeCaseHandler::noE, Nat>>::TauF>(
                     _sv0.v())) {
        const auto &[t0] =
            std::get<typename ItreeF<ItreeCaseHandler::noE, Nat,
                                     Itree<ItreeCaseHandler::noE, Nat>>::TauF>(
                _sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}
