#include "run_bot_handle_existential.h"

std::optional<Nat> RunBotHandleExistential::run(
    const Nat &fuel,
    Itree<crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = t.observe();
      if (std::holds_alternative<typename ItreeF<
              crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>,
              Itree<crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>>>::
                                     RetF>(_sv0.v())) {
        const auto &[r0] = std::get<typename ItreeF<
            crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>,
            Itree<crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>>>::
                                        RetF>(_sv0.v());
        if (std::holds_alternative<
                typename Sum<RunBotHandleExistential::Run_error, Nat>::Inl>(
                r0.v())) {
          return std::optional<Nat>();
        } else {
          const auto &[a01] = std::get<
              typename Sum<RunBotHandleExistential::Run_error, Nat>::Inr>(
              r0.v());
          return std::make_optional<Nat>(a01);
        }
      } else if (std::holds_alternative<typename ItreeF<
                     crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>,
                     Itree<crane::obj, Sum<RunBotHandleExistential::Run_error,
                                           Nat>>>::TauF>(_sv0.v())) {
        const auto &[t0] = std::get<typename ItreeF<
            crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>,
            Itree<crane::obj, Sum<RunBotHandleExistential::Run_error, Nat>>>::
                                        TauF>(_sv0.v());
        return run(*a0, t0);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}
