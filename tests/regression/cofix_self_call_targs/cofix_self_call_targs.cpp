#include "cofix_self_call_targs.h"

std::optional<Nat> CofixSelfCallTargs::run(
    const Nat &fuel, CofixSelfCallTargs::tree<CofixSelfCallTargs::noE, Nat> t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = observe<CofixSelfCallTargs::noE, Nat>(t);
      if (std::holds_alternative<typename CofixSelfCallTargs::treeF<
              CofixSelfCallTargs::noE, Nat,
              CofixSelfCallTargs::tree<CofixSelfCallTargs::noE, Nat>>::RetF>(
              _sv0.v())) {
        const auto &[r0] = std::get<typename CofixSelfCallTargs::treeF<
            CofixSelfCallTargs::noE, Nat,
            CofixSelfCallTargs::tree<CofixSelfCallTargs::noE, Nat>>::RetF>(
            _sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<typename CofixSelfCallTargs::treeF<
                     CofixSelfCallTargs::noE, Nat,
                     CofixSelfCallTargs::tree<CofixSelfCallTargs::noE,
                                              Nat>>::TauF>(_sv0.v())) {
        const auto &[t2] = std::get<typename CofixSelfCallTargs::treeF<
            CofixSelfCallTargs::noE, Nat,
            CofixSelfCallTargs::tree<CofixSelfCallTargs::noE, Nat>>::TauF>(
            _sv0.v());
        return run(*a0, t2);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}
