#include "mrec_handler_branch_types.h"

std::optional<Sum<Nat, Nat>> MrecHandlerBranchTypes::run(
    const Nat &fuel,
    const Itree<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                     MrecHandlerBranchTypes::FailE, crane::obj>,
                Sum<Nat, Nat>> &t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Sum<Nat, Nat>>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    auto &&_sv0 = t.observe();
    if (std::holds_alternative<typename ItreeF<
            Sum1<MrecHandlerBranchTypes::extE<Nat>,
                 MrecHandlerBranchTypes::FailE, crane::obj>,
            Sum<Nat, Nat>,
            Itree<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                       MrecHandlerBranchTypes::FailE, crane::obj>,
                  Sum<Nat, Nat>>>::RetF>(_sv0.v())) {
      const auto &[r0] = std::get<
          typename ItreeF<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                               MrecHandlerBranchTypes::FailE, crane::obj>,
                          Sum<Nat, Nat>,
                          Itree<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                                     MrecHandlerBranchTypes::FailE, crane::obj>,
                                Sum<Nat, Nat>>>::RetF>(_sv0.v());
      return std::make_optional<Sum<Nat, Nat>>(r0);
    } else if (std::holds_alternative<typename ItreeF<
                   Sum1<MrecHandlerBranchTypes::extE<Nat>,
                        MrecHandlerBranchTypes::FailE, crane::obj>,
                   Sum<Nat, Nat>,
                   Itree<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                              MrecHandlerBranchTypes::FailE, crane::obj>,
                         Sum<Nat, Nat>>>::TauF>(_sv0.v())) {
      const auto &[t0] = std::get<
          typename ItreeF<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                               MrecHandlerBranchTypes::FailE, crane::obj>,
                          Sum<Nat, Nat>,
                          Itree<Sum1<MrecHandlerBranchTypes::extE<Nat>,
                                     MrecHandlerBranchTypes::FailE, crane::obj>,
                                Sum<Nat, Nat>>>::TauF>(_sv0.v());
      return run(*a0, t0);
    } else {
      return std::optional<Sum<Nat, Nat>>();
    }
  }
}
