#include "match_observe_alias_family.h"

std::optional<Nat> MatchObserveAliasFamily::run(
    const Nat &fuel, Itree<Sum1<MatchObserveAliasFamily::aE<Nat>,
                                MatchObserveAliasFamily::BE, crane::obj>,
                           Nat>
                         t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    auto &&_sv0 = t.observe();
    if (std::holds_alternative<
            typename ItreeF<Sum1<MatchObserveAliasFamily::aE<Nat>,
                                 MatchObserveAliasFamily::BE, crane::obj>,
                            Nat,
                            Itree<Sum1<MatchObserveAliasFamily::aE<Nat>,
                                       MatchObserveAliasFamily::BE, crane::obj>,
                                  Nat>>::RetF>(_sv0.v())) {
      const auto &[r0] = std::get<
          typename ItreeF<Sum1<MatchObserveAliasFamily::aE<Nat>,
                               MatchObserveAliasFamily::BE, crane::obj>,
                          Nat,
                          Itree<Sum1<MatchObserveAliasFamily::aE<Nat>,
                                     MatchObserveAliasFamily::BE, crane::obj>,
                                Nat>>::RetF>(_sv0.v());
      return std::make_optional<Nat>(r0);
    } else if (std::holds_alternative<typename ItreeF<
                   Sum1<MatchObserveAliasFamily::aE<Nat>,
                        MatchObserveAliasFamily::BE, crane::obj>,
                   Nat,
                   Itree<Sum1<MatchObserveAliasFamily::aE<Nat>,
                              MatchObserveAliasFamily::BE, crane::obj>,
                         Nat>>::TauF>(_sv0.v())) {
      const auto &[t0] = std::get<
          typename ItreeF<Sum1<MatchObserveAliasFamily::aE<Nat>,
                               MatchObserveAliasFamily::BE, crane::obj>,
                          Nat,
                          Itree<Sum1<MatchObserveAliasFamily::aE<Nat>,
                                     MatchObserveAliasFamily::BE, crane::obj>,
                                Nat>>::TauF>(_sv0.v());
      return run(*a0, t0);
    } else {
      return std::optional<Nat>();
    }
  }
}
