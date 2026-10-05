#include "vis_existential_cont.h"

std::optional<Nat> VisExistentialCont::answer(
    const Nat &,
    const VisExistentialCont::tree<VisExistentialCont::askE, Nat> &t0) {
  auto &&_sv = observe<VisExistentialCont::askE, Nat>(t0);
  if (std::holds_alternative<typename VisExistentialCont::treeF<
          VisExistentialCont::askE, Nat,
          VisExistentialCont::tree<VisExistentialCont::askE, Nat>>::RetF>(
          _sv.v())) {
    const auto &[r0] = std::get<typename VisExistentialCont::treeF<
        VisExistentialCont::askE, Nat,
        VisExistentialCont::tree<VisExistentialCont::askE, Nat>>::RetF>(
        _sv.v());
    return std::make_optional<Nat>(r0);
  } else if (std::holds_alternative<typename VisExistentialCont::treeF<
                 VisExistentialCont::askE, Nat,
                 VisExistentialCont::tree<VisExistentialCont::askE,
                                          Nat>>::TauF>(_sv.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[x, e0] = std::get<typename VisExistentialCont::treeF<
        VisExistentialCont::askE, Nat,
        VisExistentialCont::tree<VisExistentialCont::askE, Nat>>::VisF>(
        _sv.v());
    const auto &[a00] = x;
    auto &&_sv1 = observe<VisExistentialCont::askE, Nat>(e0(a00));
    if (std::holds_alternative<typename VisExistentialCont::treeF<
            VisExistentialCont::askE, Nat,
            VisExistentialCont::tree<VisExistentialCont::askE, Nat>>::RetF>(
            _sv1.v())) {
      const auto &[r1] = std::get<typename VisExistentialCont::treeF<
          VisExistentialCont::askE, Nat,
          VisExistentialCont::tree<VisExistentialCont::askE, Nat>>::RetF>(
          _sv1.v());
      return std::make_optional<Nat>(r1);
    } else {
      return std::optional<Nat>();
    }
  }
}
