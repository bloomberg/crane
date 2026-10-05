#include "vis_cont_type.h"

std::optional<Nat>
VisContType::run(const Nat &fuel,
                 const VisContType::tree<VisContType::noE, Nat> &t) {
  if (std::holds_alternative<typename Nat::O>(fuel.v())) {
    return std::optional<Nat>();
  } else {
    const auto &[a0] = std::get<typename Nat::S>(fuel.v());
    return [&]() {
      auto &&_sv0 = observe<VisContType::noE, Nat>(t);
      if (std::holds_alternative<typename VisContType::treeF<
              VisContType::noE, Nat,
              VisContType::tree<VisContType::noE, Nat>>::RetF>(_sv0.v())) {
        const auto &[r0] = std::get<typename VisContType::treeF<
            VisContType::noE, Nat,
            VisContType::tree<VisContType::noE, Nat>>::RetF>(_sv0.v());
        return std::make_optional<Nat>(r0);
      } else if (std::holds_alternative<typename VisContType::treeF<
                     VisContType::noE, Nat,
                     VisContType::tree<VisContType::noE, Nat>>::TauF>(
                     _sv0.v())) {
        const auto &[t2] = std::get<typename VisContType::treeF<
            VisContType::noE, Nat,
            VisContType::tree<VisContType::noE, Nat>>::TauF>(_sv0.v());
        return run(*a0, t2);
      } else {
        throw std::logic_error("absurd case");
      }
    }();
  }
}
