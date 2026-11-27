#include "gadt_index_erasure.h"

crane::obj GadtIndexErasure::eval(const GadtIndexErasure::expr &e) {
  if (std::holds_alternative<typename GadtIndexErasure::expr::Lit>(e.v())) {
    const auto &[a0] = std::get<typename GadtIndexErasure::expr::Lit>(e.v());
    return a0;
  } else if (std::holds_alternative<typename GadtIndexErasure::expr::Bl>(e.v())) {
    const auto &[a0] = std::get<typename GadtIndexErasure::expr::Bl>(e.v());
    return a0;
  } else if (
          std::holds_alternative<typename GadtIndexErasure::expr::Ite>(e.v())) {
    const auto &[a, a1, a2] =
        std::get<typename GadtIndexErasure::expr::Ite>(e.v());
    if (crane::any_cast<bool>(eval(*a))) {
      return eval(*a1);
    } else {
      return eval(*a2);
    }
  } else {
    const auto &[a0, b0] =
        std::get<typename GadtIndexErasure::expr::Pair>(e.v());
    return std::make_pair(crane::obj(eval(*a0)), crane::obj(eval(*b0)));
  }
}

/// The evaluator is passed as a function value to map, which instantiates
/// it at nat while its signature still returns std::any.
List<uint64_t>
GadtIndexErasure::evalAll(const List<GadtIndexErasure::expr> &l) {
  return l.template map<uint64_t>([](GadtIndexErasure::expr _ue0) {
    return crane::any_cast<uint64_t>(eval(_ue0));
  });
}
