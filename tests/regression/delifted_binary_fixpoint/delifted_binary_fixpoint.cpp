#include "delifted_binary_fixpoint.h"

/// A local fixpoint of two arguments that is not lifted to a helper, because
/// its return type is recovered from its body.  Every other de-lifted
/// fixpoint in the suite is unary, and a unary one cannot show whether the
/// self-call passes all of its arguments: _self_go(_self_go, p)(x) and
/// _self_go(_self_go, p, x) differ only from arity two up.
///
/// This does not reproduce the curried spine -- the optimiser uncurries this
/// body before translation sees it, whichever way the recursion is written.
/// It covers the arity-two de-lift path, which nothing else did.
bool DeliftedBinaryFixpoint::same(Positive a, Positive b) {
  auto go_impl = [](auto &_self_go, const Positive &p,
                    const Positive &x) -> bool {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      if (std::holds_alternative<typename Positive::XI>(x.v())) {
        const auto &[a00] = std::get<typename Positive::XI>(x.v());
        return _self_go(_self_go, *a0, *a00);
      } else {
        return false;
      }
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      if (std::holds_alternative<typename Positive::XO>(x.v())) {
        const auto &[a00] = std::get<typename Positive::XO>(x.v());
        return _self_go(_self_go, *a0, *a00);
      } else {
        return false;
      }
    } else {
      if (std::holds_alternative<typename Positive::XH>(x.v())) {
        return true;
      } else {
        return false;
      }
    }
  };
  auto go = [&](const Positive &p, const Positive &x) -> bool {
    return go_impl(go_impl, p, x);
  };
  return go(Positive::xo(std::move(a)), Positive::xo(std::move(b)));
}
