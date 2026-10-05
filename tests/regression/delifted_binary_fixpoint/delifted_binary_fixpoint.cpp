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
bool DeliftedBinaryFixpoint::same(const Positive &a, const Positive &b) {
  auto go = [](const Positive &p, const Positive &x) -> bool {
    const Positive *_loop_x = &x;
    const Positive *_loop_p = &p;
    while (true) {
      if (std::holds_alternative<typename Positive::XI>(_loop_p->v())) {
        const auto &[a0] = std::get<typename Positive::XI>(_loop_p->v());
        if (std::holds_alternative<typename Positive::XI>(_loop_x->v())) {
          const auto &[a00] = std::get<typename Positive::XI>(_loop_x->v());
          _loop_x = crane_raw(a00);
          _loop_p = crane_raw(a0);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Positive::XO>(_loop_p->v())) {
        const auto &[a0] = std::get<typename Positive::XO>(_loop_p->v());
        if (std::holds_alternative<typename Positive::XO>(_loop_x->v())) {
          const auto &[a00] = std::get<typename Positive::XO>(_loop_x->v());
          _loop_x = crane_raw(a00);
          _loop_p = crane_raw(a0);
        } else {
          return false;
        }
      } else {
        if (std::holds_alternative<typename Positive::XH>(_loop_x->v())) {
          return true;
        } else {
          return false;
        }
      }
    }
  };
  return go(Positive::xo(a), Positive::xo(b));
}
