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
  {
    const Positive &_lc1_p = Positive::xo(a);
    const Positive &_lc1_x = Positive::xo(b);
    const Positive *_lc1_loop_x = &_lc1_x;
    const Positive *_lc1_loop_p = &_lc1_p;
    while (true) {
      if (std::holds_alternative<typename Positive::XI>(_lc1_loop_p->v())) {
        const auto &[a0] = std::get<typename Positive::XI>(_lc1_loop_p->v());
        if (std::holds_alternative<typename Positive::XI>(_lc1_loop_x->v())) {
          const auto &[a00] = std::get<typename Positive::XI>(_lc1_loop_x->v());
          _lc1_loop_x = crane_raw(a00);
          _lc1_loop_p = crane_raw(a0);
        } else {
          return false;
        }
      } else if (std::holds_alternative<typename Positive::XO>(
                     _lc1_loop_p->v())) {
        const auto &[a0] = std::get<typename Positive::XO>(_lc1_loop_p->v());
        if (std::holds_alternative<typename Positive::XO>(_lc1_loop_x->v())) {
          const auto &[a00] = std::get<typename Positive::XO>(_lc1_loop_x->v());
          _lc1_loop_x = crane_raw(a00);
          _lc1_loop_p = crane_raw(a0);
        } else {
          return false;
        }
      } else {
        if (std::holds_alternative<typename Positive::XH>(_lc1_loop_x->v())) {
          return true;
        } else {
          return false;
        }
      }
    }
  }
}
