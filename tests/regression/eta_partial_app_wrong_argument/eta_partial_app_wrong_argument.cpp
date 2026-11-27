#include "eta_partial_app_wrong_argument.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A function-typed recursive call z r [] used as a local fixpoint's
/// accumulator is eta-expanded to [=](uint64_t) -> bool { return z(a1_value,
/// _pa1, _loop_x0); }: the lambda's parameter is left unnamed and the call
/// passes the loop's accumulator (crane::fn<bool(uint64_t)>) in its place,
/// "no viable conversion from 'const crane::fn<bool (uint64_t)>' to
/// 'uint64_t'".  The eta-expansion's parameter is _x0, spelled like
/// go's accumulator, and the tail loop renamed every _x0 to _loop_x0,
/// the lambda's own included.  The renaming now stops at a lambda whose
/// parameter shadows the name.
bool EtaPartialAppWrongArgument::z(const List<uint64_t> &l,
                                   const List<uint64_t> &m, uint64_t x0_) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return true;
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(m.v())) {
      return true;
    } else {
      const auto &[a00, a10] = std::get<typename List<uint64_t>::Cons>(m.v());
      const List<uint64_t> &a10_value = *a10;
      const List<bool> &_lc1_k = List<bool>::nil();
      const crane::fn<bool(uint64_t)> &_lc1_x0 =
          [=, a10_value = a10_value, a1_value = a1_value](uint64_t _x0) -> bool {
            return z(a1_value, a10_value, _x0);
          };
      // Loop replaces the tail recursion: each recursive call updates the loop
      // variables.
      const List<bool> *_lc1_loop_k = &_lc1_k;
      while (true) {
        if (std::holds_alternative<typename List<bool>::Nil>(_lc1_loop_k->v())) {
          crane::fn<bool(uint64_t)> cf = [](uint64_t) { return false; };
          crane::fn<uint64_t(uint64_t)> cg = [=](uint64_t) { return a00; };
          return cf(cg(x0_));
        } else {
          const auto &[_, a11] =
              std::get<typename List<bool>::Cons>(_lc1_loop_k->v());
          const List<bool> &a11_value = *a11;
          _lc1_loop_k = &a11_value;
        }
      }
    }
  }
}
