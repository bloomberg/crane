#include "local_fix_returns_function.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local let fix go ... : nat -> nat applied to one more argument than it
/// binds.  The C++ lambda for go is eta-expanded to return uint64_t, but its
/// branches still return lambdas, and the recursive call names go inside its
/// own auto initializer.  Under CRANE_CHECK_IR=1 (the test suite) extraction
/// stops first: "closure escape: the local fixpoint go escapes in its
/// generated code but nowhere in Core".
uint64_t LocalFixReturnsFunction::t(const List<uint64_t> &l) {
  const crane::fn<uint64_t(uint64_t)> &_lc1_acc = [](uint64_t x) { return x; };
  uint64_t _lc1_x0_ = UINT64_C(1);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  const List<uint64_t> *_lc1_loop_l0 = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_l0->v())) {
      return (_lc1_x0_ + UINT64_C(1));
    } else {
      const auto &[_, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_l0->v());
      _lc1_loop_l0 = crane_raw(a1);
    }
  }
}

/// The same fixpoint at top level, applied to fewer arguments than it
/// binds once eta-expansion gives it the definition's last parameter: the
/// closure for the partial application passed the written arguments last
/// first, go(acc, l, _pa0), which does not compile for g and swaps
/// l and acc for h.
std::optional<uint64_t>
LocalFixReturnsFunction::g(uint64_t, std::optional<uint64_t> x0_) {
  return []() {
    auto go =
        [](List<bool> l,
           crane::fn<std::optional<uint64_t>(std::optional<uint64_t>)>,
           std::optional<uint64_t>)
             -> std::optional<uint64_t> {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          List<bool> _loop_l = std::move(l);
          while (true) {
            if (std::holds_alternative<typename List<bool>::Nil>(
                    _loop_l.v_mut())) {
              return std::optional<uint64_t>();
            } else {
              auto &[_, a1] =
                  std::get<typename List<bool>::Cons>(_loop_l.v_mut());
              _loop_l = List<bool>(*a1);
            }
          }
        };
    return [=](std::optional<uint64_t> _pa0) {
      return go(List<bool>::nil(), [](std::optional<uint64_t>) {
        return std::optional<uint64_t>();
      },
                _pa0);
    };
  }()(x0_);
}

std::optional<uint64_t>
LocalFixReturnsFunction::h(uint64_t n, std::optional<uint64_t> x0_) {
  return [&]() {
    auto go =
        [](List<bool> l, uint64_t acc,
           std::optional<uint64_t> x0_0)
             -> std::optional<uint64_t> {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          List<bool> _loop_l = std::move(l);
          while (true) {
            if (std::holds_alternative<typename List<bool>::Nil>(
                    _loop_l.v_mut())) {
              if (x0_0.has_value()) {
                const uint64_t &y = *x0_0;
                return std::make_optional<uint64_t>((y + acc));
              } else {
                return std::make_optional<uint64_t>(acc);
              }
            } else {
              auto &[_, a1] =
                  std::get<typename List<bool>::Cons>(_loop_l.v_mut());
              acc = (acc + 1);
              _loop_l = List<bool>(*a1);
            }
          }
        };
    return [=](std::optional<uint64_t> _pa0) {
      return go(List<bool>::cons(true, List<bool>::nil()), n, _pa0);
    };
  }()(x0_);
}
