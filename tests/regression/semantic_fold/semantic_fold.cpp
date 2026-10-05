#include "semantic_fold.h"

/// Rewrites licensed by declared meanings (Crane Semantics): a sum over a
/// list carried forward in an accumulator, and small closed definitions
/// computed at extraction time.  Each has a counterpart that must be left as
/// written.
SemanticFold::list SemanticFold::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return list::nil();
  } else {
    uint64_t n = len - 1;
    return list::cons(start, seq((start + 1), n));
  }
}

/// Whitelisted: unsigned addition of a pure contribution, rewritten to a
/// loop.  A list long enough to exhaust the stack frame by frame must sum.
uint64_t SemanticFold::sum(const SemanticFold::list &l) {
  {
    const SemanticFold::list &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const SemanticFold::list *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename SemanticFold::list::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename SemanticFold::list::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + a0);
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

uint64_t SemanticFold::sum_scaled(uint64_t k, const SemanticFold::list &l) {
  {
    const SemanticFold::list &_lc1_l0 = l;
    uint64_t _lc1_acc = UINT64_C(0);
    uint64_t _lc1_loop_acc = _lc1_acc;
    const SemanticFold::list *_lc1_loop_l0 = &_lc1_l0;
    while (true) {
      if (std::holds_alternative<typename SemanticFold::list::Nil>(
              _lc1_loop_l0->v())) {
        return _lc1_loop_acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename SemanticFold::list::Cons>(_lc1_loop_l0->v());
        _lc1_loop_acc = (_lc1_loop_acc + ((k * a0) + UINT64_C(1)));
        _lc1_loop_l0 = crane_raw(a1);
      }
    }
  }
}

/// Declined: sub is not associative.
uint64_t SemanticFold::alt(const SemanticFold::list &l) {
  if (std::holds_alternative<typename SemanticFold::list::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename SemanticFold::list::Cons>(l.v());
    auto &&_once1 = alt(*a1);
    return (((a0 - _once1) > a0 ? 0 : (a0 - _once1)));
  }
}

/// Declined: plus' is the program's own function, with no declared
/// meaning.
uint64_t SemanticFold::plus_(uint64_t x0_, uint64_t x1_) { return (x0_ + x1_); }

uint64_t SemanticFold::sum_(const SemanticFold::list &l) {
  if (std::holds_alternative<typename SemanticFold::list::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename SemanticFold::list::Cons>(l.v());
    return plus_(a0, sum_(*a1));
  }
}

SemanticFold::Color SemanticFold::next(SemanticFold::Color c) {
  switch (c) {
  case Color::RED: {
    return Color::GREEN;
  }
  case Color::GREEN: {
    return Color::BLUE;
  }
  case Color::BLUE: {
    return Color::RED;
  }
  default:
    std::unreachable();
  }
}
