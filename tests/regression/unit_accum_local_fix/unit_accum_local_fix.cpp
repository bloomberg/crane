#include "unit_accum_local_fix.h"

/// for_each_with at B := unit, unfolded below into a local fixpoint.
uint64_t UnitAccumLocalFix::fill(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> a =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(n),
                                                       UINT64_C(0));
  [&]() {
    auto for_each_with =
        [](const List<uint64_t> &xs, std::monostate,
           const crane::fn<void(std::monostate, uint64_t)> &f)
             -> void {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          const List<uint64_t> *_loop_xs = &xs;
          while (true) {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _loop_xs->v())) {
              return;
            } else {
              const auto &[a0, a1] =
                  std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
              f(std::monostate{}, a0);
              _loop_xs = crane_raw(a1);
            }
          }
          return;
        };
    return for_each_with(ListDef::seq(UINT64_C(0), n), std::monostate{},
                         [=](std::monostate, uint64_t i) {
                           std::span{*a}[i] = (i * UINT64_C(2));
                           return std::monostate{};
                         });
  }();
  return std::span{std::as_const(*a)}[
      (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))];
}

uint64_t UnitAccumLocalFix::fill_top(uint64_t n) {
  std::shared_ptr<crane::array_storage<uint64_t>> a =
      std::make_shared<crane::array_storage<uint64_t>>(crane::st::extent(n),
                                                       UINT64_C(0));
  each_unit(ListDef::seq(UINT64_C(0), n), [=](std::monostate, uint64_t i) {
    std::span{*a}[i] = (i * UINT64_C(3));
    return std::monostate{};
  });
  return std::span{std::as_const(*a)}[
      (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))];
}

/// A pure top-level Fixpoint returning its unit accumulator.
void UnitAccumLocalFix::walk_top(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return;
  } else {
    const auto &[_, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    walk_top(*a1);
  }
}

/// A pure local fixpoint returning its unit accumulator.
void UnitAccumLocalFix::walk(const List<uint64_t> &l) {
  auto go = [](const List<uint64_t> &xs, std::monostate) -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<uint64_t> *_loop_xs = &xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return;
      } else {
        const auto &[_, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_xs = crane_raw(a1);
      }
    }
    return;
  };
  {
    go(l, std::monostate{});
  }
}

/// The unit result of a local fixpoint used as a value.
std::pair<std::monostate, uint64_t>
UnitAccumLocalFix::walk_pair(const List<uint64_t> &l) {
  auto go = [](const List<uint64_t> &xs, std::monostate) -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<uint64_t> *_loop_xs = &xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return;
      } else {
        const auto &[_, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_xs = crane_raw(a1);
      }
    }
    return;
  };
  go(l, std::monostate{});
  return std::make_pair(std::monostate{}, l.length());
}

/// A unit-returning local fixpoint called twice, so held as a closure.
std::pair<std::monostate, std::monostate>
UnitAccumLocalFix::walk_twice(const List<uint64_t> &l) {
  auto go = [](const List<uint64_t> &xs, std::monostate) -> void {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<uint64_t> *_loop_xs = &xs;
    while (true) {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(_loop_xs->v())) {
        return;
      } else {
        const auto &[_, a1] =
            std::get<typename List<uint64_t>::Cons>(_loop_xs->v());
        _loop_xs = crane_raw(a1);
      }
    }
    return;
  };
  return std::make_pair(
      [&]() {
        go(l, std::monostate{});
        return std::monostate{};
      }(),
      [&]() {
        go(l.rev(), std::monostate{});
        return std::monostate{};
      }());
}

/// A unit accumulator threaded beside a nat one.
uint64_t UnitAccumLocalFix::sum_with_unit(const List<uint64_t> &l) {
  uint64_t _lc1_acc = UINT64_C(0);
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _lc1_loop_acc = _lc1_acc;
  const List<uint64_t> *_lc1_loop_xs = &l;
  while (true) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_lc1_loop_xs->v())) {
      return _lc1_loop_acc;
    } else {
      const auto &[a0, a1] =
          std::get<typename List<uint64_t>::Cons>(_lc1_loop_xs->v());
      _lc1_loop_acc = (_lc1_loop_acc + a0);
      _lc1_loop_xs = crane_raw(a1);
    }
  }
}

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  if (len <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t len0 = len - 1;
    return List<uint64_t>::cons(start, ListDef::seq((start + 1), len0));
  }
}
