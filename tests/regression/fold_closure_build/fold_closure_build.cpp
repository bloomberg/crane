#include "fold_closure_build.h"

/// Pattern 1: Build a COMPOSED function via fold.
/// Each step wraps the accumulator in a new closure.
///
/// Equivalent to:
/// compose_all 10, 20, 30 id
/// = fold_left (fun acc h => fun x => acc(h + x)) id 10,20,30
/// = fun x => id(10 + (20 + (30 + x)))
/// = fun x => 60 + x
///
/// The inner closure fun x => acc(h+x) captures acc (std::function)
/// and h (unsigned int). If these are captured by =, safe. By &, dangles.
uint64_t
FoldClosureBuild::compose_adders(const FoldClosureBuild::mylist<uint64_t> &l,
                                 uint64_t _x0) {
  return fold_left<std::function<uint64_t(uint64_t)>, uint64_t>(
      [](std::function<uint64_t(uint64_t)> acc,
         uint64_t h) -> std::function<uint64_t(uint64_t)> {
        return [=](uint64_t x) mutable { return acc((h + x)); };
      },
      [](uint64_t x) { return x; }, l)(_x0);
}

/// Pattern 3: Fold producing a list of closures (not composing them).
/// Each closure captures the list element from the fold iteration.
FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>>
FoldClosureBuild::collect_adders(const FoldClosureBuild::mylist<uint64_t> &l) {
  return fold_left<FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>>,
                   uint64_t>(
      [](FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>> acc,
         uint64_t h) {
        return mylist<std::function<uint64_t(uint64_t)>>::mycons(
            [=](uint64_t x) mutable { return (h + x); }, acc);
      },
      mylist<std::function<uint64_t(uint64_t)>>::mynil(), l);
}

uint64_t FoldClosureBuild::apply_all(
    const FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  if (std::holds_alternative<typename FoldClosureBuild::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename FoldClosureBuild::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return (a0(x) + apply_all(*a1, x));
  }
}

/// Pattern 4: Fold with a FIXPOINT as accumulator.
/// The fixpoint captures both acc and h from the fold callback.
///
/// BUG HYPOTHESIS: The fixpoint go uses & to capture acc and h.
/// acc is the std::function accumulator from fold_left.
/// h is the current list element.
/// Both are locals in the fold callback's scope.
/// When fold returns, these scopes are destroyed, but the
/// final fixpoint (stored in the accumulator) still references them.
uint64_t
FoldClosureBuild::compose_with_fix(const FoldClosureBuild::mylist<uint64_t> &l,
                                   uint64_t _x0) {
  return fold_left<std::function<uint64_t(uint64_t)>, uint64_t>(
      [](std::function<uint64_t(uint64_t)> acc, uint64_t h) {
        auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
          if (x <= 0) {
            return acc(h);
          } else {
            uint64_t x_ = x - 1;
            return (_self_go(_self_go, x_) + 1);
          }
        };
        auto go = [=](uint64_t x) mutable -> uint64_t {
          return go_impl(go_impl, x);
        };
        return go;
      },
      [](uint64_t x) { return x; }, l)(_x0);
}
