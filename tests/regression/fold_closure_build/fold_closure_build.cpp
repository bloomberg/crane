#include <fold_closure_build.h>

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
unsigned int FoldClosureBuild::compose_adders(
    const FoldClosureBuild::mylist<unsigned int> &l, const unsigned int &_x0) {
  return fold_left<std::function<unsigned int(unsigned int)>, unsigned int>(
      [](const std::function<unsigned int(unsigned int)> acc,
         unsigned int h) -> std::function<unsigned int(unsigned int)> {
        return [=](const unsigned int &x) mutable { return acc((h + x)); };
      },
      [](unsigned int x) { return x; }, l)(_x0);
}

/// Pattern 3: Fold producing a list of closures (not composing them).
/// Each closure captures the list element from the fold iteration.
FoldClosureBuild::mylist<std::function<unsigned int(unsigned int)>>
FoldClosureBuild::collect_adders(
    const FoldClosureBuild::mylist<unsigned int> &l) {
  return fold_left<
      FoldClosureBuild::mylist<std::function<unsigned int(unsigned int)>>,
      unsigned int>(
      [](FoldClosureBuild::mylist<std::function<unsigned int(unsigned int)>>
             acc,
         unsigned int h) {
        return mylist<std::function<unsigned int(unsigned int)>>::mycons(
            [=](const unsigned int &x) mutable { return (h + x); }, acc);
      },
      mylist<std::function<unsigned int(unsigned int)>>::mynil(), l);
}

unsigned int FoldClosureBuild::apply_all(
    const FoldClosureBuild::mylist<std::function<unsigned int(unsigned int)>>
        &fns,
    const unsigned int &x) {
  if (std::holds_alternative<typename FoldClosureBuild::mylist<
          std::function<unsigned int(unsigned int)>>::Mynil>(fns.v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename FoldClosureBuild::mylist<
        std::function<unsigned int(unsigned int)>>::Mycons>(fns.v());
    return (d_a0(x) + apply_all(*(d_a1), x));
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
unsigned int FoldClosureBuild::compose_with_fix(
    const FoldClosureBuild::mylist<unsigned int> &l, const unsigned int &_x0) {
  return fold_left<std::function<unsigned int(unsigned int)>, unsigned int>(
      [](const std::function<unsigned int(unsigned int)> acc, unsigned int h) {
        auto go_impl = [=](auto &_self_go,
                           unsigned int x) mutable -> unsigned int {
          if (x <= 0) {
            return acc(h);
          } else {
            unsigned int x_ = x - 1;
            return (_self_go(_self_go, x_) + 1);
          }
        };
        auto go = [=](unsigned int x) mutable -> unsigned int {
          return go_impl(go_impl, x);
        };
        return go;
      },
      [](unsigned int x) { return x; }, l)(_x0);
}
