#include "functor_binder_scope_check.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by
/// hand.  The original was in a functor body; the functor is not needed.
///
/// A local fixpoint's step matches on a match of a Z parameter, and one
/// branch matches a list literal against [_], which Core writes as a let
/// in a wildcard branch.  Lowering that branch's statements pushed the let's
/// binder type and nothing popped it, so the sibling argument rest read
/// the binder one further in: under CRANE_CHECK_IR=1 extraction failed the
/// Core check "binder scopes: the variable at index 3 is x0_0 to the names
/// in scope and _x to the binders typed in scope".
uint64_t FunctorBinderScopeCheck::h(uint64_t a, Z z, const List<uint64_t> &l,
                                    uint64_t x0_) {
  return [&]() {
    auto go =
        [=](List<uint64_t> l0, crane::fn<uint64_t(uint64_t)> acc,
            uint64_t x0_0)
             -> uint64_t {
          // Loop replaces the tail recursion: each recursive call updates the
          // loop variables.
          crane::fn<uint64_t(uint64_t)> _loop_acc = std::move(acc);
          List<uint64_t> _loop_l0 = std::move(l0);
          while (true) {
            if (std::holds_alternative<typename List<uint64_t>::Nil>(
                    _loop_l0.v_mut())) {
              return _loop_acc(x0_0);
            } else {
              auto &[_, a1] =
                  std::get<typename List<uint64_t>::Cons>(_loop_l0.v_mut());
              const List<uint64_t> &a1_value = *a1;
              _loop_acc = [&]() -> crane::fn<uint64_t(uint64_t)> {
                if (std::holds_alternative<typename Z::Z0>(z.v())) {
                  return [=](uint64_t) { return a; };
                } else {
                  List<uint64_t> l1 =
                      List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil());
                  if (std::holds_alternative<typename List<uint64_t>::Nil>(
                          l1.v_mut())) {
                    return std::move(_loop_acc);
                  } else {
                    return [](uint64_t) { return UINT64_C(1); };
                  }
                }
              }();
              _loop_l0 = List<uint64_t>(a1_value);
            }
          }
        };
    return [=](uint64_t _pa0) {
      return go(l, [](uint64_t) { return UINT64_C(0); }, _pa0);
    };
  }()(x0_);
}
