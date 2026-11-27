#include "local_fix_nontail_function_result.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local fixpoint returning a function through a non-tail recursive call
/// (let rv := go r acc in if .. then (fun _ => Leaf) else rv), in a match
/// branch, called on a literal []: under CRANE_CHECK_IR=1 "closure escape:
/// the local fixpoint go escapes in its generated code but nowhere in Core".
/// The tail-call shapes in local_fix_returns_function and
/// local_fix_function_result_inlined are fixed.  Eta-expanded to the
/// function's argument, go r acc is a partial application, whose closure
/// holds go: escape analysis now counts one as an escape.
/// Variants: the call in mutual fixpoints, through a second local fixpoint
/// whose step returns its function accumulator, and with the outer
/// fixpoint called inside the inner one's step.
List<LocalFixNontailFunctionResult::pt> LocalFixNontailFunctionResult::h6a(
    uint64_t n, const LocalFixNontailFunctionResult::tree &x0_) {
  if (n <= 0) {
    return List<LocalFixNontailFunctionResult::pt>::nil();
  } else {
    uint64_t m = n - 1;
    auto go_impl =
        [](auto &_self_go, List<uint64_t> l,
           crane::fn<List<LocalFixNontailFunctionResult::pt>(
               LocalFixNontailFunctionResult::tree)> acc,
           LocalFixNontailFunctionResult::tree x0_0)
             -> List<LocalFixNontailFunctionResult::pt> {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
            return acc(std::move(x0_0));
          } else {
            auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
            const List<uint64_t> &a1_value = *a1;
            crane::fn<List<LocalFixNontailFunctionResult::pt>(
                LocalFixNontailFunctionResult::tree)> rv =
                [=, a1_value = a1_value, acc = std::move(acc)](
                    LocalFixNontailFunctionResult::tree _pa0) {
                  return _self_go(_self_go, a1_value, std::move(acc), _pa0);
                };
            auto go2 =
                [](const List<uint64_t> &l2,
                   const crane::fn<List<LocalFixNontailFunctionResult::pt>(
                       LocalFixNontailFunctionResult::tree)> &a2,
                   const LocalFixNontailFunctionResult::tree &x0_1)
                     -> List<LocalFixNontailFunctionResult::pt> {
                  // Loop replaces the tail recursion: each recursive call
                  // updates the loop variables.
                  const List<uint64_t> *_loop_l2 = &l2;
                  while (true) {
                    if (std::holds_alternative<typename List<uint64_t>::Nil>(
                            _loop_l2->v())) {
                      return a2(x0_1);
                    } else {
                      const auto &[_, a10] = std::get<
                          typename List<uint64_t>::Cons>(_loop_l2->v());
                      _loop_l2 = crane_raw(a10);
                    }
                  }
                };
            return go2(
                List<uint64_t>::cons(std::move(a0), List<uint64_t>::nil()),
                std::move(rv), std::move(x0_0));
          }
        };
    List<uint64_t> _lc1_l = List<uint64_t>::cons(
        UINT64_C(1), List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()));
    crane::fn<List<LocalFixNontailFunctionResult::pt>(
        LocalFixNontailFunctionResult::tree)> _lc1_acc =
        [=](LocalFixNontailFunctionResult::tree _x0) -> List<
            LocalFixNontailFunctionResult::pt> { return h6b(m, _x0); };
    LocalFixNontailFunctionResult::tree _lc1_x0_0 = x0_;
    return go_impl(go_impl, std::move(_lc1_l), std::move(_lc1_acc),
                   std::move(_lc1_x0_0));
  }
}

List<LocalFixNontailFunctionResult::pt> LocalFixNontailFunctionResult::h6b(
    uint64_t n, const LocalFixNontailFunctionResult::tree &x0_) {
  if (n <= 0) {
    return List<LocalFixNontailFunctionResult::pt>::cons(
        pt{UINT64_C(0), true}, List<LocalFixNontailFunctionResult::pt>::nil());
  } else {
    uint64_t m = n - 1;
    return h6a(m, x0_);
  }
}

List<LocalFixNontailFunctionResult::pt> LocalFixNontailFunctionResult::k1(
    uint64_t n, const LocalFixNontailFunctionResult::tree &x0_) {
  if (n <= 0) {
    return List<LocalFixNontailFunctionResult::pt>::nil();
  } else {
    uint64_t m = n - 1;
    auto go_impl =
        [](auto &_self_go, List<uint64_t> l,
           crane::fn<List<LocalFixNontailFunctionResult::pt>(
               LocalFixNontailFunctionResult::tree)> acc,
           LocalFixNontailFunctionResult::tree x0_0)
             -> List<LocalFixNontailFunctionResult::pt> {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
            return acc(std::move(x0_0));
          } else {
            auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v_mut());
            const List<uint64_t> &a1_value = *a1;
            auto go2 =
                [=, a1_value = a1_value](
                    List<uint64_t> l2,
                    crane::fn<List<LocalFixNontailFunctionResult::pt>(
                        LocalFixNontailFunctionResult::tree)> a2,
                    LocalFixNontailFunctionResult::tree x0_1)
                     -> List<LocalFixNontailFunctionResult::pt> {
                  // Loop replaces the tail recursion: each recursive call
                  // updates the loop variables.
                  List<uint64_t> _loop_l2 = std::move(l2);
                  while (true) {
                    if (std::holds_alternative<typename List<uint64_t>::Nil>(
                            _loop_l2.v_mut())) {
                      return _self_go(_self_go, a1_value, std::move(a2),
                                      std::move(x0_1));
                    } else {
                      auto &[_, a10] = std::get<typename List<uint64_t>::Cons>(
                          _loop_l2.v_mut());
                      _loop_l2 = List<uint64_t>(*a10);
                    }
                  }
                };
            crane::fn<List<LocalFixNontailFunctionResult::pt>(
                LocalFixNontailFunctionResult::tree)> rv =
                [=, acc = std::move(acc), go2 = std::move(go2)](
                    LocalFixNontailFunctionResult::tree _pa0) {
                  return go2(List<uint64_t>::cons(a0, List<uint64_t>::nil()),
                             std::move(acc), _pa0);
                };
            if (a0 == UINT64_C(7)) {
              return List<LocalFixNontailFunctionResult::pt>::nil();
            } else {
              return rv(std::move(x0_0));
            }
          }
        };
    List<uint64_t> _lc1_l = List<uint64_t>::cons(
        UINT64_C(1), List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()));
    crane::fn<List<LocalFixNontailFunctionResult::pt>(
        LocalFixNontailFunctionResult::tree)> _lc1_acc =
        [=](LocalFixNontailFunctionResult::tree _x0) -> List<
            LocalFixNontailFunctionResult::pt> { return k1(m, _x0); };
    LocalFixNontailFunctionResult::tree _lc1_x0_0 = x0_;
    return go_impl(go_impl, std::move(_lc1_l), std::move(_lc1_acc),
                   std::move(_lc1_x0_0));
  }
}
