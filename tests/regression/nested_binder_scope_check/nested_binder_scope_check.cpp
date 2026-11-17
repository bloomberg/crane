#include "nested_binder_scope_check.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A let (or a local fixpoint call) nested in the argument of another one
/// fails the Core boundary check under CRANE_CHECK_IR=1 (the test suite's
/// setting): "binder scopes: the variable at index 2 is a to the names in
/// scope and q to the binders typed in scope".  Without the check the C++
/// is right.
///
/// - f: nested record updates through lets.
/// - g: a local fixpoint call as the accumulator of another.
NestedBinderScopeCheck::pt NestedBinderScopeCheck::f(uint64_t a) {
  NestedBinderScopeCheck::pt p;
  NestedBinderScopeCheck::pt q = pt{UINT64_C(0), true};
  p = pt{UINT64_C(0), std::move(q).py};
  return pt{a, std::move(p).py};
}

bool NestedBinderScopeCheck::g(uint64_t) {
  List<uint64_t> l = List<uint64_t>::nil();
  bool acc;
  List<uint64_t> l0 = List<uint64_t>::nil();
  bool acc0 = true;
  acc = (std::holds_alternative<typename List<uint64_t>::Nil>(l0.v()) ? true
                                                                      : acc0);
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
    return acc;
  } else {
    return true;
  }
}
