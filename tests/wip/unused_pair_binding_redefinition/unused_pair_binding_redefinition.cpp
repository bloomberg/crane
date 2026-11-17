#include "unused_pair_binding_redefinition.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Two sequential matches on pairs whose fields are unused, each scrutinee a
/// local fixpoint call, lower to two auto [_x, _x0] = ...; structured
/// bindings in one scope: "redefinition of '_x'".
uint64_t UnusedPairBindingRedefinition::f(uint64_t a) {
  uint64_t x;
  auto [_x, _x0] = [&]() {
    List<uint64_t> l = List<uint64_t>::cons(
        UINT64_C(0), List<uint64_t>::cons(UINT64_C(0), List<uint64_t>::nil()));
    std::pair<uint64_t, uint64_t> acc = std::make_pair(a, a);
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return acc;
    } else {
      return std::make_pair(a, a);
    }
  }();
  x = UINT64_C(0);
  auto [_x, _x0] = [&]() {
    List<uint64_t> l =
        List<uint64_t>::cons(a, List<uint64_t>::cons(a, List<uint64_t>::nil()));
    std::pair<bool, bool> acc = std::make_pair(true, true);
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return std::make_pair(true, true);
    } else {
      return acc;
    }
  }();
  return (x + UINT64_C(5));
}
