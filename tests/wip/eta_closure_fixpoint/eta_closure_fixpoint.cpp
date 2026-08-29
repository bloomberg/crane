#include "eta_closure_fixpoint.h"

/// The Fixpoint form of the eta-expansion arity bug: adder is emitted
/// as uint64_t adder(uint64_t, uint64_t), so map adder ... cannot build
/// the std::function<uint64_t(uint64_t)> it is declared to produce.
uint64_t EtaClosureFixpoint::adder(uint64_t n, uint64_t k) {
  if (n <= 0) {
    return k;
  } else {
    uint64_t j = n - 1;
    return (adder(j, k) + 1);
  }
}

uint64_t EtaClosureFixpoint::run(uint64_t k) {
  return List<uint64_t>::cons(
             UINT64_C(1),
             List<uint64_t>::cons(
                 UINT64_C(2),
                 List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil())))
      .template map<std::function<uint64_t(uint64_t)>>(adder)
      .template fold_left<uint64_t>(
          [](uint64_t a, std::function<uint64_t(uint64_t)> f) { return f(a); },
          k);
}
