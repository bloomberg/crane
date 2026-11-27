#include "sig_is_its_witness.h"

/// A plain witness, built, projected and matched.
uint64_t SigIsItsWitness::pos(uint64_t n) { return (n + 1); }

uint64_t SigIsItsWitness::pos_val(uint64_t n) { return pos(n); }

uint64_t SigIsItsWitness::pos_match(uint64_t n) {
  const uint64_t &m = pos(n);
  return m + UINT64_C(1);
}

/// Nested: a sig of a sig.
uint64_t SigIsItsWitness::nested(uint64_t n) { return pos(n); }

uint64_t SigIsItsWitness::nested_val(uint64_t n) { return nested(n); }

uint64_t SigIsItsWitness::apply_fixes_zero(uint64_t n) { return fixes_zero(n); }

uint64_t SigIsItsWitness::unit_sig_used(uint64_t n) {
  const std::monostate &u = unit_sig;
  return n;
}

List<uint64_t> SigIsItsWitness::unwrap_list(const List<uint64_t> &xs) {
  return wrap<List<uint64_t>>(xs);
}

/// Witnesses in a container.
List<uint64_t> SigIsItsWitness::positives(uint64_t k) {
  if (k <= 0) {
    return List<uint64_t>::nil();
  } else {
    uint64_t k_ = k - 1;
    return List<uint64_t>::cons(pos(k_), positives(k_));
  }
}

uint64_t SigIsItsWitness::sum_positives(uint64_t k) {
  return positives(k).template fold_left<uint64_t>(
      [](uint64_t acc, uint64_t p) { return acc + p; },
      UINT64_C(0));
}

uint64_t SigIsItsWitness::rt_sum(const SigIsItsWitness::rt &t) {
  if (std::holds_alternative<typename SigIsItsWitness::rt::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename SigIsItsWitness::rt::Node>(t.v());
    const SigIsItsWitness::rt &r = (*a0);
    return a1 + rt_sum(r);
  }
}

/// sig2.
uint64_t SigIsItsWitness::between(uint64_t n) { return n; }

uint64_t SigIsItsWitness::between_val(uint64_t n) {
  const uint64_t &m = between(n);
  return m;
}
