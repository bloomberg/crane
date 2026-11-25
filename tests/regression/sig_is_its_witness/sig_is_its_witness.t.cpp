// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <sig_is_its_witness.h>

#include <iostream>

namespace {
int failures = 0;
void check(bool ok, const char *what) {
  if (!ok) {
    std::cout << "FAILED: " << what << std::endl;
    ++failures;
  }
}
} // namespace

int main() {
  using M = SigIsItsWitness;
  check(M::pos_val(4) == 5, "pos_val 4 = 5");
  check(M::pos_match(4) == 6, "pos_match 4 = 6");
  check(M::nested_val(2) == 3, "nested_val 2 = 3");
  check(M::apply_fixes_zero(21) == 42, "apply_fixes_zero 21 = 42");
  check(M::unit_sig_used(7) == 7, "unit_sig_used 7 = 7");
  auto xs = List<uint64_t>::cons(1, List<uint64_t>::cons(2, List<uint64_t>::nil()));
  {
    auto ys = M::unwrap_list(xs);
    const auto *c = std::get_if<typename List<uint64_t>::Cons>(&ys.v());
    check(c && c->a == 1, "unwrap_list keeps the list");
  }
  check(M::sum_positives(3) == 6, "sum_positives 3 = 1 + 2 + 3");
  check(M::rt_example_sum == 7, "rt_example_sum = 7");
  check(M::between_val(9) == 9, "between_val 9 = 9");
  if (failures == 0) {
    std::cout << "sig_is_its_witness: all tests passed" << std::endl;
  }
  return failures;
}
