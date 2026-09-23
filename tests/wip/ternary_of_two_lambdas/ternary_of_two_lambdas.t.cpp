#include <ternary_of_two_lambdas.h>

#include <cassert>

namespace {

Nat nat_of(int k) {
  Nat n = Nat::o();
  for (int i = 0; i < k; ++i) {
    n = Nat::s(std::move(n));
  }
  return n;
}

int int_of(Nat n) {
  int k = 0;
  while (std::holds_alternative<typename Nat::S>(n.v())) {
    const auto &[a0] = std::get<typename Nat::S>(n.v());
    n = *a0;
    ++k;
  }
  return k;
}

} // namespace

int main() {
  // The gate is that [pick] compiles at all: its body is an eta-expansion
  // whose invented parameter landed outside the conditional.
  assert(int_of(go(nat_of(4), nat_of(5))) == 9);  // even: 4 + 5
  assert(int_of(go(nat_of(3), nat_of(5))) == 15); // odd:  3 * 5
  assert(int_of(go(nat_of(0), nat_of(7))) == 7);
  return 0;
}
