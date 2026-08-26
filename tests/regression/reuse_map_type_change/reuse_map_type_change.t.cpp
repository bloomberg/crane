#include <reuse_map_type_change.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: go1 n = n*(n+1)/2 + n, go2 n = n*(n+1).
  for (unsigned n : {1u, 5u, 10u}) {
    unsigned w1 = n * (n + 1u) / 2u + n;
    unsigned w2 = n * (n + 1u);
    unsigned g1 = ReuseMapTypeChange::go1(n);
    unsigned g2 = ReuseMapTypeChange::go2(n);
    std::cout << "go1 " << n << " = " << g1 << " (want " << w1 << ")   go2 "
              << n << " = " << g2 << " (want " << w2 << ")" << std::endl;
    assert(g1 == w1);
    assert(g2 == w2);
  }
  return 0;
}
