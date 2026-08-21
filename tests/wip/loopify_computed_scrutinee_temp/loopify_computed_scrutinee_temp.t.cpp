#include <loopify_computed_scrutinee_temp.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: go n = 7*n + n*(n-1)/2.
  for (unsigned n : {1u, 5u, 10u, 33u, 100u}) {
    unsigned want = 7u * n + n * (n - 1u) / 2u;
    unsigned got = LoopifyComputedScrutineeTemp::go(n);
    std::cout << "go " << n << " = " << got << " (want " << want << ")"
              << std::endl;
    assert(got == want);
  }
  return 0;
}
