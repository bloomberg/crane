#include <loopify_reuse_bool_qualified.h>

#include <cassert>
#include <iostream>

int main() {
  // Rocq: go n = sum (incr [1..n]) = n*(n+1)/2 + n.
  for (unsigned n : {1u, 5u, 10u}) {
    unsigned want = n * (n + 1u) / 2u + n;
    unsigned got = LoopifyReuseBoolQualified::go(n);
    std::cout << "go " << n << " = " << got << " (want " << want << ")"
              << std::endl;
    assert(got == want);
  }
  return 0;
}
