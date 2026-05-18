#include "doc_comments.h"

/// add computes the sum of two natural numbers n and m.
/// It works by structural recursion on n.
uint64_t DocComments::add(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t p = n - 1;
    return (add(p, m) + 1);
  }
}

uint64_t DocComments::no_doc_comment(uint64_t x) { return x; }

/// double n returns 2 * n.
uint64_t DocComments::double_(uint64_t n) { return add(n, n); }
