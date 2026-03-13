#include <doc_comments.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

/// add computes the sum of two natural numbers n and m.
/// It works by structural recursion on n.
__attribute__((pure)) unsigned int DocComments::add(const unsigned int n,
                                                    const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int p = n - 1;
    return (add(std::move(p), m) + 1);
  }
}

__attribute__((pure)) unsigned int
DocComments::no_doc_comment(const unsigned int x) {
  return std::move(x);
}

/// double n returns 2 * n.
__attribute__((pure)) unsigned int DocComments::double_(const unsigned int n) {
  return add(n, n);
}
