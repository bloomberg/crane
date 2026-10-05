// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <semantic_fold.h>

#include <cassert>
#include <cstdint>
#include <iostream>

using list = SemanticFold::list;

// Values computed at extraction time are constant expressions.
static_assert(SemanticFold::ten_sum == 55);
static_assert(SemanticFold::scaled == 3 * (0 + 1 + 2 + 3) + 4);
// 1 - (2 - (3 - (4 - 0))), each step saturating at zero.
static_assert(SemanticFold::alt_small == 0);
static_assert(SemanticFold::third == SemanticFold::Color::BLUE);

int main() {
  // Frame-per-element recursion over this many cells overflows the stack at
  // -O0; the accumulator loop does not.
  // Built here rather than by [seq], which recurses per element too.
  list l = list::nil();
  for (uint64_t i = 2000000; i > 0; --i) {
    l = list::cons(i, std::move(l));
  }
  assert(SemanticFold::sum(l) == UINT64_C(2000000) * UINT64_C(2000001) / 2);

  // Unsigned addition wraps at the declared width, in either association.
  list w = list::cons(UINT64_MAX, list::cons(UINT64_C(2), list::nil()));
  assert(SemanticFold::sum(w) == UINT64_C(1));
  assert(SemanticFold::sum_scaled(UINT64_C(1), w) == UINT64_C(3));

  list s = SemanticFold::seq(UINT64_C(1), UINT64_C(4));
  assert(SemanticFold::alt(s) == UINT64_C(0));
  // Each level of [alt] evaluates its recursive call once, though the
  // subtraction's mapping mentions it twice: thirty levels would otherwise
  // make about a billion calls.
  assert(SemanticFold::alt(SemanticFold::seq(UINT64_C(1), UINT64_C(30))) == UINT64_C(0));
  assert(SemanticFold::sum_(s) == UINT64_C(10));
  assert(SemanticFold::big_sum == UINT64_C(29999) * UINT64_C(30000) / 2);

  std::cout << "semantic_fold: ok\n";
  return 0;
}
