// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: a self-referential inductive inside a functor must not
// generate doubled type names like HashTrie::Trie::template Trie<X>.

#include "SepExtSelfRefInductive.h"

struct IntS {
  using t = int;
};

int main() {
  const auto t = SepExtSelfRefInductive::HashTrie<IntS>::empty<bool>();
  const bool b = SepExtSelfRefInductive::HashTrie<IntS>::is_empty<bool>(t);
  (void)b;
  return 0;
}
