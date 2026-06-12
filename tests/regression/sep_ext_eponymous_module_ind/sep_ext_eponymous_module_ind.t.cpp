// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: When a Module and its contained Inductive have the same name
// after capitalization (Module Trie / Inductive trie -> Trie), Crane
// should not generate a doubled path Trie::Trie<X>.

#include "SepExtEponymousModuleInd.h"
#include "Datatypes.h"

int main() {
  using T = SepExtEponymousModuleInd::Trie<std::optional<Datatypes::Nat>>;
  const T leaf = T::leaf();
  (void)leaf;
  return 0;
}
