// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: Nested tuple access (fst (snd vs)) where the tuple is erased
// to std::any.  Crane generates any_cast<pair<ConcreteA, pair<...>>>
// but runtime type is pair<any, any> — a double-cast failure.

#include "SepExtAnyNestedMatch.h"

int main() {
  return 0;
}
