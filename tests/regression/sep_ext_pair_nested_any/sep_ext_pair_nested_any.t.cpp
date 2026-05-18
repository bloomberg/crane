// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: Crane generates any_cast<pair<any,any>> for a pair pattern match
// when the pair type has std::any in a nested position.  The pair is
// concrete at runtime, so std::any_cast throws bad_any_cast.
//
// use_it is a namespace-level const bool initialized at static-init time.
// The initializer calls any_cast<pair<any,any>>(produce) where produce
// has type std::pair<std::optional<List<SigT<Nat,std::any>>>,bool>.
// That cast throws bad_any_cast, std::terminate is called, and the
// program exits non-zero before main() runs.
//
// When the bug is fixed: use_it is initialized to true (the match on
// (None, true) returns the second component b = true), and main returns 0.

#include "SepExtPairNestedAny.h"

int main() {
  // produce = (None, true); use_it = match produce with | (_, b) => b = true.
  return SepExtPairNestedAny::use_it ? 0 : 1;
}
