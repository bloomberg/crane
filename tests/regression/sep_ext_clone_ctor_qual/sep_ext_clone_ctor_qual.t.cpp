// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// Regression: the unique-ptr pre-extraction binding for list tails inside
// a template functor must use the fully-qualified type name.  Previously,
// Crane emitted bare List<std::pair<t, T1>> deriving from the unique_ptr
// field instead of Datatypes::List<std::pair<typename X::t, T1>>.

#include "SepExtCloneCtorQual.h"

#include <cassert>
#include <utility>

struct IntOT {
  using t = int;
};

int main() {
  using FL = SepExtCloneCtorQual::FMapList<IntOT>;

  // nil case: has_tail returns false for any value
  Datatypes::List<std::pair<int, bool>> empty{};
  assert(!FL::has_tail(empty, true));

  // cons case: has_tail returns true regardless of the value
  auto nonempty = Datatypes::List<std::pair<int, bool>>::cons(
      std::make_pair(42, false), Datatypes::List<std::pair<int, bool>>{});
  assert(FL::has_tail(nonempty, false));

  return 0;
}
