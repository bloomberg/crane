// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
// WIP: Crane generates "throw logic_error" for apply_entry because
// it cannot translate the dependent projT2 application when the
// function type is computed by a Fixpoint and erased to std::any.

#include "SepExtAnyFunCall.h"

struct MySym {
  using sym = int;
  using sym_semty = bool;
};

int main() {
  using A = SepExtAnyFunCall::Actions<MySym>;
  auto e = A::make_entry(
    Datatypes::List<int>::nil(),
    [](std::any) -> bool { return true; }
  );
  // Crane stubs this with throw; correct code would call the function.
  bool result = A::apply_entry(e, std::any{});
  return result ? 0 : 1;
}
