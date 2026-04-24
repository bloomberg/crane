// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "todo_monadic_global_alias.h"

namespace {

unsigned int nat_to_uint(const Nat &n) {
  if (std::holds_alternative<Nat::O>(n.v())) {
    return 0u;
  } else {
    const auto &s = std::get<Nat::S>(n.v());
    return 1u + nat_to_uint(*s.d_a0);
  }
}

} // namespace

int main() {
  assert(nat_to_uint(TodoMonadicGlobalAlias::base()) == 7u);
  assert(nat_to_uint(TodoMonadicGlobalAlias::alias()) == 7u);
  assert(nat_to_uint(TodoMonadicGlobalAlias::rebound()) == 8u);
  return 0;
}
