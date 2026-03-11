// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "todo_monadic_global_alias.h"

namespace {

unsigned int nat_to_uint(const std::shared_ptr<Nat> &n)
{
    return std::visit(
        Overloaded {
            [](const Nat::O &) -> unsigned int { return 0u; },
            [](const Nat::S &succ) -> unsigned int {
                return 1u + nat_to_uint(succ._a0);
            },
        },
        n->v());
}

}  // close unnamed namespace

int main()
{
    assert(nat_to_uint(TodoMonadicGlobalAlias::base()) == 7u);
    assert(nat_to_uint(TodoMonadicGlobalAlias::alias()) == 7u);
    assert(nat_to_uint(TodoMonadicGlobalAlias::rebound()) == 8u);
    return 0;
}
