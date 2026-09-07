// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <deep_expr_const_return.h>
#include <cassert>
#include <cstdint>

int main()
{
    assert(DeepExprConstReturn::test == 150);
    return 0;
}
