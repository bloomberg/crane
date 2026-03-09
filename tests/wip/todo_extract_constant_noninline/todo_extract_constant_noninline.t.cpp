// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <cassert>

#include "todo_extract_constant_noninline.h"

int main()
{
    assert(TodoExtractConstantNoninline::test_value == 5u);
    assert(TodoExtractConstantNoninline::twice_value == 4u);
    return 0;
}
