// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
#include <list_dep_type_erasure.h>

#include <cassert>
#include <cstdint>
#include <iostream>

int main() {
    // Referencing [d] forces its [contents] field initializer to compile.  With
    // the bug that initializer is [List<T1>::cons(...)] ('T1' undeclared here);
    // once fixed it is [List<crane::obj>::cons(...)], matching the erased field.
    std::uint64_t n = ListDepTypeErasure::dlen(ListDepTypeErasure::d);
    std::cout << "dlen(d) = " << n << std::endl;
    assert(n == 3);
    return 0;
}
