// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// crane::unreachable(): std::unreachable() where the standard library has
// it (C++23), the compiler's builtin otherwise.  A switch over every
// constructor of an enum ends in it; the std flavor builds as C++26 and
// writes std::unreachable() itself, the BDE flavor builds as C++20 and
// writes this.

#pragma once

#include <utility>

namespace crane {

[[noreturn]] inline void unreachable() {
#if defined(__cpp_lib_unreachable)
  std::unreachable();
#elif defined(_MSC_VER) && !defined(__clang__)
  __assume(false);
#else
  __builtin_unreachable();
#endif
}

} // namespace crane
