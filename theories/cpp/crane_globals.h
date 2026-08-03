// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.

// To maintain global variables that can be defined dynamically, we
// require a global map that can store values of any type.
// This is used for the translation of global state events to CPP.

#ifndef CRANE_GLOBALS_H_
#define CRANE_GLOBALS_H_

#include <any>
#include <cstdint>
#include <map>

inline std::map<uint64_t, std::any> _crane_globals;

#endif // CRANE_GLOBALS_H_
