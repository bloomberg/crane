#include "cross_file_module_ref.h"

Nat bump(const Nat &n) { return Nat::s(n); }

Nat Lib2::bump0(const Nat &n) { return Nat::s(Nat::s(n)); }
