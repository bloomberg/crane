#include "cross_file_module_ref.h"

Nat bump0(Nat n) { return Nat::s(std::move(n)); }

Nat Lib2::bump(Nat n) { return Nat::s(Nat::s(std::move(n))); }
