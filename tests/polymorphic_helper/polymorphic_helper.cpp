#include "polymorphic_helper.h"

Nat foo(Nat n, bool b) { return _foo_aux(std::move(n), n).add(_foo_aux(b, n)); }
