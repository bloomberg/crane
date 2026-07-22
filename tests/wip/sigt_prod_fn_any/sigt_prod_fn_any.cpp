#include "sigt_prod_fn_any.h"

Inst::sem my_arg(std::monostate) { return UINT64_C(0); }

/// In Rocq this is true (predicate 0 =? 0 holds). The extracted C++ throws
/// std::bad_any_cast instead.
bool check(std::monostate) { return M::run(my_entry, my_arg); }
