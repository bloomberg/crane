#include "sigt_prod_fn_any_lit.h"

Inst::sem my_arg(std::monostate) { return UINT64_C(0); }

/// In Rocq this is true (predicate 0 =? 0), and the extracted C++ now
/// agrees.
bool check(std::monostate) { return M::run(my_entry, my_arg); }
