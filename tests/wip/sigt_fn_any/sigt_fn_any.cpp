#include "sigt_fn_any.h"

Inst::sem my_arg(std::monostate) { return UINT64_C(0); }

/// In Rocq this evaluates to true ((fun n => n =? 0) 0). In C++ the extracted
/// code throws std::bad_any_cast when called. Kept as a function (not a value)
/// so the C++ test driver can invoke it under try/catch rather than crashing at
/// static-initialization time.
bool check(std::monostate) { return M::run(my_entry, my_arg); }
