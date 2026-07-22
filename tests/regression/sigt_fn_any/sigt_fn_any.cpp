#include "sigt_fn_any.h"

Inst::sem my_arg(std::monostate) { return UINT64_C(0); }

/// In Rocq this evaluates to true ((fun n => n =? 0) 0), and the extracted
/// C++ now returns true as well.  Kept as a function (not a value) so the C++
/// test driver can invoke it under try/catch (before the fix it threw
/// std::bad_any_cast).
bool check(std::monostate) { return M::run(my_entry, my_arg); }
