#include "sigt_fn_any.h"

Inst::sem my_arg(std::monostate) { return UINT64_C(0); }

bool check(std::monostate) { return M::run(my_entry, my_arg); }
