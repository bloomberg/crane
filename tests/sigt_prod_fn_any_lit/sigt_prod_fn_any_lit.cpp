#include "sigt_prod_fn_any_lit.h"

Inst::sem my_arg(std::monostate) { return UINT64_C(0); }

bool check(std::monostate) { return M::run(my_entry, my_arg); }
