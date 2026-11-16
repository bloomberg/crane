#include "sigt_prod_fn_any_lit_pair.h"

Inst::sem my_arg(std::monostate) { return true; }

bool check() { return M::run(my_entry, my_arg); }
