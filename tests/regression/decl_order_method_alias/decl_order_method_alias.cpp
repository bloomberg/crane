#include "decl_order_method_alias.h"

std::optional<rfile> RegFile::write_r(rfile x0_, uint64_t x1_, const Rv &x2_) {
  return RegFile::template replace_nth<Rv>(x0_, x1_, x2_);
}
