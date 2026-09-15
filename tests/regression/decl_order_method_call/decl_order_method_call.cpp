#include "decl_order_method_call.h"

std::optional<List<Rv>> Regs::write_r(const List<Rv> &x0_, uint64_t x1_,
                                      const Rv &x2_) {
  return Regs::template replace_nth<Rv>(x0_, x1_, x2_);
}
