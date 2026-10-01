#include "decl_order_forward_use.h"

Nat::nat DeclOrderForwardUse::d(const Nat::nat &x0_, const Nat::nat &x1_) {
  return x0_.div(x1_);
}

Prod<Nat::nat, Nat::nat> Nat::divmod(const Nat::nat &x, const Nat::nat &y,
                                     const Nat::nat &q, const Nat::nat &u) {
  if (std::holds_alternative<typename Nat::nat::O>(x.v())) {
    return Prod<Nat::nat, Nat::nat>::pair(q, u);
  } else {
    const auto &[a0] = std::get<typename Nat::nat::S>(x.v());
    if (std::holds_alternative<typename Nat::nat::O>(u.v())) {
      return Nat::divmod(*a0, y, Nat::nat::s(q), y);
    } else {
      const auto &[a00] = std::get<typename Nat::nat::S>(u.v());
      return Nat::divmod(*a0, y, q, *a00);
    }
  }
}
