#include "decl_order_forward_use.h"

Nat::nat DeclOrderForwardUse::d(const Nat::nat &x0_, const Nat::nat &x1_) {
  return x0_.div(x1_);
}

Prod<Nat::nat, Nat::nat> Nat::divmod(const Nat::nat &x, const Nat::nat &y,
                                     Nat::nat q, Nat::nat u) {
  if (std::holds_alternative<typename Nat::nat::O>(x.v())) {
    return Prod<Nat::nat, Nat::nat>::pair(std::move(q), std::move(u));
  } else {
    const auto &[a0] = std::get<typename Nat::nat::S>(x.v());
    if (std::holds_alternative<typename Nat::nat::O>(u.v_mut())) {
      return Nat::divmod(*a0, y, Nat::nat::s(std::move(q)), y);
    } else {
      auto &[a00] = std::get<typename Nat::nat::S>(u.v_mut());
      return Nat::divmod(*a0, y, std::move(q), *a00);
    }
  }
}
