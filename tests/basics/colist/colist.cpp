#include <colist.h>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <variant>

std::shared_ptr<Colist::colist<std::shared_ptr<Nat::nat>>>
Colist::nats(const std::shared_ptr<Nat::nat> &n) {
  return colist<std::shared_ptr<Nat::nat>>::ctor::cocons_(
      n, nats(Nat::nat::ctor::S_(n)));
}
