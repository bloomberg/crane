#include <algorithm>
#include <any>
#include <cassert>
#include <colist.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Colist::colist<std::shared_ptr<Nat::nat>>>
Colist::nats(std::shared_ptr<Nat::nat> n) {
  return colist<std::shared_ptr<Nat::nat>>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Colist::colist<std::shared_ptr<Nat::nat>>> {
        return colist<std::shared_ptr<Nat::nat>>::ctor::cocons_(
            n, nats(Nat::nat::ctor::S_(n)));
      });
}
