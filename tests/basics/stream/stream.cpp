#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <stream.h>
#include <string>
#include <variant>

std::shared_ptr<Stream::stream<std::shared_ptr<Nat::nat>>>
Stream::nats_from(std::shared_ptr<Nat::nat> n) {
  return stream<std::shared_ptr<Nat::nat>>::ctor::lazy_(
      [=](void) -> std::shared_ptr<Stream::stream<std::shared_ptr<Nat::nat>>> {
        return stream<std::shared_ptr<Nat::nat>>::ctor::scons_(
            n, nats_from(Nat::nat::ctor::S_(n)));
      });
}
