#include <stream.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<Stream::stream<std::shared_ptr<Nat>>>
Stream::nats_from(std::shared_ptr<Nat> n) {
  return stream<std::shared_ptr<Nat>>::ctor::lazy_(
      [=](void) mutable
          -> std::shared_ptr<Stream::stream<std::shared_ptr<Nat>>> {
        return stream<std::shared_ptr<Nat>>::ctor::scons_(
            n, nats_from(Nat::ctor::S_(n)));
      });
}
