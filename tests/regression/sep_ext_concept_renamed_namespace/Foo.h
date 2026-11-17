#pragma once

#include <concepts>

#include "Datatypes.h"

namespace Foo_ {
template <typename I>
concept Foo = requires {
  { I::foo_val() } -> std::convertible_to<Datatypes::Nat>;
};
} // namespace Foo_
