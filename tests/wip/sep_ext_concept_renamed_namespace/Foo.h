#ifndef INCLUDED_FOO
#define INCLUDED_FOO

#include <concepts>

#include "Datatypes.h"

namespace Foo_ {

template <typename I>
concept Foo = requires {
  { I::foo_val() } -> std::convertible_to<Datatypes::Nat>;
};

} // namespace Foo_

#endif // INCLUDED_FOO
