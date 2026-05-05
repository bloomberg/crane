#ifndef INCLUDED_SEPEXTNSALIAS
#define INCLUDED_SEPEXTNSALIAS

#include <memory>
#include <optional>
#include <type_traits>

#include "Datatypes.h"

namespace SepExtNsAlias {

struct Foo {
  static inline const Datatypes::Nat x = Datatypes::Nat::o();
};

using FooAlias = Foo;

} // namespace SepExtNsAlias

#endif // INCLUDED_SEPEXTNSALIAS
