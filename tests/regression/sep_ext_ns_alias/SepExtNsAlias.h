#ifndef INCLUDED_SEPEXTNSALIAS
#define INCLUDED_SEPEXTNSALIAS

#include "Datatypes.h"

namespace SepExtNsAlias {

struct Foo {
  static const Datatypes::Nat &x() {
    static const Datatypes::Nat v = Datatypes::Nat::o();
    return v;
  }
};

using FooAlias = Foo;

} // namespace SepExtNsAlias

#endif // INCLUDED_SEPEXTNSALIAS
