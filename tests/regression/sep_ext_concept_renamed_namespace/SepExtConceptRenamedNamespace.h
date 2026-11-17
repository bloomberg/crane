#pragma once

#include "Datatypes.h"
#include "Foo.h"

namespace SepExtConceptRenamedNamespace {
template <Foo_::Foo _tcI0> Datatypes::Nat use_it() { return _tcI0::foo_val(); }
} // namespace SepExtConceptRenamedNamespace
