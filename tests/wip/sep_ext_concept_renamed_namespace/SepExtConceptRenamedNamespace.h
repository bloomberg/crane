#ifndef INCLUDED_SEPEXTCONCEPTRENAMEDNAMESPACE
#define INCLUDED_SEPEXTCONCEPTRENAMEDNAMESPACE

#include "Datatypes.h"
#include "Foo.h"

namespace SepExtConceptRenamedNamespace {

template <Foo::Foo _tcI0> Datatypes::Nat use_it() { return _tcI0::foo_val(); }

} // namespace SepExtConceptRenamedNamespace

#endif // INCLUDED_SEPEXTCONCEPTRENAMEDNAMESPACE
