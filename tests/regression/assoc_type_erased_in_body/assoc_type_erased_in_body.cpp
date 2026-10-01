#include "assoc_type_erased_in_body.h"

Nat AssocTypeErasedInBody::go(const Nat &) { return PointerV<IPZ>::ptr_tag(); }
