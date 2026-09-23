#include "assoc_type_erased_in_body.h"

Nat AssocTypeErasedInBody::go(const Nat &) {
  return crane_any_cast<std::pair<iptr, prov>>(PointerV<IPZ>::null()).first;
}
