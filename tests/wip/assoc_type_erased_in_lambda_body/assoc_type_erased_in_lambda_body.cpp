#include "assoc_type_erased_in_lambda_body.h"

Nat AssocTypeErasedInLambdaBody::go(const Nat &) {
  return PointerV<IPZ>::ptr_tag();
}
