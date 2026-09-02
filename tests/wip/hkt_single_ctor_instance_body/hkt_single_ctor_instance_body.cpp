#include "hkt_single_ctor_instance_body.h"

HktSingleCtorInstanceBody::box<Nat>
HktSingleCtorInstanceBody::run(const Nat &n) {
  return liftme<HktSingleCtorInstanceBody::PB, HktSingleCtorInstanceBody::FB>(
      n);
}
