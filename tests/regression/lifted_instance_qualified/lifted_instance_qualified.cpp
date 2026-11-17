#include "lifted_instance_qualified.h"

String LiftedInstanceQualified::use(const Nat &n) {
  return Other::banner0.append(StringUtil::banner.append(::showN::show(n)));
}
