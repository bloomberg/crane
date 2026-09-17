#include "lifted_instance_qualified.h"

String LiftedInstanceQualified::use(const Nat &n) {
  return Other::banner.append(StringUtil::banner0.append(::showN::show(n)));
}
