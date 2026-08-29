#include "qualified_record_shadow.h"

QualifiedRecordShadow::Shadow
QualifiedRecordShadow::bump(const QualifiedRecordShadow::Shadow &x) {
  uint64_t n = x.value;
  return Shadow{(n + 1)};
}
