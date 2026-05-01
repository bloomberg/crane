#include <qualified_record_shadow.h>

QualifiedRecordShadow::Shadow
QualifiedRecordShadow::bump(const QualifiedRecordShadow::Shadow &x) {
  unsigned int n = x.Shadow::value;
  return Shadow{(n + 1)};
}
