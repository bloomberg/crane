#include <nested_record_update_qual.h>

NestedRecordUpdateQual::Shadow
NestedRecordUpdateQual::bump(const NestedRecordUpdateQual::Shadow &x) {
  unsigned int n = x.Shadow::value;
  return Shadow{(n + 1)};
}
