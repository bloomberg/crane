#include "nested_record_update_qual.h"

NestedRecordUpdateQual::Shadow
NestedRecordUpdateQual::bump(const NestedRecordUpdateQual::Shadow &x) {
  uint64_t n = x.value;
  return Shadow{(n + 1)};
}
