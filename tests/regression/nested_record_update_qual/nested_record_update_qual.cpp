#include <nested_record_update_qual.h>

#include <memory>
#include <optional>
#include <type_traits>

__attribute__((pure)) NestedRecordUpdateQual::Shadow
NestedRecordUpdateQual::bump(const NestedRecordUpdateQual::Shadow &x) {
  unsigned int n = x.Shadow::value;
  return Shadow{(n + 1)};
}
