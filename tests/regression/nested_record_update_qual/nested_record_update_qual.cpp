#include <nested_record_update_qual.h>

#include <memory>
#include <type_traits>

std::shared_ptr<NestedRecordUpdateQual::Shadow> NestedRecordUpdateQual::bump(
    const std::shared_ptr<NestedRecordUpdateQual::Shadow> &x) {
  unsigned int n = x->Shadow::value;
  return std::make_shared<NestedRecordUpdateQual::Shadow>(Shadow{(n + 1)});
}
