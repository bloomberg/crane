#include <qualified_record_shadow.h>

#include <memory>
#include <type_traits>

std::shared_ptr<QualifiedRecordShadow::Shadow> QualifiedRecordShadow::bump(
    const std::shared_ptr<QualifiedRecordShadow::Shadow> &x) {
  unsigned int n = x->Shadow::value;
  return std::make_shared<QualifiedRecordShadow::Shadow>(Shadow{(n + 1)});
}
