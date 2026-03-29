#include <record_apply.h>

#include <functional>
#include <memory>
#include <type_traits>

__attribute__((pure)) unsigned int
RecordApply::apply_record(const std::shared_ptr<RecordApply::R> &r0,
                          const unsigned int a, const unsigned int b) {
  return r0->f(a, b);
}
