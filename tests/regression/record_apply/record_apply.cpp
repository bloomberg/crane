#include <record_apply.h>

#include <functional>
#include <type_traits>

__attribute__((pure)) unsigned int
RecordApply::apply_record(const RecordApply::R &r0, const unsigned int &a,
                          const unsigned int &b) {
  return r0.f(a, b);
}
