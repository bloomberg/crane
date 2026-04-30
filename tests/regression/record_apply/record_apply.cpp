#include <record_apply.h>

unsigned int RecordApply::apply_record(const RecordApply::R &r0,
                                       const unsigned int &a,
                                       const unsigned int &b) {
  return r0.f(a, b);
}
