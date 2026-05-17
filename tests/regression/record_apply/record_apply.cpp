#include "record_apply.h"

unsigned int RecordApply::apply_record(const RecordApply::R &r0, unsigned int a,
                                       unsigned int b) {
  return r0.f(a, b);
}
