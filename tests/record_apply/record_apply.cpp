#include "record_apply.h"

uint64_t RecordApply::apply_record(const RecordApply::R &r0, uint64_t a,
                                   uint64_t b) {
  return r0.f(a, b);
}
