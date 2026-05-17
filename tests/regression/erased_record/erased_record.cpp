#include "erased_record.h"

uint64_t ErasedRecord::complex_match(const ErasedRecord::ManyProps &r) {
  uint64_t f0 = r.field0;
  uint64_t f1 = r.field1;
  uint64_t f2 = r.field2;
  uint64_t f3 = r.field3;
  uint64_t f4 = r.field4;
  return ((((f0 + f1) + f2) + f3) + f4);
}

uint64_t ErasedRecord::unusual_body(const ErasedRecord::ManyProps &r) {
  uint64_t f0 = r.field0;
  uint64_t f1 = r.field1;
  uint64_t f2 = r.field2;
  uint64_t f3 = r.field3;
  uint64_t f4 = r.field4;
  return ((((f0 + f1) + f2) + f3) + f4);
}

uint64_t ErasedRecord::access_mostly_props(const ErasedRecord::MostlyProps &r) {
  uint64_t r1 = r.real1;
  uint64_t r2 = r.real2;
  uint64_t r3 = r.real3;
  return ((r1 + r2) + r3);
}
