#include <erased_record.h>

__attribute__((pure)) unsigned int
ErasedRecord::complex_match(const ErasedRecord::ManyProps &r) {
  unsigned int f0 = r.field0;
  unsigned int f1 = r.field1;
  unsigned int f2 = r.field2;
  unsigned int f3 = r.field3;
  unsigned int f4 = r.field4;
  return ((((f0 + f1) + f2) + f3) + f4);
}

__attribute__((pure)) unsigned int
ErasedRecord::unusual_body(const ErasedRecord::ManyProps &r) {
  unsigned int f0 = r.field0;
  unsigned int f1 = r.field1;
  unsigned int f2 = r.field2;
  unsigned int f3 = r.field3;
  unsigned int f4 = r.field4;
  return ((((f0 + f1) + f2) + f3) + f4);
}

__attribute__((pure)) unsigned int
ErasedRecord::access_mostly_props(const ErasedRecord::MostlyProps &r) {
  unsigned int r1 = r.real1;
  unsigned int r2 = r.real2;
  unsigned int r3 = r.real3;
  return ((r1 + r2) + r3);
}
