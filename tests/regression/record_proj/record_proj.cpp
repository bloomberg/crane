#include "record_proj.h"

uint64_t RecordProj::weird_access(const RecordProj::Point &p) {
  uint64_t a = p.x;
  uint64_t b = p.y;
  uint64_t sum = (a + b);
  return (sum + a);
}

uint64_t RecordProj::complex_access(const RecordProj::ComplexRecord &c) {
  uint64_t f1 = c.field1;
  uint64_t f2 = c.field2;
  uint64_t f3 = c.field3;
  return ((f1 + f2) + f3);
}

uint64_t RecordProj::nested_record_match(const RecordProj::Point &p1,
                                         const RecordProj::Point &p2) {
  uint64_t x1 = p1.x;
  uint64_t y1 = p1.y;
  uint64_t x2 = p2.x;
  uint64_t y2 = p2.y;
  return (((x1 + y1) + x2) + y2);
}
