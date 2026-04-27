#include <record_proj.h>

__attribute__((pure)) unsigned int
RecordProj::weird_access(const RecordProj::Point &p) {
  unsigned int a = p.x;
  unsigned int b = p.y;
  unsigned int sum = (a + b);
  return (sum + a);
}

__attribute__((pure)) unsigned int
RecordProj::complex_access(const RecordProj::ComplexRecord &c) {
  unsigned int f1 = c.field1;
  unsigned int f2 = c.field2;
  unsigned int f3 = c.field3;
  return ((f1 + f2) + f3);
}

__attribute__((pure)) unsigned int
RecordProj::nested_record_match(const RecordProj::Point &p1,
                                const RecordProj::Point &p2) {
  unsigned int x1 = p1.x;
  unsigned int y1 = p1.y;
  unsigned int x2 = p2.x;
  unsigned int y2 = p2.y;
  return (((x1 + y1) + x2) + y2);
}
