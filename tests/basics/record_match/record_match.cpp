#include <record_match.h>

unsigned int RecordMatch::sum(const RecordMatch::MyRec &r) {
  unsigned int n1 = r.f1;
  unsigned int n2 = r.f2;
  unsigned int n3 = r.f3;
  return ((n1 + n2) + n3);
}
