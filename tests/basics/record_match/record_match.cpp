#include "record_match.h"

uint64_t RecordMatch::sum(const RecordMatch::MyRec &r) {
  uint64_t n1 = r.f1;
  uint64_t n2 = r.f2;
  uint64_t n3 = r.f3;
  return ((n1 + n2) + n3);
}
