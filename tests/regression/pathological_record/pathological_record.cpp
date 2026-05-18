#include "pathological_record.h"

uint64_t PathologicalRecord::hof_access(const PathologicalRecord::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return ((a + b) + c);
}

uint64_t PathologicalRecord::nested_lets(const PathologicalRecord::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return ((a + b) + c);
}

uint64_t
PathologicalRecord::conditional_access(const PathologicalRecord::Rec &r,
                                       bool flag) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  if (flag) {
    return (a + b);
  } else {
    return (b + c);
  }
}

uint64_t PathologicalRecord::countdown(uint64_t n,
                                       const PathologicalRecord::Rec &r) {
  if (n <= 0) {
    return r.f1;
  } else {
    uint64_t n_ = n - 1;
    std::any _x = r.f1;
    uint64_t b = r.f2;
    std::any _x0 = r.f3;
    return (countdown(n_, r) + b);
  }
}

uint64_t PathologicalRecord::double_match(const PathologicalRecord::Rec &r1,
                                          const PathologicalRecord::Rec &r2) {
  uint64_t a1 = r1.f1;
  uint64_t b1 = r1.f2;
  uint64_t c1 = r1.f3;
  uint64_t a2 = r2.f1;
  uint64_t b2 = r2.f2;
  uint64_t c2 = r2.f3;
  uint64_t x = (a1 + a2);
  uint64_t y = (b1 + b2);
  uint64_t z = (c1 + c2);
  return ((x + y) * z);
}

uint64_t
PathologicalRecord::closure_over_fields(const PathologicalRecord::Rec &r,
                                        uint64_t x) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  return (((x + a) + b) + c);
}

uint64_t PathologicalRecord::guarded_pattern(const PathologicalRecord::Rec &r) {
  uint64_t a = r.f1;
  uint64_t b = r.f2;
  uint64_t c = r.f3;
  if (a == UINT64_C(0)) {
    return (b + c);
  } else {
    if (b == UINT64_C(0)) {
      return (a + c);
    } else {
      return (a + b);
    }
  }
}

uint64_t
PathologicalRecord::scrambled_access(const PathologicalRecord::BigRec &r) {
  uint64_t a = r.bf1;
  uint64_t b = r.bf2;
  uint64_t c = r.bf3;
  uint64_t d = r.bf4;
  uint64_t e = r.bf5;
  return ((((e + d) + c) + b) + a);
}

uint64_t
PathologicalRecord::repeated_access(const PathologicalRecord::BigRec &r) {
  uint64_t a = r.bf1;
  uint64_t b = r.bf2;
  uint64_t c = r.bf3;
  uint64_t d = r.bf4;
  uint64_t e = r.bf5;
  return (((((((((a + a) + b) + b) + c) + c) + d) + d) + e) + e);
}
