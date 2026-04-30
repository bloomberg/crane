#include <pathological_record.h>

unsigned int PathologicalRecord::hof_access(const PathologicalRecord::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return ((a + b) + c);
}

unsigned int PathologicalRecord::nested_lets(const PathologicalRecord::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return ((a + b) + c);
}

unsigned int
PathologicalRecord::conditional_access(const PathologicalRecord::Rec &r,
                                       const bool &flag) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  if (flag) {
    return (a + b);
  } else {
    return (b + c);
  }
}

unsigned int PathologicalRecord::countdown(const unsigned int &n,
                                           const PathologicalRecord::Rec &r) {
  if (n <= 0) {
    return r.f1;
  } else {
    unsigned int n_ = n - 1;
    std::any _x = r.f1;
    unsigned int b = r.f2;
    std::any _x0 = r.f3;
    return (countdown(n_, r) + b);
  }
}

unsigned int
PathologicalRecord::double_match(const PathologicalRecord::Rec &r1,
                                 const PathologicalRecord::Rec &r2) {
  unsigned int a1 = r1.f1;
  unsigned int b1 = r1.f2;
  unsigned int c1 = r1.f3;
  unsigned int a2 = r2.f1;
  unsigned int b2 = r2.f2;
  unsigned int c2 = r2.f3;
  unsigned int x = (a1 + a2);
  unsigned int y = (b1 + b2);
  unsigned int z = (c1 + c2);
  return ((x + y) * z);
}

unsigned int
PathologicalRecord::closure_over_fields(const PathologicalRecord::Rec &r,
                                        const unsigned int &x) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  return (((x + a) + b) + c);
}

unsigned int
PathologicalRecord::guarded_pattern(const PathologicalRecord::Rec &r) {
  unsigned int a = r.f1;
  unsigned int b = r.f2;
  unsigned int c = r.f3;
  if (a == 0u) {
    return (b + c);
  } else {
    if (b == 0u) {
      return (a + c);
    } else {
      return (a + b);
    }
  }
}

unsigned int
PathologicalRecord::scrambled_access(const PathologicalRecord::BigRec &r) {
  unsigned int a = r.bf1;
  unsigned int b = r.bf2;
  unsigned int c = r.bf3;
  unsigned int d = r.bf4;
  unsigned int e = r.bf5;
  return ((((e + d) + c) + b) + a);
}

unsigned int
PathologicalRecord::repeated_access(const PathologicalRecord::BigRec &r) {
  unsigned int a = r.bf1;
  unsigned int b = r.bf2;
  unsigned int c = r.bf3;
  unsigned int d = r.bf4;
  unsigned int e = r.bf5;
  return (((((((((a + a) + b) + b) + c) + c) + d) + d) + e) + e);
}
