#include <pathological_record.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int PathologicalRecord::hof_access(
    const std::shared_ptr<PathologicalRecord::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return ((a + b) + c);
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::nested_lets(
    const std::shared_ptr<PathologicalRecord::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return ((a + b) + c);
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::conditional_access(
    const std::shared_ptr<PathologicalRecord::Rec> &r, const bool flag) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    if (flag) {
      return (a + b);
    } else {
      return (b + c);
    }
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::countdown(
    const unsigned int n, const std::shared_ptr<PathologicalRecord::Rec> &r) {
  if (n <= 0) {
    return r->f1;
  } else {
    unsigned int n_ = n - 1;
    return [&](void) {
      std::any _x = r->f1;
      unsigned int b = r->f2;
      std::any _x0 = r->f3;
      return (countdown(n_, r) + b);
    }();
  }
}

__attribute__((pure)) unsigned int PathologicalRecord::double_match(
    const std::shared_ptr<PathologicalRecord::Rec> &r1,
    const std::shared_ptr<PathologicalRecord::Rec> &r2) {
  return [&](void) {
    unsigned int a1 = r1->f1;
    unsigned int b1 = r1->f2;
    unsigned int c1 = r1->f3;
    return [&](void) {
      unsigned int a2 = r2->f1;
      unsigned int b2 = r2->f2;
      unsigned int c2 = r2->f3;
      unsigned int x = (a1 + a2);
      unsigned int y = (b1 + b2);
      unsigned int z = (c1 + c2);
      return ((std::move(x) + std::move(y)) * std::move(z));
    }();
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::closure_over_fields(
    const std::shared_ptr<PathologicalRecord::Rec> &r, const unsigned int x) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    return (((x + a) + b) + c);
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::guarded_pattern(
    const std::shared_ptr<PathologicalRecord::Rec> &r) {
  return [&](void) {
    unsigned int a = r->f1;
    unsigned int b = r->f2;
    unsigned int c = r->f3;
    if (a == 0u) {
      return (b + c);
    } else {
      if (b == 0u) {
        return (a + c);
      } else {
        return (a + b);
      }
    }
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::scrambled_access(
    const std::shared_ptr<PathologicalRecord::BigRec> &r) {
  return [&](void) {
    unsigned int a = r->bf1;
    unsigned int b = r->bf2;
    unsigned int c = r->bf3;
    unsigned int d = r->bf4;
    unsigned int e = r->bf5;
    return ((((e + d) + c) + b) + a);
  }();
}

__attribute__((pure)) unsigned int PathologicalRecord::repeated_access(
    const std::shared_ptr<PathologicalRecord::BigRec> &r) {
  return [&](void) {
    unsigned int a = r->bf1;
    unsigned int b = r->bf2;
    unsigned int c = r->bf3;
    unsigned int d = r->bf4;
    unsigned int e = r->bf5;
    return (((((((((a + a) + b) + b) + c) + c) + d) + d) + e) + e);
  }();
}
