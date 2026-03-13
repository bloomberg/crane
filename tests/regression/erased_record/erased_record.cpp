#include <erased_record.h>

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

__attribute__((pure)) unsigned int
ErasedRecord::complex_match(const std::shared_ptr<ErasedRecord::ManyProps> &r) {
  return [&](void) {
    unsigned int f0 = r->field0;
    unsigned int f1 = r->field1;
    unsigned int f2 = r->field2;
    unsigned int f3 = r->field3;
    unsigned int f4 = r->field4;
    return ((((f0 + f1) + f2) + f3) + f4);
  }();
}

__attribute__((pure)) unsigned int
ErasedRecord::unusual_body(const std::shared_ptr<ErasedRecord::ManyProps> &r) {
  return [&](void) {
    unsigned int f0 = r->field0;
    unsigned int f1 = r->field1;
    unsigned int f2 = r->field2;
    unsigned int f3 = r->field3;
    unsigned int f4 = r->field4;
    return ((((f0 + f1) + f2) + f3) + f4);
  }();
}

__attribute__((pure)) unsigned int ErasedRecord::access_mostly_props(
    const std::shared_ptr<ErasedRecord::MostlyProps> &r) {
  return [&](void) {
    unsigned int r1 = r->real1;
    unsigned int r2 = r->real2;
    unsigned int r3 = r->real3;
    return ((r1 + r2) + r3);
  }();
}
