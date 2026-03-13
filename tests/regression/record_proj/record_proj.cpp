#include <record_proj.h>

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
RecordProj::weird_access(const std::shared_ptr<RecordProj::Point> &p) {
  return [&](void) {
    unsigned int a = p->x;
    unsigned int b = p->y;
    unsigned int sum = (a + b);
    return (std::move(sum) + a);
  }();
}

__attribute__((pure)) unsigned int RecordProj::complex_access(
    const std::shared_ptr<RecordProj::ComplexRecord> &c) {
  return [&](void) {
    unsigned int f1 = c->field1;
    unsigned int f2 = c->field2;
    unsigned int f3 = c->field3;
    return ((f1 + f2) + f3);
  }();
}

__attribute__((pure)) unsigned int
RecordProj::nested_record_match(const std::shared_ptr<RecordProj::Point> &p1,
                                const std::shared_ptr<RecordProj::Point> &p2) {
  return [&](void) {
    unsigned int x1 = p1->x;
    unsigned int y1 = p1->y;
    return [&](void) {
      unsigned int x2 = p2->x;
      unsigned int y2 = p2->y;
      return (((x1 + y1) + x2) + y2);
    }();
  }();
}
