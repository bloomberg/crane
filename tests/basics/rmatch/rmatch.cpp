#include <algorithm>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <rmatch.h>
#include <string>
#include <utility>
#include <variant>

unsigned int RMatch::f1(const std::shared_ptr<RMatch::MyRec> &m) {
  return m->f1;
}

unsigned int RMatch::f2(const std::shared_ptr<RMatch::MyRec> &m) {
  return m->f2;
}

unsigned int RMatch::f3(const std::shared_ptr<RMatch::MyRec> &m) {
  return m->f3;
}

unsigned int RMatch::sum(const std::shared_ptr<RMatch::MyRec> &r) {
  return [&](void) {
    unsigned int n1 = r->f1;
    unsigned int n2 = r->f2;
    unsigned int n3 = r->f3;
    return ((n1 + n2) + n3);
  }();
}
