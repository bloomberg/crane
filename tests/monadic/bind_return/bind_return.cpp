#include <any>
#include <bind_return.h>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>
#include <vector>

int bindreturn::test1() { return ignoreAndReturn<int>(42); }

int bindreturn::test2() {
  return transform<std::shared_ptr<Unit::unit>, int>(
      Unit::unit::ctor::tt_(),
      [](std::shared_ptr<Unit::unit> _x) { return 42; });
}

int bindreturn::test3() {
  return nested<std::shared_ptr<Unit::unit>, bool, int>(
      Unit::unit::ctor::tt_(),
      [](std::shared_ptr<Unit::unit> _x) { return true; },
      [](bool b) {
        if (b) {
          return 1;
        } else {
          return 0;
        }
      });
}

int bindreturn::test4() {
  std::vector<int> v = {};
  v.push_back(1);
  v.push_back(2);
  v.push_back(3);
  return v.size();
}

std::shared_ptr<List::list<int>> bindreturn::intToList(const int n) {
  return List::list<int>::ctor::cons_(n, List::list<int>::ctor::nil_());
}

std::shared_ptr<List::list<int>> bindreturn::test5() {
  int x = 1;
  return intToList(x);
}

int bindreturn::test6() {
  std::shared_ptr<Unit::unit> _x = Unit::unit::ctor::tt_();
  bool y = true;
  return [&](void) {
    if (y) {
      return 42;
    } else {
      return 0;
    }
  }();
}
