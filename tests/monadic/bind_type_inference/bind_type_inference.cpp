#include <bind_type_inference.h>

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

int64_t BindTypeInference::test1() {
  return ignoreAndReturn<int64_t>(int64_t(42));
}

int64_t BindTypeInference::test2() {
  return transform<Unit, int64_t>(Unit::e_TT,
                                  [](Unit _x) { return int64_t(42); });
}

int64_t BindTypeInference::test3() {
  return nested<Unit, bool, int64_t>(
      Unit::e_TT, [](Unit _x) { return true; },
      [](bool b) {
        if (b) {
          return int64_t(1);
        } else {
          return int64_t(0);
        }
      });
}

int64_t BindTypeInference::test4() {
  std::vector<int64_t> v = {};
  v.push_back(int64_t(1));
  v.push_back(int64_t(2));
  v.push_back(int64_t(3));
  return v.size();
}

std::shared_ptr<List<int64_t>> BindTypeInference::intToList(const int64_t n) {
  return List<int64_t>::cons(n, List<int64_t>::nil());
}

std::shared_ptr<List<int64_t>> BindTypeInference::test5() {
  int64_t x = int64_t(1);
  return intToList(x);
}

int64_t BindTypeInference::test6() {
  Unit _x = Unit::e_TT;
  bool y = true;
  return [&](void) {
    if (y) {
      return int64_t(42);
    } else {
      return int64_t(0);
    }
  }();
}
