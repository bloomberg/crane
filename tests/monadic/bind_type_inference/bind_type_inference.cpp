#include "bind_type_inference.h"

int64_t BindTypeInference::test1() {
  return ignoreAndReturn<int64_t>(INT64_C(42));
}

int64_t BindTypeInference::test2() {
  return transform<std::monostate, int64_t>(
      std::monostate{}, [](std::monostate) { return INT64_C(42); });
}

int64_t BindTypeInference::test3() {
  return nested<std::monostate, bool, int64_t>(
      std::monostate{}, [](std::monostate) { return true; },
      [](bool b) {
        if (b) {
          return INT64_C(1);
        } else {
          return INT64_C(0);
        }
      });
}

int64_t BindTypeInference::test4() {
  std::vector<int64_t> v = {};
  v.push_back(INT64_C(1));
  v.push_back(INT64_C(2));
  v.push_back(INT64_C(3));
  return std::move(v).size();
}

List<int64_t> BindTypeInference::intToList(int64_t n) {
  return List<int64_t>::cons(n, List<int64_t>::nil());
}

List<int64_t> BindTypeInference::test5() {
  int64_t x = INT64_C(1);
  return intToList(x);
}

int64_t BindTypeInference::test6() {
  bool y = true;
  return (y ? INT64_C(42) : INT64_C(0));
}
