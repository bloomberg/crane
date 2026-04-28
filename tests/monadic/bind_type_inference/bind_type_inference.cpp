#include <bind_type_inference.h>

int64_t BindTypeInference::test1() {
  return ignoreAndReturn<int64_t>(int64_t(42));
}

int64_t BindTypeInference::test2() {
  return transform<std::monostate, int64_t>(
      std::monostate{}, [](const std::monostate &) { return int64_t(42); });
}

int64_t BindTypeInference::test3() {
  return nested<std::monostate, bool, int64_t>(
      std::monostate{}, [](const std::monostate &) { return true; },
      [](const bool &b) {
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

__attribute__((pure)) List<int64_t>
BindTypeInference::intToList(const int64_t n) {
  return List<int64_t>::cons(n, List<int64_t>::nil());
}

List<int64_t> BindTypeInference::test5() {
  int64_t x = int64_t(1);
  return intToList(x);
}

int64_t BindTypeInference::test6() {
  bool y = true;
  return (y ? int64_t(42) : int64_t(0));
}
