#include "mutable_vector.h"

int64_t MutableVectorTest::test1(int64_t) {
  std::vector<int64_t> v = {};
  v.push_back(INT64_C(3));
  v.push_back(INT64_C(2));
  v.push_back(INT64_C(7));
  int64_t x = v.size();
  v.pop_back();
  int64_t y = v.size();
  return static_cast<int64_t>(
      (static_cast<uint64_t>(x) - static_cast<uint64_t>(y)) &
      0x7FFFFFFFFFFFFFFFULL);
}

std::vector<int64_t> MutableVectorTest::test2(int64_t) {
  std::vector<int64_t> v = {};
  v.push_back(INT64_C(12));
  v.push_back(INT64_C(23));
  v.pop_back();
  v.push_back(INT64_C(3));
  int64_t x = v.size();
  v.push_back(x);
  int64_t y = v.at(INT64_C(2));
  v.push_back(INT64_C(98));
  v.push_back(y);
  return v;
}
