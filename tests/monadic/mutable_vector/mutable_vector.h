#ifndef INCLUDED_MUTABLE_VECTOR
#define INCLUDED_MUTABLE_VECTOR

#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <variant>
#include <vector>

struct MutableVectorTest {
  static int64_t test1(const int64_t _x);
  static std::vector<int64_t> test2(const int64_t _x);
};

#endif // INCLUDED_MUTABLE_VECTOR
