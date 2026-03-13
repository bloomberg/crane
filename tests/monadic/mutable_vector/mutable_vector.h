#ifndef INCLUDED_MUTABLE_VECTOR
#define INCLUDED_MUTABLE_VECTOR

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct MutableVectorTest {
  __attribute__((pure)) static int64_t test1(const int64_t _x);
  __attribute__((pure)) static std::vector<int64_t> test2(const int64_t _x);
};

#endif // INCLUDED_MUTABLE_VECTOR
