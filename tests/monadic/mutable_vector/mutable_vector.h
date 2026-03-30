#ifndef INCLUDED_MUTABLE_VECTOR
#define INCLUDED_MUTABLE_VECTOR

#include <cstdint>
#include <type_traits>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct MutableVectorTest {
  static int64_t test1(const int64_t _x);
  static std::vector<int64_t> test2(const int64_t _x);
};

#endif // INCLUDED_MUTABLE_VECTOR
