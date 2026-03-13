#ifndef INCLUDED_PARALLEL
#define INCLUDED_PARALLEL

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <functional>
#include <future>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  static inline const unsigned int one = 1u;
};

struct ParallelTest {
  __attribute__((pure)) static unsigned int
  ack(const std::pair<unsigned int, unsigned int> p);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  fast(const unsigned int m, const unsigned int n);
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  slow(const unsigned int m, const unsigned int n);
};

#endif // INCLUDED_PARALLEL
