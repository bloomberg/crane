#ifndef INCLUDED_THREAD
#define INCLUDED_THREAD

#include <algorithm>
#include <any>
#include <cassert>
#include <chrono>
#include <cstdint>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <thread>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct threadtest {
  __attribute__((pure)) static void fun1(const unsigned int n);
  __attribute__((pure)) static void fun2(const unsigned int n);
  __attribute__((pure)) static void test(const unsigned int m,
                                         const unsigned int n);
  static void test2(const unsigned int m, const unsigned int n);
};

#endif // INCLUDED_THREAD
