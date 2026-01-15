#include <algorithm>
#include <chrono>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <thread>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct threadtest {
  static void fun1(const unsigned int n);

  static void fun2(const unsigned int n);

  static void test(const unsigned int m, const unsigned int n);

  static void test2(const unsigned int m, const unsigned int n);
};
