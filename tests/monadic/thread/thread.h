#ifndef INCLUDED_THREAD
#define INCLUDED_THREAD

#include <chrono>
#include <cstdint>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <thread>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct threadtest {
  static void fun1(const unsigned int &n);
  static void fun2(const unsigned int &n);
  static void test(const unsigned int &m, unsigned int n);
  static void test_pure(const unsigned int &m, const unsigned int &n);
};

#endif // INCLUDED_THREAD
