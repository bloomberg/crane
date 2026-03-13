#ifndef INCLUDED_IO
#define INCLUDED_IO

#include <algorithm>
#include <any>
#include <cassert>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Unit { e_TT };

struct iotest {
  static void test1(const std::string _x);
  __attribute__((pure)) static Unit test2(const std::string s);
  __attribute__((pure)) static void test3(const std::string s);
  __attribute__((pure)) static std::string test4();
  __attribute__((pure)) static void test5();
};

#endif // INCLUDED_IO
