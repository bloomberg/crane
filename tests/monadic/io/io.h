#ifndef INCLUDED_IO
#define INCLUDED_IO

#include <fstream>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct iotest {
  static void test1(const std::string _x);
  static void test2(const std::string s);
  static void test3(const std::string s);
  static std::string test4();
  static void test5();
};

#endif // INCLUDED_IO
