#ifndef INCLUDED_MAIN_TOPLEVEL
#define INCLUDED_MAIN_TOPLEVEL

#include <filesystem>
#include <fstream>
#include <iostream>
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

struct Greeter {
  static void greet();
};

int main();

#endif // INCLUDED_MAIN_TOPLEVEL
