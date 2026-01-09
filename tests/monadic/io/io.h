#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Unit {
  struct tt;
  using unit = std::variant<tt>;
  struct tt {
    static std::shared_ptr<unit> make();
  };
};

struct iotest {
  static void test1(const std::string _x);

  static std::shared_ptr<typename Unit::unit> test2(const std::string s);

  static void test3(const std::string s);

  static std::string test4();

  static void test5();
};
