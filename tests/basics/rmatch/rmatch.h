#include <algorithm>
#include <any>
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

struct RMatch {
  struct MyRec {
    unsigned int f1;
    unsigned int f2;
    unsigned int f3;
  };

  static unsigned int f1(const std::shared_ptr<MyRec> &m);

  static unsigned int f2(const std::shared_ptr<MyRec> &m);

  static unsigned int f3(const std::shared_ptr<MyRec> &m);

  static unsigned int sum(const std::shared_ptr<MyRec> &r);
};
