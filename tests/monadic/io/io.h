#include <any>
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
  struct unit {
  public:
    struct tt {};
    using variant_t = std::variant<tt>;

  private:
    variant_t v_;
    explicit unit(tt _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Unit::unit> tt_() {
        return std::shared_ptr<Unit::unit>(new Unit::unit(tt{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct iotest {
  static void test1(const std::string _x);

  static std::shared_ptr<Unit::unit> test2(const std::string s);

  static void test3(const std::string s);

  static std::string test4();

  static void test5();
};
