#ifndef INCLUDED_FREE_MONAD
#define INCLUDED_FREE_MONAD

#include "crane_fn.h"
#include <any>
#include <functional>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

enum class Unit { TT };

struct FreeMonad {
  struct IO {
    // TYPES
    struct Pure {
      std::any a;
    };

    struct Bind {
      std::shared_ptr<IO> a;
      std::function<IO(std::any)> b;
    };

    struct Get_line {};

    struct Print {
      std::string a0;
    };

    using variant_t = std::variant<Pure, Bind, Get_line, Print>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    IO() {}

    explicit IO(Pure _v) : v_(std::move(_v)) {}

    explicit IO(Bind _v) : v_(std::move(_v)) {}

    explicit IO(Get_line _v) : v_(_v) {}

    explicit IO(Print _v) : v_(std::move(_v)) {}

    static IO pure(std::any a) { return IO(Pure{std::move(a)}); }

    static IO bind(IO a, std::function<IO(std::any)> b) {
      return IO(Bind{std::make_shared<IO>(std::move(a)), std::move(b)});
    }

    static IO get_line() { return IO(Get_line{}); }

    static IO print(std::string a0) { return IO(Print{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F0, typename F1, typename F3>
    requires std::is_invocable_r_v<T1, F3 &, std::string &>
  static T1 IO_rect(F0 &&f, F1 &&f0, T1 f1, F3 &&f2, const IO &i) {
    if (std::holds_alternative<typename IO::Pure>(i.v())) {
      const auto &[a0] = std::get<typename IO::Pure>(i.v());
      return std::any_cast<T1>(crane_call_erased(f, std::any_cast<T2>(a0)));
    } else if (std::holds_alternative<typename IO::Bind>(i.v())) {
      const auto &[a, b] = std::get<typename IO::Bind>(i.v());
      return std::any_cast<T1>(f0(*a, IO_rect<T1, T2>(f, f0, f1, f2, *a), b,
                                  [=](const auto &a0) mutable {
                                    return IO_rect<T1, T2>(f, f0, f1, f2,
                                                           b(a0));
                                  }));
    } else if (std::holds_alternative<typename IO::Get_line>(i.v())) {
      return f1;
    } else {
      const auto &[a0] = std::get<typename IO::Print>(i.v());
      return f2(a0);
    }
  }

  template <typename T1, typename T2, typename F0, typename F1, typename F3>
    requires std::is_invocable_r_v<T1, F3 &, std::string &>
  static T1 IO_rec(F0 &&f, F1 &&f0, T1 f1, F3 &&f2, const IO &i) {
    if (std::holds_alternative<typename IO::Pure>(i.v())) {
      const auto &[a0] = std::get<typename IO::Pure>(i.v());
      return std::any_cast<T1>(crane_call_erased(f, std::any_cast<T2>(a0)));
    } else if (std::holds_alternative<typename IO::Bind>(i.v())) {
      const auto &[a, b] = std::get<typename IO::Bind>(i.v());
      return std::any_cast<T1>(f0(*a, IO_rec<T1, T2>(f, f0, f1, f2, *a), b,
                                  [=](const auto &a0) mutable {
                                    return IO_rec<T1, T2>(f, f0, f1, f2, b(a0));
                                  }));
    } else if (std::holds_alternative<typename IO::Get_line>(i.v())) {
      return f1;
    } else {
      const auto &[a0] = std::get<typename IO::Print>(i.v());
      return f2(a0);
    }
  }

  static inline const IO test = IO::pure(Unit::TT);
};

#endif // INCLUDED_FREE_MONAD
