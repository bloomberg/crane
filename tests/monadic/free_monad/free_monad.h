#ifndef INCLUDED_FREE_MONAD
#define INCLUDED_FREE_MONAD

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Unit { e_TT };

struct FreeMonad {
  struct IO {
    // TYPES
    struct Pure {
      std::any d_a0;
    };

    struct Bind {
      std::shared_ptr<IO> d_a0;
      std::function<std::shared_ptr<IO>(std::any)> d_a1;
    };

    struct Get_line {};

    struct Print {
      std::string d_a0;
    };

    using variant_t = std::variant<Pure, Bind, Get_line, Print>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit IO(Pure _v) : d_v_(std::move(_v)) {}

    explicit IO(Bind _v) : d_v_(std::move(_v)) {}

    explicit IO(Get_line _v) : d_v_(std::move(_v)) {}

    explicit IO(Print _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<IO> Pure_(std::any a0) {
        return std::shared_ptr<IO>(new IO(Pure{a0}));
      }

      static std::shared_ptr<IO>
      Bind_(const std::shared_ptr<IO> &a0,
            std::function<std::shared_ptr<IO>(std::any)> a1) {
        return std::shared_ptr<IO>(new IO(Bind{a0, a1}));
      }

      static std::shared_ptr<IO> Get_line_() {
        return std::shared_ptr<IO>(new IO(Get_line{}));
      }

      static std::shared_ptr<IO> Print_(std::string a0) {
        return std::shared_ptr<IO>(new IO(Print{a0}));
      }

      static std::unique_ptr<IO> Pure_uptr(std::any a0) {
        return std::unique_ptr<IO>(new IO(Pure{a0}));
      }

      static std::unique_ptr<IO>
      Bind_uptr(const std::shared_ptr<IO> &a0,
                std::function<std::shared_ptr<IO>(std::any)> a1) {
        return std::unique_ptr<IO>(new IO(Bind{a0, a1}));
      }

      static std::unique_ptr<IO> Get_line_uptr() {
        return std::unique_ptr<IO>(new IO(Get_line{}));
      }

      static std::unique_ptr<IO> Print_uptr(std::string a0) {
        return std::unique_ptr<IO>(new IO(Print{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename F0, typename F1, MapsTo<T1, std::string> F3>
  static T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                    const std::shared_ptr<IO> &i) {
    return std::visit(
        Overloaded{[&](const typename IO::Pure _args) -> T1 {
                     F0 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename IO::Bind _args) -> T1 {
                     std::shared_ptr<IO> i0 = _args.d_a0;
                     std::function<std::shared_ptr<IO>(std::any)> i1 =
                         _args.d_a1;
                     return f0(i0, IO_rect<T1>(f, f0, f1, f2, i0), i1,
                               [=](std::any a) mutable {
                                 return IO_rect<T1>(f, f0, f1, f2, i1(a));
                               });
                   },
                   [&](const typename IO::Get_line _args) -> T1 { return f1; },
                   [&](const typename IO::Print _args) -> T1 {
                     std::string s = _args.d_a0;
                     return f2(s);
                   }},
        i->v());
  }

  template <typename T1, typename F0, typename F1, MapsTo<T1, std::string> F3>
  static T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                   const std::shared_ptr<IO> &i) {
    return std::visit(
        Overloaded{[&](const typename IO::Pure _args) -> T1 {
                     F0 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename IO::Bind _args) -> T1 {
                     std::shared_ptr<IO> i0 = _args.d_a0;
                     std::function<std::shared_ptr<IO>(std::any)> i1 =
                         _args.d_a1;
                     return f0(i0, IO_rec<T1>(f, f0, f1, f2, i0), i1,
                               [=](std::any a) mutable {
                                 return IO_rec<T1>(f, f0, f1, f2, i1(a));
                               });
                   },
                   [&](const typename IO::Get_line _args) -> T1 { return f1; },
                   [&](const typename IO::Print _args) -> T1 {
                     std::string s = _args.d_a0;
                     return f2(s);
                   }},
        i->v());
  }

  static inline const std::shared_ptr<IO> test = IO::ctor::Pure_(Unit::e_TT);
};

#endif // INCLUDED_FREE_MONAD
