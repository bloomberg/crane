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

enum class unit { tt };

struct FreeMonad {
  struct IO {
    // TYPES
    struct pure {
      std::any _a0;
    };

    struct bind {
      std::shared_ptr<IO> _a0;
      std::function<std::shared_ptr<IO>(std::any)> _a1;
    };

    struct get_line {};

    struct print {
      std::string _a0;
    };

    using variant_t = std::variant<pure, bind, get_line, print>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit IO(pure _v) : v_(std::move(_v)) {}

    explicit IO(bind _v) : v_(std::move(_v)) {}

    explicit IO(get_line _v) : v_(std::move(_v)) {}

    explicit IO(print _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<IO> pure_(std::any a0) {
        return std::shared_ptr<IO>(new IO(pure{a0}));
      }

      static std::shared_ptr<IO>
      bind_(const std::shared_ptr<IO> &a0,
            std::function<std::shared_ptr<IO>(std::any)> a1) {
        return std::shared_ptr<IO>(new IO(bind{a0, a1}));
      }

      static std::shared_ptr<IO> get_line_() {
        return std::shared_ptr<IO>(new IO(get_line{}));
      }

      static std::shared_ptr<IO> print_(std::string a0) {
        return std::shared_ptr<IO>(new IO(print{a0}));
      }

      static std::unique_ptr<IO> pure_uptr(std::any a0) {
        return std::unique_ptr<IO>(new IO(pure{a0}));
      }

      static std::unique_ptr<IO>
      bind_uptr(const std::shared_ptr<IO> &a0,
                std::function<std::shared_ptr<IO>(std::any)> a1) {
        return std::unique_ptr<IO>(new IO(bind{a0, a1}));
      }

      static std::unique_ptr<IO> get_line_uptr() {
        return std::unique_ptr<IO>(new IO(get_line{}));
      }

      static std::unique_ptr<IO> print_uptr(std::string a0) {
        return std::unique_ptr<IO>(new IO(print{a0}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1, MapsTo<T1, std::string> F3>
  static T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                    const std::shared_ptr<IO> &i) {
    return std::visit(
        Overloaded{[&](const typename IO::pure _args) -> T1 {
                     F0 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename IO::bind _args) -> T1 {
                     std::shared_ptr<IO> i0 = _args._a0;
                     std::function<std::shared_ptr<IO>(std::any)> i1 =
                         _args._a1;
                     return f0(i0, IO_rect<T1>(f, f0, f1, f2, i0), i1,
                               [=](std::any a) mutable {
                                 return IO_rect<T1>(f, f0, f1, f2, i1(a));
                               });
                   },
                   [&](const typename IO::get_line _args) -> T1 { return f1; },
                   [&](const typename IO::print _args) -> T1 {
                     std::string s = _args._a0;
                     return f2(s);
                   }},
        i->v());
  }

  template <typename T1, typename F0, typename F1, MapsTo<T1, std::string> F3>
  static T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                   const std::shared_ptr<IO> &i) {
    return std::visit(
        Overloaded{[&](const typename IO::pure _args) -> T1 {
                     F0 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename IO::bind _args) -> T1 {
                     std::shared_ptr<IO> i0 = _args._a0;
                     std::function<std::shared_ptr<IO>(std::any)> i1 =
                         _args._a1;
                     return f0(i0, IO_rec<T1>(f, f0, f1, f2, i0), i1,
                               [=](std::any a) mutable {
                                 return IO_rec<T1>(f, f0, f1, f2, i1(a));
                               });
                   },
                   [&](const typename IO::get_line _args) -> T1 { return f1; },
                   [&](const typename IO::print _args) -> T1 {
                     std::string s = _args._a0;
                     return f2(s);
                   }},
        i->v());
  }

  static inline const std::shared_ptr<IO> test = IO::ctor::pure_(unit::tt);
};
