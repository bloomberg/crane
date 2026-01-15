#include <functional>
#include <iostream>
#include <memory>
#include <string>
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
    explicit unit(tt x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<unit> tt_() {
        return std::shared_ptr<unit>(new unit(tt{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct FreeMonad {
  template <typename x> struct IO {
  public:
    struct pure {
      x _a0;
    };
    struct bind {
      std::shared_ptr<IO<unknown>> _a0;
      std::function<std::shared_ptr<IO<x>>(unknown)> _a1;
    };
    struct get_line {};
    struct print {
      std::string _a0;
    };
    using variant_t = std::variant<pure, bind, get_line, print>;

  private:
    variant_t v_;
    explicit IO(pure x) : v_(std::move(x)) {}
    explicit IO(bind x) : v_(std::move(x)) {}
    explicit IO(get_line x) : v_(std::move(x)) {}
    explicit IO(print x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<IO<x>> pure_(x a0) {
        return std::shared_ptr<IO<x>>(new IO<x>(pure{a0}));
      }
      static std::shared_ptr<IO<x>>
      bind_(const std::shared_ptr<IO<unknown>> &a0,
            std::function<std::shared_ptr<IO<x>>(unknown)> a1) {
        return std::shared_ptr<IO<x>>(new IO<x>(bind{a0, a1}));
      }
      static std::shared_ptr<IO<x>> get_line_() {
        return std::shared_ptr<IO<x>>(new IO<x>(get_line{}));
      }
      static std::shared_ptr<IO<x>> print_(std::string a0) {
        return std::shared_ptr<IO<x>>(new IO<x>(print{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T1, unknown> F0,
            MapsTo<T1, std::shared_ptr<IO<unknown>>, T1,
                   std::function<std::shared_ptr<IO<unknown>>(unknown)>,
                   std::function<T1(unknown)>>
                F1,
            MapsTo<T1, std::string> F3>
  static T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                    const std::shared_ptr<IO<T2>> &i) {
    return std::visit(
        Overloaded{
            [&](const typename IO<T2>::pure _args) -> T1 {
              T2 a = _args._a0;
              return f("dummy", a);
            },
            [&](const typename IO<T2>::bind _args) -> T1 {
              std::shared_ptr<IO<unknown>> i0 = _args._a0;
              std::function<std::shared_ptr<IO<T2>>(unknown)> i1 = _args._a1;
              return f0("dummy", "dummy", i0,
                        IO_rect<T1, T2>(f, f0, f1, f2, i0), i1, [&](unknown a) {
                          return IO_rect<T1, T2>(f, f0, f1, f2, i1(a));
                        });
            },
            [&](const typename IO<T2>::get_line _args) -> T1 { return f1; },
            [&](const typename IO<T2>::print _args) -> T1 {
              std::string s = _args._a0;
              return f2(s);
            }},
        i->v());
  }

  template <typename T1, typename T2, MapsTo<T1, unknown> F0,
            MapsTo<T1, std::shared_ptr<IO<unknown>>, T1,
                   std::function<std::shared_ptr<IO<unknown>>(unknown)>,
                   std::function<T1(unknown)>>
                F1,
            MapsTo<T1, std::string> F3>
  static T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                   const std::shared_ptr<IO<T2>> &i) {
    return std::visit(
        Overloaded{
            [&](const typename IO<T2>::pure _args) -> T1 {
              T2 a = _args._a0;
              return f("dummy", a);
            },
            [&](const typename IO<T2>::bind _args) -> T1 {
              std::shared_ptr<IO<unknown>> i0 = _args._a0;
              std::function<std::shared_ptr<IO<T2>>(unknown)> i1 = _args._a1;
              return f0("dummy", "dummy", i0, IO_rec<T1, T2>(f, f0, f1, f2, i0),
                        i1, [&](unknown a) {
                          return IO_rec<T1, T2>(f, f0, f1, f2, i1(a));
                        });
            },
            [&](const typename IO<T2>::get_line _args) -> T1 { return f1; },
            [&](const typename IO<T2>::print _args) -> T1 {
              std::string s = _args._a0;
              return f2(s);
            }},
        i->v());
  }

  static inline const std::shared_ptr<IO<std::shared_ptr<Unit::unit>>> test =
      IO<std::shared_ptr<Unit::unit>>::ctor::pure_(Unit::unit::ctor::tt_());
};
