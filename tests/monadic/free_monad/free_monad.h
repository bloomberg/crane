#include <any>
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

struct FreeMonad {
  template <typename x> struct iO {
  public:
    struct pure {
      x _a0;
    };
    struct bind {
      std::shared_ptr<iO<std::any>> _a0;
      std::function<std::shared_ptr<iO<x>>(std::any)> _a1;
    };
    struct get_line {};
    struct print {
      std::string _a0;
    };
    using variant_t = std::variant<pure, bind, get_line, print>;

  private:
    variant_t v_;
    explicit iO(pure _v) : v_(std::move(_v)) {}
    explicit iO(bind _v) : v_(std::move(_v)) {}
    explicit iO(get_line _v) : v_(std::move(_v)) {}
    explicit iO(print _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<iO<x>> pure_(x a0) {
        return std::shared_ptr<iO<x>>(new iO<x>(pure{a0}));
      }
      static std::shared_ptr<iO<x>>
      bind_(const std::shared_ptr<iO<std::any>> &a0,
            std::function<std::shared_ptr<iO<x>>(std::any)> a1) {
        return std::shared_ptr<iO<x>>(new iO<x>(bind{a0, a1}));
      }
      static std::shared_ptr<iO<x>> get_line_() {
        return std::shared_ptr<iO<x>>(new iO<x>(get_line{}));
      }
      static std::shared_ptr<iO<x>> print_(std::string a0) {
        return std::shared_ptr<iO<x>>(new iO<x>(print{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, MapsTo<T1, std::any> F0,
            MapsTo<T1, std::shared_ptr<iO<std::any>>, T1,
                   std::function<std::shared_ptr<iO<std::any>>(std::any)>,
                   std::function<T1(std::any)>>
                F1,
            MapsTo<T1, std::string> F3>
  static T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                    const std::shared_ptr<iO<T2>> &i) {
    return std::visit(
        Overloaded{
            [&](const typename iO<T2>::pure _args) -> T1 {
              T2 a = _args._a0;
              return f("dummy", a);
            },
            [&](const typename iO<T2>::bind _args) -> T1 {
              std::shared_ptr<iO<std::any>> i0 = _args._a0;
              std::function<std::shared_ptr<iO<T2>>(std::any)> i1 = _args._a1;
              return f0("dummy", "dummy", i0,
                        IO_rect<T1, T2>(f, f0, f1, f2, i0), i1,
                        [&](std::any a) {
                          return IO_rect<T1, T2>(f, f0, f1, f2, i1(a));
                        });
            },
            [&](const typename iO<T2>::get_line _args) -> T1 { return f1; },
            [&](const typename iO<T2>::print _args) -> T1 {
              std::string s = _args._a0;
              return f2(s);
            }},
        i->v());
  }

  template <typename T1, typename T2, MapsTo<T1, std::any> F0,
            MapsTo<T1, std::shared_ptr<iO<std::any>>, T1,
                   std::function<std::shared_ptr<iO<std::any>>(std::any)>,
                   std::function<T1(std::any)>>
                F1,
            MapsTo<T1, std::string> F3>
  static T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                   const std::shared_ptr<iO<T2>> &i) {
    return std::visit(
        Overloaded{
            [&](const typename iO<T2>::pure _args) -> T1 {
              T2 a = _args._a0;
              return f("dummy", a);
            },
            [&](const typename iO<T2>::bind _args) -> T1 {
              std::shared_ptr<iO<std::any>> i0 = _args._a0;
              std::function<std::shared_ptr<iO<T2>>(std::any)> i1 = _args._a1;
              return f0("dummy", "dummy", i0, IO_rec<T1, T2>(f, f0, f1, f2, i0),
                        i1, [&](std::any a) {
                          return IO_rec<T1, T2>(f, f0, f1, f2, i1(a));
                        });
            },
            [&](const typename iO<T2>::get_line _args) -> T1 { return f1; },
            [&](const typename iO<T2>::print _args) -> T1 {
              std::string s = _args._a0;
              return f2(s);
            }},
        i->v());
  }

  static inline const std::shared_ptr<iO<std::shared_ptr<Unit::unit>>> test =
      iO<std::shared_ptr<Unit::unit>>::ctor::pure_(Unit::unit::ctor::tt_());
};
