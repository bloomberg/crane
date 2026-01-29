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
  struct iO {
  public:
    struct pure {
      std::any _a0;
    };
    struct bind {
      std::shared_ptr<iO> _a0;
      std::function<std::shared_ptr<iO>(std::any)> _a1;
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
      static std::shared_ptr<iO> pure_(std::any a0) {
        return std::shared_ptr<iO>(new iO(pure{a0}));
      }
      static std::shared_ptr<iO>
      bind_(const std::shared_ptr<iO> &a0,
            std::function<std::shared_ptr<iO>(std::any)> a1) {
        return std::shared_ptr<iO>(new iO(bind{a0, a1}));
      }
      static std::shared_ptr<iO> get_line_() {
        return std::shared_ptr<iO>(new iO(get_line{}));
      }
      static std::shared_ptr<iO> print_(std::string a0) {
        return std::shared_ptr<iO>(new iO(print{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, MapsTo<T1, std::any> F0,
            MapsTo<T1, std::shared_ptr<iO>, T1,
                   std::function<std::shared_ptr<iO>(std::any)>,
                   std::function<T1(std::any)>>
                F1,
            MapsTo<T1, std::string> F3>
  static T1 IO_rect(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                    const std::shared_ptr<iO> &i) {
    return std::visit(
        Overloaded{[&](const typename iO::pure _args) -> T1 {
                     std::any a = _args._a0;
                     return f("dummy", a);
                   },
                   [&](const typename iO::bind _args) -> T1 {
                     std::shared_ptr<iO> i0 = _args._a0;
                     std::function<std::shared_ptr<iO>(std::any)> i1 =
                         _args._a1;
                     return f0("dummy", "dummy", i0,
                               IO_rect<T1>(f, f0, f1, f2, i0), i1,
                               [&](std::any a) {
                                 return IO_rect<T1>(f, f0, f1, f2, i1(a));
                               });
                   },
                   [&](const typename iO::get_line _args) -> T1 { return f1; },
                   [&](const typename iO::print _args) -> T1 {
                     std::string s = _args._a0;
                     return f2(s);
                   }},
        i->v());
  }

  template <typename T1, MapsTo<T1, std::any> F0,
            MapsTo<T1, std::shared_ptr<iO>, T1,
                   std::function<std::shared_ptr<iO>(std::any)>,
                   std::function<T1(std::any)>>
                F1,
            MapsTo<T1, std::string> F3>
  static T1 IO_rec(F0 &&f, F1 &&f0, const T1 f1, F3 &&f2,
                   const std::shared_ptr<iO> &i) {
    return std::visit(
        Overloaded{[&](const typename iO::pure _args) -> T1 {
                     std::any a = _args._a0;
                     return f("dummy", a);
                   },
                   [&](const typename iO::bind _args) -> T1 {
                     std::shared_ptr<iO> i0 = _args._a0;
                     std::function<std::shared_ptr<iO>(std::any)> i1 =
                         _args._a1;
                     return f0("dummy", "dummy", i0,
                               IO_rec<T1>(f, f0, f1, f2, i0), i1,
                               [&](std::any a) {
                                 return IO_rec<T1>(f, f0, f1, f2, i1(a));
                               });
                   },
                   [&](const typename iO::get_line _args) -> T1 { return f1; },
                   [&](const typename iO::print _args) -> T1 {
                     std::string s = _args._a0;
                     return f2(s);
                   }},
        i->v());
  }

  static inline const std::shared_ptr<iO> test =
      iO::ctor::pure_(Unit::unit::ctor::tt_());
};
