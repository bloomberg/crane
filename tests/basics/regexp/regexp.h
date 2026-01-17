#include <algorithm>
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

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<list<A>> nil_() {
        return std::shared_ptr<list<A>>(new list<A>(nil{}));
      }
      static std::shared_ptr<list<A>>
      cons_(A a0, const std::shared_ptr<list<A>> &a1) {
        return std::shared_ptr<list<A>>(new list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Matcher {
  static bool char_eq(const int x, const int y);

  struct regexp {
  public:
    struct Any {};
    struct Char {
      int _a0;
    };
    struct Eps {};
    struct Cat {
      std::shared_ptr<regexp> _a0;
      std::shared_ptr<regexp> _a1;
    };
    struct Alt {
      std::shared_ptr<regexp> _a0;
      std::shared_ptr<regexp> _a1;
    };
    struct Zero {};
    struct Star {
      std::shared_ptr<regexp> _a0;
    };
    using variant_t = std::variant<Any, Char, Eps, Cat, Alt, Zero, Star>;

  private:
    variant_t v_;
    explicit regexp(Any x) : v_(std::move(x)) {}
    explicit regexp(Char x) : v_(std::move(x)) {}
    explicit regexp(Eps x) : v_(std::move(x)) {}
    explicit regexp(Cat x) : v_(std::move(x)) {}
    explicit regexp(Alt x) : v_(std::move(x)) {}
    explicit regexp(Zero x) : v_(std::move(x)) {}
    explicit regexp(Star x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<regexp> Any_() {
        return std::shared_ptr<regexp>(new regexp(Any{}));
      }
      static std::shared_ptr<regexp> Char_(int a0) {
        return std::shared_ptr<regexp>(new regexp(Char{a0}));
      }
      static std::shared_ptr<regexp> Eps_() {
        return std::shared_ptr<regexp>(new regexp(Eps{}));
      }
      static std::shared_ptr<regexp> Cat_(const std::shared_ptr<regexp> &a0,
                                          const std::shared_ptr<regexp> &a1) {
        return std::shared_ptr<regexp>(new regexp(Cat{a0, a1}));
      }
      static std::shared_ptr<regexp> Alt_(const std::shared_ptr<regexp> &a0,
                                          const std::shared_ptr<regexp> &a1) {
        return std::shared_ptr<regexp>(new regexp(Alt{a0, a1}));
      }
      static std::shared_ptr<regexp> Zero_() {
        return std::shared_ptr<regexp>(new regexp(Zero{}));
      }
      static std::shared_ptr<regexp> Star_(const std::shared_ptr<regexp> &a0) {
        return std::shared_ptr<regexp>(new regexp(Star{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <
      typename T1, MapsTo<T1, int> F1,
      MapsTo<T1, std::shared_ptr<regexp>, T1, std::shared_ptr<regexp>, T1> F3,
      MapsTo<T1, std::shared_ptr<regexp>, T1, std::shared_ptr<regexp>, T1> F4,
      MapsTo<T1, std::shared_ptr<regexp>, T1> F6>
  static T1 regexp_rect(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3,
                        const T1 f4, F6 &&f5,
                        const std::shared_ptr<regexp> &r) {
    return std::visit(
        Overloaded{
            [&](const typename regexp::Any _args) -> T1 { return f; },
            [&](const typename regexp::Char _args) -> T1 {
              int c = _args._a0;
              return f0(c);
            },
            [&](const typename regexp::Eps _args) -> T1 { return f1; },
            [&](const typename regexp::Cat _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args._a0;
              std::shared_ptr<regexp> r2 = _args._a1;
              return f2(r1, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Alt _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args._a0;
              std::shared_ptr<regexp> r2 = _args._a1;
              return f3(r1, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Zero _args) -> T1 { return f4; },
            [&](const typename regexp::Star _args) -> T1 {
              std::shared_ptr<regexp> r0 = _args._a0;
              return f5(r0, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r0));
            }},
        r->v());
  }

  template <
      typename T1, MapsTo<T1, int> F1,
      MapsTo<T1, std::shared_ptr<regexp>, T1, std::shared_ptr<regexp>, T1> F3,
      MapsTo<T1, std::shared_ptr<regexp>, T1, std::shared_ptr<regexp>, T1> F4,
      MapsTo<T1, std::shared_ptr<regexp>, T1> F6>
  static T1 regexp_rec(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3,
                       const T1 f4, F6 &&f5, const std::shared_ptr<regexp> &r) {
    return std::visit(
        Overloaded{
            [&](const typename regexp::Any _args) -> T1 { return f; },
            [&](const typename regexp::Char _args) -> T1 {
              int c = _args._a0;
              return f0(c);
            },
            [&](const typename regexp::Eps _args) -> T1 { return f1; },
            [&](const typename regexp::Cat _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args._a0;
              std::shared_ptr<regexp> r2 = _args._a1;
              return f2(r1, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Alt _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args._a0;
              std::shared_ptr<regexp> r2 = _args._a1;
              return f3(r1, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Zero _args) -> T1 { return f4; },
            [&](const typename regexp::Star _args) -> T1 {
              std::shared_ptr<regexp> r0 = _args._a0;
              return f5(r0, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r0));
            }},
        r->v());
  }

  static bool regexp_eq(const std::shared_ptr<regexp> &r,
                        const std::shared_ptr<regexp> &x);

  static std::shared_ptr<regexp> OptCat(const std::shared_ptr<regexp> &r1,
                                        const std::shared_ptr<regexp> &r2);

  static std::shared_ptr<regexp> OptAlt(const std::shared_ptr<regexp> &r1,
                                        const std::shared_ptr<regexp> &r2);

  static std::shared_ptr<regexp> null(const std::shared_ptr<regexp> &r);

  static bool accepts_null(const std::shared_ptr<regexp> &r);

  static std::shared_ptr<regexp> deriv(const std::shared_ptr<regexp> &r,
                                       const int c);

  static std::shared_ptr<regexp>
  derivs(const std::shared_ptr<regexp> &r,
         const std::shared_ptr<List::list<int>> &cs);

  static bool deriv_parse(const std::shared_ptr<regexp> &r,
                          const std::shared_ptr<List::list<int>> &cs);

  static bool NullEpsOrZero(const std::shared_ptr<regexp> &r);

  static bool parse(const std::shared_ptr<regexp> &r,
                    const std::shared_ptr<List::list<int>> &cs);

  static bool parse_bool(const std::shared_ptr<regexp> &r,
                         const std::shared_ptr<List::list<int>> &cs);

  static inline const std::shared_ptr<regexp> r1 = regexp::ctor::Cat_(
      regexp::ctor::Star_(regexp::ctor::Char_(0)), regexp::ctor::Char_(1));

  static inline const std::shared_ptr<List::list<int>> s1 =
      List::list<int>::ctor::cons_(
          0, List::list<int>::ctor::cons_(1, List::list<int>::ctor::nil_()));

  static inline const std::shared_ptr<List::list<int>> s2 =
      List::list<int>::ctor::cons_(1, List::list<int>::ctor::nil_());

  static inline const std::shared_ptr<List::list<int>> s3 =
      List::list<int>::ctor::cons_(
          0, List::list<int>::ctor::cons_(
                 0, List::list<int>::ctor::cons_(
                        1, List::list<int>::ctor::nil_())));

  static inline const std::shared_ptr<List::list<int>> s4 =
      List::list<int>::ctor::cons_(0, List::list<int>::ctor::nil_());
};
