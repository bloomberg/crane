#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
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

template <typename A> struct List {
  // TYPES
  struct nil {};

  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };

  using variant_t = std::variant<nil, cons>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit List(nil _v) : v_(std::move(_v)) {}

  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }

    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }

    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Matcher {
  static bool char_eq(const int64_t x, const int64_t y);

  struct regexp {
    // TYPES
    struct Any {};

    struct Char {
      int64_t _a0;
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
    // DATA
    variant_t v_;

    // CREATORS
    explicit regexp(Any _v) : v_(std::move(_v)) {}

    explicit regexp(Char _v) : v_(std::move(_v)) {}

    explicit regexp(Eps _v) : v_(std::move(_v)) {}

    explicit regexp(Cat _v) : v_(std::move(_v)) {}

    explicit regexp(Alt _v) : v_(std::move(_v)) {}

    explicit regexp(Zero _v) : v_(std::move(_v)) {}

    explicit regexp(Star _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<regexp> Any_() {
        return std::shared_ptr<regexp>(new regexp(Any{}));
      }

      static std::shared_ptr<regexp> Char_(int64_t a0) {
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

      static std::unique_ptr<regexp> Any_uptr() {
        return std::unique_ptr<regexp>(new regexp(Any{}));
      }

      static std::unique_ptr<regexp> Char_uptr(int64_t a0) {
        return std::unique_ptr<regexp>(new regexp(Char{a0}));
      }

      static std::unique_ptr<regexp> Eps_uptr() {
        return std::unique_ptr<regexp>(new regexp(Eps{}));
      }

      static std::unique_ptr<regexp>
      Cat_uptr(const std::shared_ptr<regexp> &a0,
               const std::shared_ptr<regexp> &a1) {
        return std::unique_ptr<regexp>(new regexp(Cat{a0, a1}));
      }

      static std::unique_ptr<regexp>
      Alt_uptr(const std::shared_ptr<regexp> &a0,
               const std::shared_ptr<regexp> &a1) {
        return std::unique_ptr<regexp>(new regexp(Alt{a0, a1}));
      }

      static std::unique_ptr<regexp> Zero_uptr() {
        return std::unique_ptr<regexp>(new regexp(Zero{}));
      }

      static std::unique_ptr<regexp>
      Star_uptr(const std::shared_ptr<regexp> &a0) {
        return std::unique_ptr<regexp>(new regexp(Star{a0}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <
      typename T1, MapsTo<T1, int64_t> F1,
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
              int64_t c = _args._a0;
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
      typename T1, MapsTo<T1, int64_t> F1,
      MapsTo<T1, std::shared_ptr<regexp>, T1, std::shared_ptr<regexp>, T1> F3,
      MapsTo<T1, std::shared_ptr<regexp>, T1, std::shared_ptr<regexp>, T1> F4,
      MapsTo<T1, std::shared_ptr<regexp>, T1> F6>
  static T1 regexp_rec(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3,
                       const T1 f4, F6 &&f5, const std::shared_ptr<regexp> &r) {
    return std::visit(
        Overloaded{
            [&](const typename regexp::Any _args) -> T1 { return f; },
            [&](const typename regexp::Char _args) -> T1 {
              int64_t c = _args._a0;
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
  static std::shared_ptr<regexp> OptCat(std::shared_ptr<regexp> r1,
                                        std::shared_ptr<regexp> r2);
  static std::shared_ptr<regexp> OptAlt(std::shared_ptr<regexp> r1,
                                        std::shared_ptr<regexp> r2);
  static std::shared_ptr<regexp> null(const std::shared_ptr<regexp> &r);
  static bool accepts_null(const std::shared_ptr<regexp> &r);
  static std::shared_ptr<regexp> deriv(const std::shared_ptr<regexp> &r,
                                       const int64_t c);
  static std::shared_ptr<regexp>
  derivs(std::shared_ptr<regexp> r, const std::shared_ptr<List<int64_t>> &cs);
  static bool deriv_parse(const std::shared_ptr<regexp> &r,
                          const std::shared_ptr<List<int64_t>> &cs);
  static bool NullEpsOrZero(const std::shared_ptr<regexp> &r);
  static bool parse(const std::shared_ptr<regexp> &r,
                    const std::shared_ptr<List<int64_t>> &cs);
  static bool parse_bool(const std::shared_ptr<regexp> &r,
                         const std::shared_ptr<List<int64_t>> &cs);
  static inline const std::shared_ptr<regexp> r1 =
      regexp::ctor::Cat_(regexp::ctor::Star_(regexp::ctor::Char_(int64_t(0))),
                         regexp::ctor::Char_(int64_t(1)));
  static inline const std::shared_ptr<List<int64_t>> s1 =
      List<int64_t>::ctor::cons_(
          int64_t(0),
          List<int64_t>::ctor::cons_(int64_t(1), List<int64_t>::ctor::nil_()));
  static inline const std::shared_ptr<List<int64_t>> s2 =
      List<int64_t>::ctor::cons_(int64_t(1), List<int64_t>::ctor::nil_());
  static inline const std::shared_ptr<List<int64_t>> s3 =
      List<int64_t>::ctor::cons_(
          int64_t(0),
          List<int64_t>::ctor::cons_(
              int64_t(0), List<int64_t>::ctor::cons_(
                              int64_t(1), List<int64_t>::ctor::nil_())));
  static inline const std::shared_ptr<List<int64_t>> s4 =
      List<int64_t>::ctor::cons_(int64_t(0), List<int64_t>::ctor::nil_());
};
