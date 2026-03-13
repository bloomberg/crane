#ifndef INCLUDED_REGEXP
#define INCLUDED_REGEXP

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

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Matcher {
  __attribute__((pure)) static bool char_eq(const int64_t x, const int64_t y);

  /// Regular expression abstract syntax
  struct regexp {
    // TYPES
    struct Any {};

    struct Char {
      int64_t d_a0;
    };

    struct Eps {};

    struct Cat {
      std::shared_ptr<regexp> d_a0;
      std::shared_ptr<regexp> d_a1;
    };

    struct Alt {
      std::shared_ptr<regexp> d_a0;
      std::shared_ptr<regexp> d_a1;
    };

    struct Zero {};

    struct Star {
      std::shared_ptr<regexp> d_a0;
    };

    using variant_t = std::variant<Any, Char, Eps, Cat, Alt, Zero, Star>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit regexp(Any _v) : d_v_(std::move(_v)) {}

    explicit regexp(Char _v) : d_v_(std::move(_v)) {}

    explicit regexp(Eps _v) : d_v_(std::move(_v)) {}

    explicit regexp(Cat _v) : d_v_(std::move(_v)) {}

    explicit regexp(Alt _v) : d_v_(std::move(_v)) {}

    explicit regexp(Zero _v) : d_v_(std::move(_v)) {}

    explicit regexp(Star _v) : d_v_(std::move(_v)) {}

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
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
              int64_t c = _args.d_a0;
              return f0(c);
            },
            [&](const typename regexp::Eps _args) -> T1 { return f1; },
            [&](const typename regexp::Cat _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args.d_a0;
              std::shared_ptr<regexp> r2 = _args.d_a1;
              return f2(r1, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Alt _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args.d_a0;
              std::shared_ptr<regexp> r2 = _args.d_a1;
              return f3(r1, regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Zero _args) -> T1 { return f4; },
            [&](const typename regexp::Star _args) -> T1 {
              std::shared_ptr<regexp> r0 = _args.d_a0;
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
              int64_t c = _args.d_a0;
              return f0(c);
            },
            [&](const typename regexp::Eps _args) -> T1 { return f1; },
            [&](const typename regexp::Cat _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args.d_a0;
              std::shared_ptr<regexp> r2 = _args.d_a1;
              return f2(r1, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Alt _args) -> T1 {
              std::shared_ptr<regexp> r1 = _args.d_a0;
              std::shared_ptr<regexp> r2 = _args.d_a1;
              return f3(r1, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r1), r2,
                        regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r2));
            },
            [&](const typename regexp::Zero _args) -> T1 { return f4; },
            [&](const typename regexp::Star _args) -> T1 {
              std::shared_ptr<regexp> r0 = _args.d_a0;
              return f5(r0, regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, r0));
            }},
        r->v());
  }

  __attribute__((pure)) static bool regexp_eq(const std::shared_ptr<regexp> &r,
                                              const std::shared_ptr<regexp> &x);
  /// An optimized constructor for Cat.
  static std::shared_ptr<regexp> OptCat(std::shared_ptr<regexp> r1,
                                        std::shared_ptr<regexp> r2);
  /// Optimized version of Alt.
  static std::shared_ptr<regexp> OptAlt(std::shared_ptr<regexp> r1,
                                        std::shared_ptr<regexp> r2);
  /// If r accepts the empty string, return Eps, else return Zero.
  static std::shared_ptr<regexp> null(const std::shared_ptr<regexp> &r);
  __attribute__((pure)) static bool
  accepts_null(const std::shared_ptr<regexp> &r);
  /// This is the heart of the algorithm.  It returns a regexp denoting
  /// { cs | (c::cs) in r }.
  static std::shared_ptr<regexp> deriv(const std::shared_ptr<regexp> &r,
                                       const int64_t c);
  /// This calculates the derivative of a regular expression with respect to a
  /// string.
  static std::shared_ptr<regexp>
  derivs(std::shared_ptr<regexp> r, const std::shared_ptr<List<int64_t>> &cs);
  /// To see if cs matches r, calculate the derivative of r with respect
  /// to s, and see if the resulting regexp accepts the empty string.
  __attribute__((pure)) static bool
  deriv_parse(const std::shared_ptr<regexp> &r,
              const std::shared_ptr<List<int64_t>> &cs);
  /// null r returns Eps or Zero
  __attribute__((pure)) static bool
  NullEpsOrZero(const std::shared_ptr<regexp> &r);
  /// From this, we can build a decidable regexp matcher by running
  /// the derivative-based parser.
  __attribute__((pure)) static bool
  parse(const std::shared_ptr<regexp> &r,
        const std::shared_ptr<List<int64_t>> &cs);
  __attribute__((pure)) static bool
  parse_bool(const std::shared_ptr<regexp> &r,
             const std::shared_ptr<List<int64_t>> &cs);
  static inline const std::shared_ptr<regexp> r1 =
      regexp::ctor::Cat_(regexp::ctor::Star_(regexp::ctor::Char_(int64_t(0))),
                         regexp::ctor::Char_(int64_t(1)));
  static inline const std::shared_ptr<List<int64_t>> s1 =
      List<int64_t>::ctor::Cons_(
          int64_t(0),
          List<int64_t>::ctor::Cons_(int64_t(1), List<int64_t>::ctor::Nil_()));
  static inline const std::shared_ptr<List<int64_t>> s2 =
      List<int64_t>::ctor::Cons_(int64_t(1), List<int64_t>::ctor::Nil_());
  static inline const std::shared_ptr<List<int64_t>> s3 =
      List<int64_t>::ctor::Cons_(
          int64_t(0),
          List<int64_t>::ctor::Cons_(
              int64_t(0), List<int64_t>::ctor::Cons_(
                              int64_t(1), List<int64_t>::ctor::Nil_())));
  static inline const std::shared_ptr<List<int64_t>> s4 =
      List<int64_t>::ctor::Cons_(int64_t(0), List<int64_t>::ctor::Nil_());
};

#endif // INCLUDED_REGEXP
