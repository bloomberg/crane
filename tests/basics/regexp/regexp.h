#ifndef INCLUDED_REGEXP
#define INCLUDED_REGEXP

#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

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
      int64_t d_c;
    };

    struct Eps {};

    struct Cat {
      std::unique_ptr<regexp> d_r1;
      std::unique_ptr<regexp> d_r2;
    };

    struct Alt {
      std::unique_ptr<regexp> d_r1;
      std::unique_ptr<regexp> d_r2;
    };

    struct Zero {};

    struct Star {
      std::unique_ptr<regexp> d_r;
    };

    using variant_t = std::variant<Any, Char, Eps, Cat, Alt, Zero, Star>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    regexp() {}

    explicit regexp(Any _v) : d_v_(_v) {}

    explicit regexp(Char _v) : d_v_(std::move(_v)) {}

    explicit regexp(Eps _v) : d_v_(_v) {}

    explicit regexp(Cat _v) : d_v_(std::move(_v)) {}

    explicit regexp(Alt _v) : d_v_(std::move(_v)) {}

    explicit regexp(Zero _v) : d_v_(_v) {}

    explicit regexp(Star _v) : d_v_(std::move(_v)) {}

    regexp(const regexp &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    regexp(regexp &&_other) : d_v_(std::move(_other.d_v_)) {}

    regexp &operator=(const regexp &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    regexp &operator=(regexp &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) regexp clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<Any>(_sv.v())) {
        return regexp(Any{});
      } else if (std::holds_alternative<Char>(_sv.v())) {
        const auto &[d_c] = std::get<Char>(_sv.v());
        return regexp(Char{d_c});
      } else if (std::holds_alternative<Eps>(_sv.v())) {
        return regexp(Eps{});
      } else if (std::holds_alternative<Cat>(_sv.v())) {
        const auto &[d_r1, d_r2] = std::get<Cat>(_sv.v());
        return regexp(Cat{
            d_r1 ? std::make_unique<Matcher::regexp>(d_r1->clone()) : nullptr,
            d_r2 ? std::make_unique<Matcher::regexp>(d_r2->clone()) : nullptr});
      } else if (std::holds_alternative<Alt>(_sv.v())) {
        const auto &[d_r1, d_r2] = std::get<Alt>(_sv.v());
        return regexp(Alt{
            d_r1 ? std::make_unique<Matcher::regexp>(d_r1->clone()) : nullptr,
            d_r2 ? std::make_unique<Matcher::regexp>(d_r2->clone()) : nullptr});
      } else if (std::holds_alternative<Zero>(_sv.v())) {
        return regexp(Zero{});
      } else {
        const auto &[d_r] = std::get<Star>(_sv.v());
        return regexp(Star{d_r ? std::make_unique<Matcher::regexp>(d_r->clone())
                               : nullptr});
      }
    }

    // CREATORS
    __attribute__((pure)) static regexp any() { return regexp(Any{}); }

    __attribute__((pure)) static regexp Char_(int64_t c) {
      return regexp(Char{std::move(c)});
    }

    __attribute__((pure)) static regexp eps() { return regexp(Eps{}); }

    __attribute__((pure)) static regexp cat(const regexp &r1,
                                            const regexp &r2) {
      return regexp(
          Cat{std::make_unique<regexp>(r1), std::make_unique<regexp>(r2)});
    }

    __attribute__((pure)) static regexp alt(const regexp &r1,
                                            const regexp &r2) {
      return regexp(
          Alt{std::make_unique<regexp>(r1), std::make_unique<regexp>(r2)});
    }

    __attribute__((pure)) static regexp zero() { return regexp(Zero{}); }

    __attribute__((pure)) static regexp star(const regexp &r) {
      return regexp(Star{std::make_unique<regexp>(r)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, MapsTo<T1, int64_t> F1,
            MapsTo<T1, regexp, T1, regexp, T1> F3,
            MapsTo<T1, regexp, T1, regexp, T1> F4, MapsTo<T1, regexp, T1> F6>
  static T1 regexp_rect(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3,
                        const T1 f4, F6 &&f5, const regexp &r) {
    if (std::holds_alternative<typename regexp::Any>(r.v())) {
      return f;
    } else if (std::holds_alternative<typename regexp::Char>(r.v())) {
      const auto &[d_c] = std::get<typename regexp::Char>(r.v());
      return f0(d_c);
    } else if (std::holds_alternative<typename regexp::Eps>(r.v())) {
      return f1;
    } else if (std::holds_alternative<typename regexp::Cat>(r.v())) {
      const auto &[d_r1, d_r2] = std::get<typename regexp::Cat>(r.v());
      return f2(*(d_r1), regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r1)),
                *(d_r2), regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r2)));
    } else if (std::holds_alternative<typename regexp::Alt>(r.v())) {
      const auto &[d_r1, d_r2] = std::get<typename regexp::Alt>(r.v());
      return f3(*(d_r1), regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r1)),
                *(d_r2), regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r2)));
    } else if (std::holds_alternative<typename regexp::Zero>(r.v())) {
      return f4;
    } else {
      const auto &[d_r] = std::get<typename regexp::Star>(r.v());
      return f5(*(d_r), regexp_rect<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r)));
    }
  }

  template <typename T1, MapsTo<T1, int64_t> F1,
            MapsTo<T1, regexp, T1, regexp, T1> F3,
            MapsTo<T1, regexp, T1, regexp, T1> F4, MapsTo<T1, regexp, T1> F6>
  static T1 regexp_rec(const T1 f, F1 &&f0, const T1 f1, F3 &&f2, F4 &&f3,
                       const T1 f4, F6 &&f5, const regexp &r) {
    if (std::holds_alternative<typename regexp::Any>(r.v())) {
      return f;
    } else if (std::holds_alternative<typename regexp::Char>(r.v())) {
      const auto &[d_c] = std::get<typename regexp::Char>(r.v());
      return f0(d_c);
    } else if (std::holds_alternative<typename regexp::Eps>(r.v())) {
      return f1;
    } else if (std::holds_alternative<typename regexp::Cat>(r.v())) {
      const auto &[d_r1, d_r2] = std::get<typename regexp::Cat>(r.v());
      return f2(*(d_r1), regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r1)),
                *(d_r2), regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r2)));
    } else if (std::holds_alternative<typename regexp::Alt>(r.v())) {
      const auto &[d_r1, d_r2] = std::get<typename regexp::Alt>(r.v());
      return f3(*(d_r1), regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r1)),
                *(d_r2), regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r2)));
    } else if (std::holds_alternative<typename regexp::Zero>(r.v())) {
      return f4;
    } else {
      const auto &[d_r] = std::get<typename regexp::Star>(r.v());
      return f5(*(d_r), regexp_rec<T1>(f, f0, f1, f2, f3, f4, f5, *(d_r)));
    }
  }

  __attribute__((pure)) static bool regexp_eq(const regexp &r, const regexp &x);
  /// An optimized constructor for Cat.
  __attribute__((pure)) static regexp OptCat(regexp r2, regexp r3);
  /// Optimized version of Alt.
  __attribute__((pure)) static regexp OptAlt(regexp r2, regexp r3);
  /// If r accepts the empty string, return Eps, else return Zero.
  __attribute__((pure)) static regexp null(const regexp &r);
  __attribute__((pure)) static bool accepts_null(const regexp &r);
  /// This is the heart of the algorithm.  It returns a regexp denoting
  /// { cs | (c::cs) in r }.
  __attribute__((pure)) static regexp deriv(const regexp &r, const int64_t c);
  /// This calculates the derivative of a regular expression with respect to a
  /// string.
  __attribute__((pure)) static regexp derivs(regexp r, const List<int64_t> &cs);
  /// To see if cs matches r, calculate the derivative of r with respect
  /// to s, and see if the resulting regexp accepts the empty string.
  __attribute__((pure)) static bool deriv_parse(const regexp &r,
                                                const List<int64_t> &cs);
  /// null r returns Eps or Zero
  __attribute__((pure)) static bool NullEpsOrZero(const regexp &r);
  /// From this, we can build a decidable regexp matcher by running
  /// the derivative-based parser.
  __attribute__((pure)) static bool parse(const regexp &r,
                                          const List<int64_t> &cs);
  __attribute__((pure)) static bool parse_bool(const regexp &r,
                                               const List<int64_t> &cs);
  static inline const regexp r1 = regexp::cat(
      regexp::star(regexp::Char_(int64_t(0))), regexp::Char_(int64_t(1)));
  static inline const List<int64_t> s1 = List<int64_t>::cons(
      int64_t(0), List<int64_t>::cons(int64_t(1), List<int64_t>::nil()));
  static inline const List<int64_t> s2 =
      List<int64_t>::cons(int64_t(1), List<int64_t>::nil());
  static inline const List<int64_t> s3 = List<int64_t>::cons(
      int64_t(0),
      List<int64_t>::cons(
          int64_t(0), List<int64_t>::cons(int64_t(1), List<int64_t>::nil())));
  static inline const List<int64_t> s4 =
      List<int64_t>::cons(int64_t(0), List<int64_t>::nil());
};

#endif // INCLUDED_REGEXP
