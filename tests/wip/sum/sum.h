#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Bool0 {
  struct bool0 {
  public:
    struct true0 {};
    struct false0 {};
    using variant_t = std::variant<true0, false0>;

  private:
    variant_t v_;
    explicit bool0(true0 _v) : v_(std::move(_v)) {}
    explicit bool0(false0 _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<Bool0::bool0> true0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(true0{}));
      }
      static std::shared_ptr<Bool0::bool0> false0_() {
        return std::shared_ptr<Bool0::bool0>(new Bool0::bool0(false0{}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

struct Sum {
  template <typename A, typename B> struct either {
  public:
    struct Left {
      A _a0;
    };
    struct Right {
      B _a0;
    };
    using variant_t = std::variant<Left, Right>;

  private:
    variant_t v_;
    explicit either(Left _v) : v_(std::move(_v)) {}
    explicit either(Right _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<either<A, B>> Left_(A a0) {
        return std::shared_ptr<either<A, B>>(new either<A, B>(Left{a0}));
      }
      static std::shared_ptr<either<A, B>> Right_(B a0) {
        return std::shared_ptr<either<A, B>>(new either<A, B>(Right{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rect(F0 &&f, F1 &&f0,
                        const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     T2 b = _args._a0;
                     return f0(b);
                   }},
        e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rec(F0 &&f, F1 &&f0,
                       const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     T2 b = _args._a0;
                     return f0(b);
                   }},
        e->v());
  }

  static inline const std::shared_ptr<
      either<unsigned int, std::shared_ptr<Bool0::bool0>>>
      left_val =
          either<unsigned int, std::shared_ptr<Bool0::bool0>>::ctor::Left_(5u);

  static inline const std::shared_ptr<
      either<unsigned int, std::shared_ptr<Bool0::bool0>>>
      right_val =
          either<unsigned int, std::shared_ptr<Bool0::bool0>>::ctor::Right_(
              Bool0::bool0::ctor::true0_());

  static unsigned int
  either_to_nat(const std::shared_ptr<either<unsigned int, unsigned int>> &e);

  template <typename T1, typename T2>
  static std::shared_ptr<Bool0::bool0>
  is_left(const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(Overloaded{[](const typename either<T1, T2>::Left _args)
                                     -> std::shared_ptr<Bool0::bool0> {
                                   return Bool0::bool0::ctor::true0_();
                                 },
                                 [](const typename either<T1, T2>::Right _args)
                                     -> std::shared_ptr<Bool0::bool0> {
                                   return Bool0::bool0::ctor::false0_();
                                 }},
                      e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0>
  static std::shared_ptr<either<T3, T2>>
  map_left(F0 &&f, const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(Overloaded{[&](const typename either<T1, T2>::Left _args)
                                     -> std::shared_ptr<either<T3, T2>> {
                                   T1 a = _args._a0;
                                   return either<T3, T2>::ctor::Left_(f(a));
                                 },
                                 [](const typename either<T1, T2>::Right _args)
                                     -> std::shared_ptr<either<T3, T2>> {
                                   T2 b = _args._a0;
                                   return either<T3, T2>::ctor::Right_(b);
                                 }},
                      e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T2> F0>
  static std::shared_ptr<either<T1, T3>>
  map_right(F0 &&f, const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(Overloaded{[](const typename either<T1, T2>::Left _args)
                                     -> std::shared_ptr<either<T1, T3>> {
                                   T1 a = _args._a0;
                                   return either<T1, T3>::ctor::Left_(a);
                                 },
                                 [&](const typename either<T1, T2>::Right _args)
                                     -> std::shared_ptr<either<T1, T3>> {
                                   T2 b = _args._a0;
                                   return either<T1, T3>::ctor::Right_(f(b));
                                 }},
                      e->v());
  }

  template <typename A, typename B, typename C> struct triple {
  public:
    struct First {
      A _a0;
    };
    struct Second {
      B _a0;
    };
    struct Third {
      C _a0;
    };
    using variant_t = std::variant<First, Second, Third>;

  private:
    variant_t v_;
    explicit triple(First _v) : v_(std::move(_v)) {}
    explicit triple(Second _v) : v_(std::move(_v)) {}
    explicit triple(Third _v) : v_(std::move(_v)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<triple<A, B, C>> First_(A a0) {
        return std::shared_ptr<triple<A, B, C>>(new triple<A, B, C>(First{a0}));
      }
      static std::shared_ptr<triple<A, B, C>> Second_(B a0) {
        return std::shared_ptr<triple<A, B, C>>(
            new triple<A, B, C>(Second{a0}));
      }
      static std::shared_ptr<triple<A, B, C>> Third_(C a0) {
        return std::shared_ptr<triple<A, B, C>>(new triple<A, B, C>(Third{a0}));
      }
    };
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1> F0, MapsTo<T4, T2> F1, MapsTo<T4, T3> F2>
  static T4 triple_rect(F0 &&f, F1 &&f0, F2 &&f1,
                        const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::First _args) -> T4 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename triple<T1, T2, T3>::Second _args) -> T4 {
                     T2 b = _args._a0;
                     return f0(b);
                   },
                   [&](const typename triple<T1, T2, T3>::Third _args) -> T4 {
                     T3 c = _args._a0;
                     return f1(c);
                   }},
        t->v());
  }

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1> F0, MapsTo<T4, T2> F1, MapsTo<T4, T3> F2>
  static T4 triple_rec(F0 &&f, F1 &&f0, F2 &&f1,
                       const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::First _args) -> T4 {
                     T1 a = _args._a0;
                     return f(a);
                   },
                   [&](const typename triple<T1, T2, T3>::Second _args) -> T4 {
                     T2 b = _args._a0;
                     return f0(b);
                   },
                   [&](const typename triple<T1, T2, T3>::Third _args) -> T4 {
                     T3 c = _args._a0;
                     return f1(c);
                   }},
        t->v());
  }

  static inline const std::shared_ptr<
      triple<unsigned int, std::shared_ptr<Bool0::bool0>, unsigned int>>
      triple_test =
          triple<unsigned int, std::shared_ptr<Bool0::bool0>,
                 unsigned int>::ctor::Second_(Bool0::bool0::ctor::true0_());

  static inline const std::shared_ptr<Bool0::bool0> test_left =
      is_left<unsigned int, std::shared_ptr<Bool0::bool0>>(left_val);

  static inline const std::shared_ptr<Bool0::bool0> test_right =
      is_left<unsigned int, std::shared_ptr<Bool0::bool0>>(right_val);

  static inline const unsigned int test_either =
      either_to_nat(either<unsigned int, unsigned int>::ctor::Left_(3u));
};
