#ifndef INCLUDED_SUM
#define INCLUDED_SUM

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

struct Sum {
  template <typename t_A, typename t_B> struct either {
    // TYPES
    struct Left {
      t_A d_a0;
    };

    struct Right {
      t_B d_a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit either(Left _v) : d_v_(std::move(_v)) {}

    explicit either(Right _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<either<t_A, t_B>> Left_(t_A a0) {
        return std::shared_ptr<either<t_A, t_B>>(
            new either<t_A, t_B>(Left{a0}));
      }

      static std::shared_ptr<either<t_A, t_B>> Right_(t_B a0) {
        return std::shared_ptr<either<t_A, t_B>>(
            new either<t_A, t_B>(Right{a0}));
      }

      static std::unique_ptr<either<t_A, t_B>> Left_uptr(t_A a0) {
        return std::unique_ptr<either<t_A, t_B>>(
            new either<t_A, t_B>(Left{a0}));
      }

      static std::unique_ptr<either<t_A, t_B>> Right_uptr(t_B a0) {
        return std::unique_ptr<either<t_A, t_B>>(
            new either<t_A, t_B>(Right{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0,
            MapsTo<T3, T2> F1>
  static T3 either_rect(F0 &&f, F1 &&f0,
                        const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[&](const typename either<T1, T2>::Left _args) -> T3 {
                     T1 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     T2 b = _args.d_a0;
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
                     T1 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename either<T1, T2>::Right _args) -> T3 {
                     T2 b = _args.d_a0;
                     return f0(b);
                   }},
        e->v());
  }

  static inline const std::shared_ptr<either<unsigned int, bool>> left_val =
      either<unsigned int, bool>::ctor::Left_(5u);
  static inline const std::shared_ptr<either<unsigned int, bool>> right_val =
      either<unsigned int, bool>::ctor::Right_(true);
  __attribute__((pure)) static unsigned int
  either_to_nat(const std::shared_ptr<either<unsigned int, unsigned int>> &e);

  template <typename T1, typename T2>
  __attribute__((pure)) static bool
  is_left(const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(
        Overloaded{[](const typename either<T1, T2>::Left _args) -> bool {
                     return true;
                   },
                   [](const typename either<T1, T2>::Right _args) -> bool {
                     return false;
                   }},
        e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T1> F0>
  static std::shared_ptr<either<T3, T2>>
  map_left(F0 &&f, const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(Overloaded{[&](const typename either<T1, T2>::Left _args)
                                     -> std::shared_ptr<either<T3, T2>> {
                                   T1 a = _args.d_a0;
                                   return either<T3, T2>::ctor::Left_(f(a));
                                 },
                                 [](const typename either<T1, T2>::Right _args)
                                     -> std::shared_ptr<either<T3, T2>> {
                                   T2 b = _args.d_a0;
                                   return either<T3, T2>::ctor::Right_(b);
                                 }},
                      e->v());
  }

  template <typename T1, typename T2, typename T3, MapsTo<T3, T2> F0>
  static std::shared_ptr<either<T1, T3>>
  map_right(F0 &&f, const std::shared_ptr<either<T1, T2>> &e) {
    return std::visit(Overloaded{[](const typename either<T1, T2>::Left _args)
                                     -> std::shared_ptr<either<T1, T3>> {
                                   T1 a = _args.d_a0;
                                   return either<T1, T3>::ctor::Left_(a);
                                 },
                                 [&](const typename either<T1, T2>::Right _args)
                                     -> std::shared_ptr<either<T1, T3>> {
                                   T2 b = _args.d_a0;
                                   return either<T1, T3>::ctor::Right_(f(b));
                                 }},
                      e->v());
  }

  template <typename t_A, typename t_B, typename t_C> struct triple {
    // TYPES
    struct First {
      t_A d_a0;
    };

    struct Second {
      t_B d_a0;
    };

    struct Third {
      t_C d_a0;
    };

    using variant_t = std::variant<First, Second, Third>;

  private:
    // DATA
    variant_t d_v_;

    // CREATORS
    explicit triple(First _v) : d_v_(std::move(_v)) {}

    explicit triple(Second _v) : d_v_(std::move(_v)) {}

    explicit triple(Third _v) : d_v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<triple<t_A, t_B, t_C>> First_(t_A a0) {
        return std::shared_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(First{a0}));
      }

      static std::shared_ptr<triple<t_A, t_B, t_C>> Second_(t_B a0) {
        return std::shared_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(Second{a0}));
      }

      static std::shared_ptr<triple<t_A, t_B, t_C>> Third_(t_C a0) {
        return std::shared_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(Third{a0}));
      }

      static std::unique_ptr<triple<t_A, t_B, t_C>> First_uptr(t_A a0) {
        return std::unique_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(First{a0}));
      }

      static std::unique_ptr<triple<t_A, t_B, t_C>> Second_uptr(t_B a0) {
        return std::unique_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(Second{a0}));
      }

      static std::unique_ptr<triple<t_A, t_B, t_C>> Third_uptr(t_C a0) {
        return std::unique_ptr<triple<t_A, t_B, t_C>>(
            new triple<t_A, t_B, t_C>(Third{a0}));
      }
    };

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T4, T1> F0, MapsTo<T4, T2> F1, MapsTo<T4, T3> F2>
  static T4 triple_rect(F0 &&f, F1 &&f0, F2 &&f1,
                        const std::shared_ptr<triple<T1, T2, T3>> &t) {
    return std::visit(
        Overloaded{[&](const typename triple<T1, T2, T3>::First _args) -> T4 {
                     T1 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename triple<T1, T2, T3>::Second _args) -> T4 {
                     T2 b = _args.d_a0;
                     return f0(b);
                   },
                   [&](const typename triple<T1, T2, T3>::Third _args) -> T4 {
                     T3 c = _args.d_a0;
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
                     T1 a = _args.d_a0;
                     return f(a);
                   },
                   [&](const typename triple<T1, T2, T3>::Second _args) -> T4 {
                     T2 b = _args.d_a0;
                     return f0(b);
                   },
                   [&](const typename triple<T1, T2, T3>::Third _args) -> T4 {
                     T3 c = _args.d_a0;
                     return f1(c);
                   }},
        t->v());
  }

  static inline const std::shared_ptr<triple<unsigned int, bool, unsigned int>>
      triple_test =
          triple<unsigned int, bool, unsigned int>::ctor::Second_(true);
  static inline const bool test_left = is_left<unsigned int, bool>(left_val);
  static inline const bool test_right = is_left<unsigned int, bool>(right_val);
  static inline const unsigned int test_either =
      either_to_nat(either<unsigned int, unsigned int>::ctor::Left_(3u));
};

#endif // INCLUDED_SUM
