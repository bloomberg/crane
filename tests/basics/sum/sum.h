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

    template <typename T1, MapsTo<T1, t_B> F0>
    std::shared_ptr<either<t_A, T1>> map_right(F0 &&f) const {
      return std::visit(
          Overloaded{[](const typename either<t_A, t_B>::Left _args)
                         -> std::shared_ptr<either<t_A, T1>> {
                       return either<t_A, T1>::ctor::Left_(_args.d_a0);
                     },
                     [&](const typename either<t_A, t_B>::Right _args)
                         -> std::shared_ptr<either<t_A, T1>> {
                       return either<t_A, T1>::ctor::Right_(f(_args.d_a0));
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0>
    std::shared_ptr<either<T1, t_B>> map_left(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename either<t_A, t_B>::Left _args)
                         -> std::shared_ptr<either<T1, t_B>> {
                       return either<T1, t_B>::ctor::Left_(f(_args.d_a0));
                     },
                     [](const typename either<t_A, t_B>::Right _args)
                         -> std::shared_ptr<either<T1, t_B>> {
                       return either<T1, t_B>::ctor::Right_(_args.d_a0);
                     }},
          this->v());
    }

    __attribute__((pure)) bool is_left() const {
      return std::visit(
          Overloaded{[](const typename either<t_A, t_B>::Left _args) -> bool {
                       return true;
                     },
                     [](const typename either<t_A, t_B>::Right _args) -> bool {
                       return false;
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename either<t_A, t_B>::Left _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename either<t_A, t_B>::Right _args) -> T1 {
                       return f0(_args.d_a0);
                     }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      return std::visit(
          Overloaded{[&](const typename either<t_A, t_B>::Left _args) -> T1 {
                       return f(_args.d_a0);
                     },
                     [&](const typename either<t_A, t_B>::Right _args) -> T1 {
                       return f0(_args.d_a0);
                     }},
          this->v());
    }
  };

  static inline const std::shared_ptr<either<unsigned int, bool>> left_val =
      either<unsigned int, bool>::ctor::Left_(5u);
  static inline const std::shared_ptr<either<unsigned int, bool>> right_val =
      either<unsigned int, bool>::ctor::Right_(true);
  __attribute__((pure)) static unsigned int
  either_to_nat(const std::shared_ptr<either<unsigned int, unsigned int>> &e);

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

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1,
              MapsTo<T1, t_C> F2>
    T1 triple_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{
              [&](const typename triple<t_A, t_B, t_C>::First _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Second _args) -> T1 {
                return f0(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Third _args) -> T1 {
                return f1(_args.d_a0);
              }},
          this->v());
    }

    template <typename T1, MapsTo<T1, t_A> F0, MapsTo<T1, t_B> F1,
              MapsTo<T1, t_C> F2>
    T1 triple_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      return std::visit(
          Overloaded{
              [&](const typename triple<t_A, t_B, t_C>::First _args) -> T1 {
                return f(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Second _args) -> T1 {
                return f0(_args.d_a0);
              },
              [&](const typename triple<t_A, t_B, t_C>::Third _args) -> T1 {
                return f1(_args.d_a0);
              }},
          this->v());
    }
  };

  static inline const std::shared_ptr<triple<unsigned int, bool, unsigned int>>
      triple_test =
          triple<unsigned int, bool, unsigned int>::ctor::Second_(true);
  static inline const bool test_left = left_val->is_left();
  static inline const bool test_right = right_val->is_left();
  static inline const unsigned int test_either =
      either_to_nat(either<unsigned int, unsigned int>::ctor::Left_(3u));
};

#endif // INCLUDED_SUM
