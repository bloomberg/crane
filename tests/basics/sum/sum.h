#ifndef INCLUDED_SUM
#define INCLUDED_SUM

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Sum {
  template <typename A, typename B> struct either {
    // TYPES
    struct Left {
      A a0;
    };

    struct Right {
      B a0;
    };

    using variant_t = std::variant<Left, Right>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    either() {}

    explicit either(Left _v) : v_(std::move(_v)) {}

    explicit either(Right _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1>
    either(const either<CraneU0, CraneU1> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename either<CraneU0, CraneU1>::Left>(
                    _other.v())) {
              const auto &[a0] =
                  std::get<typename either<CraneU0, CraneU1>::Left>(_other.v());
              return Left{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU0 &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              const auto &[a0] =
                  std::get<typename either<CraneU0, CraneU1>::Right>(
                      _other.v());
              return Right{[&]() -> B {
                if constexpr (crane_convertible<B, const CraneU1 &>) {
                  return crane_convert<B>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            }
          }()) {}

    static either<A, B> left(A a0) { return either<A, B>(Left{std::move(a0)}); }

    static either<A, B> right(B a0) {
      return either<A, B>(Right{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const B &>
    either<A, T1> map_right(F0 &&f) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return either<A, T1>::left(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return either<A, T1>::right(f(a0));
      }
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, const A &>
    either<T1, B> map_left(F0 &&f) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return either<T1, B>::left(f(a0));
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return either<T1, B>::right(a0);
      }
    }

    bool is_left() const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        return true;
      } else {
        return false;
      }
    }

    template <typename T1, typename F0, typename F1>
    T1 either_rec(F0 &&f, F1 &&f0) const {
      return this->template either_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const A &> &&
               std::is_invocable_r_v<T1, F1 &, const B &>
    T1 either_rect(F0 &&f, F1 &&f0) const {
      if (std::holds_alternative<typename either<A, B>::Left>(this->v())) {
        const auto &[a0] = std::get<typename either<A, B>::Left>(this->v());
        return f(a0);
      } else {
        const auto &[a0] = std::get<typename either<A, B>::Right>(this->v());
        return f0(a0);
      }
    }
  };

  static inline const either<uint64_t, bool> left_val =
      either<uint64_t, bool>::left(UINT64_C(5));
  static inline const either<uint64_t, bool> right_val =
      either<uint64_t, bool>::right(true);
  static uint64_t either_to_nat(const either<uint64_t, uint64_t> &e);

  template <typename A, typename B, typename C> struct triple {
    // TYPES
    struct First {
      A a0;
    };

    struct Second {
      B a0;
    };

    struct Third {
      C a0;
    };

    using variant_t = std::variant<First, Second, Third>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    triple() {}

    explicit triple(First _v) : v_(std::move(_v)) {}

    explicit triple(Second _v) : v_(std::move(_v)) {}

    explicit triple(Third _v) : v_(std::move(_v)) {}

    template <typename CraneU0, typename CraneU1, typename CraneU2>
    triple(const triple<CraneU0, CraneU1, CraneU2> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<
                    typename triple<CraneU0, CraneU1, CraneU2>::First>(
                    _other.v())) {
              const auto &[a0] =
                  std::get<typename triple<CraneU0, CraneU1, CraneU2>::First>(
                      _other.v());
              return First{[&]() -> A {
                if constexpr (crane_convertible<A, const CraneU0 &>) {
                  return crane_convert<A>(a0);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }()};
            } else {
              if (std::holds_alternative<
                      typename triple<CraneU0, CraneU1, CraneU2>::Second>(
                      _other.v())) {
                const auto &[a0] = std::get<
                    typename triple<CraneU0, CraneU1, CraneU2>::Second>(
                    _other.v());
                return Second{[&]() -> B {
                  if constexpr (crane_convertible<B, const CraneU1 &>) {
                    return crane_convert<B>(a0);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
              } else {
                const auto &[a0] =
                    std::get<typename triple<CraneU0, CraneU1, CraneU2>::Third>(
                        _other.v());
                return Third{[&]() -> C {
                  if constexpr (crane_convertible<C, const CraneU2 &>) {
                    return crane_convert<C>(a0);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }()};
              }
            }
          }()) {}

    static triple<A, B, C> first(A a0) {
      return triple<A, B, C>(First{std::move(a0)});
    }

    static triple<A, B, C> second(B a0) {
      return triple<A, B, C>(Second{std::move(a0)});
    }

    static triple<A, B, C> third(C a0) {
      return triple<A, B, C>(Third{std::move(a0)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F0, typename F1, typename F2>
    T1 triple_rec(F0 &&f, F1 &&f0, F2 &&f1) const {
      return this->template triple_rect<T1>(f, f0, f1);
    }

    template <typename T1, typename F0, typename F1, typename F2>
      requires std::is_invocable_r_v<T1, F0 &, const A &> &&
               std::is_invocable_r_v<T1, F1 &, const B &> &&
               std::is_invocable_r_v<T1, F2 &, const C &>
    T1 triple_rect(F0 &&f, F1 &&f0, F2 &&f1) const {
      if (std::holds_alternative<typename triple<A, B, C>::First>(this->v())) {
        const auto &[a0] = std::get<typename triple<A, B, C>::First>(this->v());
        return f(a0);
      } else if (std::holds_alternative<typename triple<A, B, C>::Second>(
                     this->v())) {
        const auto &[a0] =
            std::get<typename triple<A, B, C>::Second>(this->v());
        return f0(a0);
      } else {
        const auto &[a0] = std::get<typename triple<A, B, C>::Third>(this->v());
        return f1(a0);
      }
    }
  };

  static inline const triple<uint64_t, bool, uint64_t> triple_test =
      triple<uint64_t, bool, uint64_t>::second(true);
  static constexpr bool test_left = true;
  static constexpr bool test_right = false;
  static constexpr uint64_t test_either = UINT64_C(3);
};

#endif // INCLUDED_SUM
