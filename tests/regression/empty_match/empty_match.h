#ifndef INCLUDED_EMPTY_MATCH
#define INCLUDED_EMPTY_MATCH

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct EmptyMatch {
  struct empty {
    empty() = delete;
  };

  template <typename T1> static T1 empty_rect(const empty &) {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 empty_rec(const empty &_x) {
    return empty_rect<T1>(_x);
  }

  template <typename T1> static T1 absurd(const empty &_x) {
    return empty_rect<T1>(_x);
  }

  static uint64_t from_empty(const empty &x0_);

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
  };

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
    requires std::is_invocable_r_v<T3, F0 &, const T1 &> &&
             std::is_invocable_r_v<T3, F1 &, const T2 &>
  static T3 either_rect(F0 &&f, F1 &&f0, const either<T1, T2> &e) {
    if (std::holds_alternative<typename either<T1, T2>::Left>(e.v())) {
      const auto &[a0] = std::get<typename either<T1, T2>::Left>(e.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename either<T1, T2>::Right>(e.v());
      return f0(a0);
    }
  }

  template <typename T1, typename T2, typename T3, typename F0, typename F1>
  static T3 either_rec(F0 &&f, F1 &&f0, const either<T1, T2> &e) {
    return either_rect<T1, T2, T3>(f, f0, e);
  }

  template <typename T1> static T1 handle_left(const either<T1, empty> &e) {
    if (std::holds_alternative<typename either<T1, empty>::Left>(e.v())) {
      const auto &[a0] = std::get<typename either<T1, empty>::Left>(e.v());
      return a0;
    } else {
      const auto &[a0] = std::get<typename either<T1, empty>::Right>(e.v());
      return absurd<T1>(a0);
    }
  }

  static inline const either<uint64_t, empty> test_either =
      either<uint64_t, empty>::left(UINT64_C(5));
  static inline const uint64_t test_handle = handle_left<uint64_t>(test_either);

  template <typename T1, typename T2>
  static either<T1, T2> complex_absurd(const empty &) {
    throw std::logic_error("absurd case");
  }
};

#endif // INCLUDED_EMPTY_MATCH
