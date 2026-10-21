#ifndef INCLUDED_INSTANCE_TVAR_SUBSTITUTION_ORDER
#define INCLUDED_INSTANCE_TVAR_SUBSTITUTION_ORDER

#include "crane_fn.h"
#include "obj.h"
#include <concepts>
#include <cstdint>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename I, typename A, typename B>
concept Conv = requires {
  { I::conv(std::declval<A>()) } -> std::convertible_to<B>;
};

struct InstanceTvarSubstitutionOrder {
  template <typename A> struct wrap {
    // DATA
    A a0;

    // ACCESSORS
    wrap<A> clone() const { return {a0}; }

    template <typename CraneU> operator wrap<CraneU>() const {
      return {[&]() -> CraneU {
        if constexpr (crane_convertible<CraneU, const A &>) {
          return crane_convert<CraneU>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }

    // CREATORS
    static wrap<A> w(A a0) { return {std::move(a0)}; }
  };

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, const T1 &>
  static T2 wrap_rect(F0 &&f, const wrap<T1> &w) {
    const auto &[a0] = w;
    return f(a0);
  }

  template <typename T1, typename T2, typename F0>
  static T2 wrap_rec(F0 &&f, const wrap<T1> &w) {
    return wrap_rect<T1, T2>(f, w);
  }

  template <typename T1> struct unw {
    static T1 conv(wrap<T1> w) {
      auto &[a0] = w;
      return std::move(a0);
    }
  };

  static inline const uint64_t result =
      unw<uint64_t>::conv(wrap<uint64_t>::w(UINT64_C(3)));
};

#endif // INCLUDED_INSTANCE_TVAR_SUBSTITUTION_ORDER
