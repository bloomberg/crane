#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>
#include <variant>

struct LazyConversionOrigin {
  template <typename A> struct stream {
    // TYPES
    template <typename CraneS0 = stream<A>> struct SCons_ {
      A a0;
      CraneS0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    template <typename CraneU>
    stream(const stream<CraneU> &_other)
        : lazy_v_(
        crane::lazy<variant_t>::converted_from(
            _other.lazy_cell(), [=]() -> variant_t {
              const auto &[a0, a1] =
                  std::get<typename stream<CraneU>::SCons>(_other.v());
              return SCons{
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a0);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  crane_convert<stream<A>>(a1)};
            })) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream<A> scons(A a0, stream<A> a1) {
      return stream<A>(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, std::move(a0), std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream<A> lazy_(F &&thunk) {
      return stream<A>(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream<uint64_t> from(uint64_t n);

  template <typename T1, typename T2>
  static stream<T2> smap(const std::type_identity_t<crane::fn<T2(T1)>> &f,
                         const stream<T1> &s) {
    const auto &[a0, a1] = std::get<typename stream<T1>::SCons>(s.v());
    return stream<T2>::lazy_(
        [=, a0 = a0, f = f]() mutable -> typename stream<T2>::SCons {
          return {f(a0), smap<T1, T2>(f, a1)};
        });
  }

  template <typename T1> static T1 hd(const stream<T1> &s) {
    const auto &[a0, _] = std::get<typename stream<T1>::SCons>(s.v());
    return a0;
  }

  template <typename T1> static stream<T1> tl(const stream<T1> &s) {
    const auto &[_, a1] = std::get<typename stream<T1>::SCons>(s.v());
    return a1;
  }

  template <typename T1> static T1 nth(uint64_t n, const stream<T1> &s) {
    if (n <= 0) {
      return hd<T1>(s);
    } else {
      uint64_t m = n - 1;
      return nth<T1>(m, tl<T1>(s));
    }
  }

  static uint64_t doubled(uint64_t n);
};
