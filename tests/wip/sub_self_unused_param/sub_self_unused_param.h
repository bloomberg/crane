#pragma once

#include "fn.h"
#include "lazy.h"
#include <cstdint>
#include <type_traits>
#include <utility>
#include <variant>

struct SubSelfUnusedParam {
  struct box {
    // DATA
    uint64_t n;

    // ACCESSORS
    box clone() const { return {n}; }

    // CREATORS
    static box box0(uint64_t n) { return {n}; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 box_rect(F0 &&f, const box &b) {
    const auto &[n0] = b;
    return f(n0);
  }

  template <typename T1, typename F0> static T1 box_rec(F0 &&f, const box &b) {
    return box_rect<T1>(f, b);
  }

  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct SCons_ {
      uint64_t a0;
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

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream sconst(uint64_t n);
  static uint64_t on_box(const box &b);
  static uint64_t on_stream(const stream &s);
  static uint64_t in_branch(bool c, const box &b);
  static inline const uint64_t result =
      ((on_box(box::box0(UINT64_C(5))) + on_stream(sconst(UINT64_C(3)))) +
       in_branch(false, box::box0(UINT64_C(5))));
};
