#ifndef INCLUDED_RC_POLICY_NAMES_EVERY_BLOCK
#define INCLUDED_RC_POLICY_NAMES_EVERY_BLOCK

#include <any>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "rc.h"

template <typename A, typename P> struct SigT;

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

struct RcPolicyNamesEveryBlock {
  struct stream {
    // TYPES
    template <typename _S0 = stream> struct SCons_ {
      uint64_t a0;
      _S0 a1;
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
      return stream(SCons{a0, std::move(a1)});
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream from(uint64_t n);
  static uint64_t hd(stream s);

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t twice(F0 &&f, uint64_t x) {
    return f(f(x));
  }

  static inline const SigT<crane::obj, crane::obj> boxed =
      SigT<crane::obj, crane::obj>::existt(crane::obj(), UINT64_C(3));
};

#endif // INCLUDED_RC_POLICY_NAMES_EVERY_BLOCK
