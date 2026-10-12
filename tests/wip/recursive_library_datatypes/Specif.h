#ifndef INCLUDED_SPECIF
#define INCLUDED_SPECIF

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

template <typename A> struct Sig;
template <typename A> struct Sig2;
template <typename A, typename P> struct SigT;
template <typename A, typename P, typename Q> struct SigT2;
template <typename A> struct Sumor;

struct SigTNotations {};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  sig<A> clone() const { return {x}; }

  template <typename CraneU> operator sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static sig<A> exist(A x) { return {std::move(x)}; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  T1 sig_rect(F0 &&f) const {
    const auto &[x0] = *this;
    return f(x0);
  }

  template <typename T1, typename F0> T1 sig_rec(F0 &&f) const {
    return this->template sig_rect<T1>(f);
  }

  A proj1_sig() const {
    const auto &[x] = *this;
    return x;
  }

  template <typename T1> T1 eq_sig_rect(const sig<A> &, const T1 &f) const {
    return f;
  }

  template <typename T1> T1 eq_sig_rec(const sig<A> &x1_, const T1 &x2_) const {
    return this->template eq_sig_rect<T1>(x1_, x2_);
  }

  template <typename T1>
  T1 eq_sig_rect_exist_l(const A &u1, const T1 &f) const {
    return sig<A>::exist(u1).template eq_sig_rect<T1>(*this, f);
  }

  template <typename T1>
  T1 eq_sig_rect_exist_r(const A &v1, const T1 &f) const {
    return this->template eq_sig_rect<T1>(sig<A>::exist(v1), f);
  }

  template <typename T1> T1 eq_sig_rect_uncurried(const sig<A> &v, T1 f) const {
    return this->template eq_sig_rect<T1>(v, [=]() { return f; }());
  }

  template <typename T1>
  T1 eq_sig_rec_uncurried(const sig<A> &x1_, T1 x2_) const {
    return this->template eq_sig_rect_uncurried<T1>(x1_, std::move(x2_));
  }
};

template <typename A> struct Sig2 {
  // DATA
  A x;

  // ACCESSORS
  sig2<A> clone() const { return {x}; }

  template <typename CraneU> operator sig2<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static sig2<A> exist2(A x) { return {std::move(x)}; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  T1 sig2_rect(F0 &&f) const {
    const auto &[x0] = *this;
    return f(x0);
  }

  template <typename T1, typename F0> T1 sig2_rec(F0 &&f) const {
    return this->template sig2_rect<T1>(f);
  }

  sig<A> sig_of_sig2() const {
    return sig<A>::exist([&]() {
      const auto &[x0] = *this;
      return x0;
    }());
  }

  template <typename T1> T1 eq_sig2_rect(const sig2<A> &, const T1 &f) const {
    return f;
  }

  template <typename T1>
  T1 eq_sig2_rec(const sig2<A> &x1_, const T1 &x2_) const {
    return this->template eq_sig2_rect<T1>(x1_, x2_);
  }

  template <typename T1>
  T1 eq_sig2_rect_exist2_l(const A &u1, const T1 &f) const {
    return sig2<A>::exist2(u1).template eq_sig2_rect<T1>(*this, f);
  }

  template <typename T1>
  T1 eq_sig2_rect_exist2_r(const A &v1, const T1 &f) const {
    return this->template eq_sig2_rect<T1>(sig2<A>::exist2(v1), f);
  }

  template <typename T1>
  T1 eq_sig2_rect_uncurried(const sig2<A> &v, T1 f) const {
    return this->template eq_sig2_rect<T1>(v, [=]() { return f; }());
  }

  template <typename T1>
  T1 eq_sig2_rec_uncurried(const sig2<A> &x1_, T1 x2_) const {
    return this->template eq_sig2_rect_uncurried<T1>(x1_, std::move(x2_));
  }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  sigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator sigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static sigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &, const P &>
  T1 sigT_rect(F0 &&f) const {
    const auto &[x0, a1] = *this;
    return f(x0, a1);
  }

  template <typename T1, typename F0> T1 sigT_rec(F0 &&f) const {
    return this->template sigT_rect<T1>(f);
  }

  A projT1() const {
    const auto &[x0, a1] = *this;
    return x0;
  }

  P projT2() const {
    const auto &[x0, a1] = *this;
    return a1;
  }

  sig<A> sig_of_sigT() const { return sig<A>::exist(this->projT1()); }

  std::pair<A, P> prod_of_sigT() const {
    return std::make_pair(this->projT1(), this->projT2());
  }

  template <typename T1>
  T1 eq_sigT_rect(const sigT<A, P> &, const T1 &f) const {
    return f;
  }

  template <typename T1>
  T1 eq_sigT_rec(const sigT<A, P> &x1_, const T1 &x2_) const {
    return this->template eq_sigT_rect<T1>(x1_, x2_);
  }

  template <typename T1>
  T1 eq_sigT_rect_existT_l(const A &u1, const P &u2, const T1 &f) const {
    return sigT<A, P>::existt(u1, u2).template eq_sigT_rect<T1>(*this, f);
  }

  template <typename T1>
  T1 eq_sigT_rect_existT_r(const A &v1, const P &v2, const T1 &f) const {
    return this->template eq_sigT_rect<T1>(sigT<A, P>::existt(v1, v2), f);
  }

  template <typename T1>
  T1 eq_sigT_rect_uncurried(const sigT<A, P> &v, T1 f) const {
    return this->template eq_sigT_rect<T1>(v, [=]() { return f; }());
  }

  template <typename T1>
  T1 eq_sigT_rec_uncurried(const sigT<A, P> &x1_, T1 x2_) const {
    return this->template eq_sigT_rect_uncurried<T1>(x1_, std::move(x2_));
  }
};

template <typename A, typename P, typename Q> struct SigT2 {
  // DATA
  A x;
  P a1;
  Q a2;

  // ACCESSORS
  sigT2<A, P, Q> clone() const { return {x, a1, a2}; }

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  operator sigT2<CraneU0, CraneU1, CraneU2>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU2 {
              if constexpr (crane_convertible<CraneU2, const Q &>) {
                return crane_convert<CraneU2>(a2);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static sigT2<A, P, Q> existt2(A x, P a1, Q a2) {
    return {std::move(x), std::move(a1), std::move(a2)};
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &, const P &, const Q &>
  T1 sigT2_rect(F0 &&f) const {
    const auto &[x0, a1, a2] = *this;
    return f(x0, a1, a2);
  }

  template <typename T1, typename F0> T1 sigT2_rec(F0 &&f) const {
    return this->template sigT2_rect<T1>(f);
  }

  sigT<A, P> sigT_of_sigT2() const {
    return sigT<A, P>::existt(
        [&]() {
          const auto &[x0, a1, a2] = *this;
          return x0;
        }(),
        [&]() {
          const auto &[x0, a10, a20] = *this;
          return a10;
        }());
  }

  Q projT3() const {
    const auto &[x, a1, a2] = *this;
    return a2;
  }

  sig2<A> sig2_of_sigT2() const {
    return sig2<A>::exist2(this->sigT_of_sigT2().projT1());
  }

  template <typename T1>
  T1 eq_sigT2_rect(const sigT2<A, P, Q> &, const T1 &f) const {
    return f;
  }

  template <typename T1>
  T1 eq_sigT2_rec(const sigT2<A, P, Q> &x1_, const T1 &x2_) const {
    return this->template eq_sigT2_rect<T1>(x1_, x2_);
  }

  template <typename T1>
  T1 eq_sigT2_rect_existT2_l(const A &u1, const P &u2, const Q &u3,
                             const T1 &f) const {
    return sigT2<A, P, Q>::existt2(u1, u2, u3)
        .template eq_sigT2_rect<T1>(*this, f);
  }

  template <typename T1>
  T1 eq_sigT2_rect_existT2_r(const A &v1, const P &v2, const Q &v3,
                             const T1 &f) const {
    return this->template eq_sigT2_rect<T1>(sigT2<A, P, Q>::existt2(v1, v2, v3),
                                            f);
  }

  template <typename T1>
  T1 eq_sigT2_rect_uncurried(const sigT2<A, P, Q> &v, T1 f) const {
    return this->template eq_sigT2_rect<T1>(v, [=]() { return f; }());
  }

  template <typename T1>
  T1 eq_sigT2_rec_uncurried(const sigT2<A, P, Q> &x1_, T1 x2_) const {
    return this->template eq_sigT2_rect_uncurried<T1>(x1_, std::move(x2_));
  }
};

template <typename T1> sigT<T1, crane::obj> sigT_of_sig(const sig<T1> &x) {
  return sigT<T1, crane::obj>::existt(
      [&]() {
        const auto &[x0] = x;
        return x0;
      }(),
      crane::obj());
}

template <typename T1>
sigT2<T1, crane::obj, crane::obj> sigT2_of_sig2(const sig2<T1> &x) {
  return sigT2<T1, crane::obj, crane::obj>::existt2(
      [&]() {
        const auto &_sv = x.sig_of_sig2();
        const auto &[x0] = _sv;
        return x0;
      }(),
      crane::obj(), crane::obj());
}

template <typename T1, typename T2>
sigT<T1, T2> sigT_of_prod(const std::pair<T1, T2> &p) {
  return sigT<T1, T2>::existt(p.first, p.second);
}

template <typename T1, typename T2, typename T3>
T3 eq_sigT_rect_existT(const T1 &u1, const T2 &u2, const T1 &v1, const T2 &v2,
                       const T3 &f) {
  return sigT<T1, T2>::existt(u1, u2).template eq_sigT_rect<T3>(
      sigT<T1, T2>::existt(v1, v2), f);
}

template <typename T1, typename T2>
T2 eq_sig_rect_exist(const T1 &u1, const T1 &v1, const T2 &f) {
  return sig<T1>::exist(u1).template eq_sig_rect<T2>(sig<T1>::exist(v1), f);
}

template <typename T1, typename T2, typename T3, typename T4>
T4 eq_sigT2_rect_existT2(const T1 &u1, const T2 &u2, const T3 &u3, const T1 &v1,
                         const T2 &v2, const T3 &v3, const T4 &f) {
  return sigT2<T1, T2, T3>::existt2(u1, u2, u3)
      .template eq_sigT2_rect<T4>(sigT2<T1, T2, T3>::existt2(v1, v2, v3), f);
}

template <typename T1, typename T2>
T2 eq_sig2_rect_exist2(const T1 &u1, const T1 &v1, const T2 &f) {
  return sig2<T1>::exist2(u1).template eq_sig2_rect<T2>(sig2<T1>::exist2(v1),
                                                        f);
}

template <typename T1> T1 sumbool_rect(const T1 &f, const T1 &f0, bool s) {
  if (s) {
    return f;
  } else {
    return f0;
  }
}

template <typename T1> T1 sumbool_rec(const T1 &f, const T1 &f0, bool s) {
  return sumbool_rect<T1>(f, f0, s);
}

template <typename A> struct Sumor {
  // TYPES
  struct Inleft {
    A a0;
  };

  struct Inright {};

  using variant_t = std::variant<Inleft, Inright>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Sumor() {}

  explicit Sumor(Inleft _v) : v_(std::move(_v)) {}

  explicit Sumor(Inright _v) : v_(_v) {}

  template <typename CraneU>
  Sumor(const sumor<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename sumor<CraneU>::Inleft>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename sumor<CraneU>::Inleft>(_other.v());
            return Inleft{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return Inright{};
          }
        }()) {}

  static sumor<A> inleft(A a0) { return sumor<A>(Inleft{std::move(a0)}); }

  static sumor<A> inright() { return sumor<A>(Inright{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  T1 sumor_rect(F0 &&f, const T1 &f0) const {
    if (std::holds_alternative<typename sumor<A>::Inleft>(this->v())) {
      const auto &[a0] = std::get<typename sumor<A>::Inleft>(this->v());
      return f(a0);
    } else {
      return f0;
    }
  }

  template <typename T1, typename F0> T1 sumor_rec(F0 &&f, const T1 &f0) const {
    return this->template sumor_rect<T1>(f, f0);
  }
};

template <typename T1, typename T2>
sig<crane::fn<T2(T1)>> Choice(std::type_identity_t<crane::fn<sig<T2>(T1)>> h) {
  return sig<crane::fn<T2(T1)>>::exist([=](const T1 &z) {
    const auto &_sv = h(z);
    const auto &[x] = _sv;
    return x;
  });
}

template <typename T1, typename T2, typename T3>
sigT<crane::fn<T2(T1)>, crane::fn<T3(T1)>>
Choice2(std::type_identity_t<crane::fn<sigT<T2, T3>(T1)>> h) {
  return sigT<crane::fn<T2(T1)>, crane::fn<T3(T1)>>::existt(
      [=](const T1 &z) { return h(z).projT1(); },
      [=](const T1 &z) {
        sigT<T2, T3> s = h(z);
        auto &[x, a1] = s;
        return a1;
      });
}

template <typename T1>
sig<crane::fn<bool(T1)>>
bool_choice(std::type_identity_t<crane::fn<bool(T1)>> h) {
  return sig<crane::fn<bool(T1)>>::exist([=](const T1 &z) {
    if (h(z)) {
      return true;
    } else {
      return false;
    }
  });
}

template <typename T1>
sig<crane::fn<T1(uint64_t)>>
dependent_choice(std::type_identity_t<crane::fn<sig<T1>(T1)>> h, T1 x0) {
  auto f_impl = [=, x0 = std::move(x0)](auto &_self_f, uint64_t n) -> T1 {
    if (n <= 0) {
      return x0;
    } else {
      uint64_t n_ = n - 1;
      const auto &_sv = h(_self_f(_self_f, n_));
      const auto &[x] = _sv;
      return x;
    }
  };
  auto f = [=, f_impl = std::move(f_impl)](uint64_t n) -> T1 {
    return f_impl(f_impl, n);
  };
  return sig<crane::fn<T1(uint64_t)>>::exist(std::move(f));
}

template <typename a> using Exc = std::optional<a>;

template <typename T1> std::optional<T1> value(const T1 &x) {
  return std::make_optional<T1>(x);
}

template <typename T1> const std::optional<T1> error = std::optional<T1>();

template <typename T1> T1 except() { throw std::logic_error("absurd case"); }

template <typename T1>
const T1 absurd_set = [](crane::obj) {
  throw std::logic_error("untranslatable curried proof term");
};

#endif // INCLUDED_SPECIF
