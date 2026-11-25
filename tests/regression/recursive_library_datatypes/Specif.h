#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

namespace Specif {
template <typename A, typename P> struct SigT;
template <typename A, typename P, typename Q> struct SigT2;
template <typename A> struct Sumor;

struct SigTNotations {};

template <typename T1, typename T2, typename F0>
T2 sig_rect(F0 &&f, const T1 &s) {
  // Precondition: P
  const T1 &x = s;
  return f(x);
}

template <typename T1, typename T2, typename F0>
T2 sig_rec(F0 &&f, const T1 &s) {
  // Precondition: P
  return sig_rect<T1, T2>(f, s);
}

template <typename T1, typename T2, typename F0>
T2 sig2_rect(F0 &&f, const T1 &s) {
  const T1 &x = s;
  return f(x);
}

template <typename T1, typename T2, typename F0>
T2 sig2_rec(F0 &&f, const T1 &s) {
  return sig2_rect<T1, T2>(f, s);
}

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
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
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }

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
    const auto &[x0, _] = *this;
    return x0;
  }

  P projT2() const {
    const auto &[_, a1] = *this;
    return a1;
  }

  A sig_of_sigT() const { return this->projT1(); }

  std::pair<A, P> prod_of_sigT() const {
    return std::make_pair(this->projT1(), this->projT2());
  }

  template <typename T1>
  T1 eq_sigT_rect(const SigT<A, P> &, const T1 &f) const {
    return f;
  }

  template <typename T1>
  T1 eq_sigT_rec(const SigT<A, P> &x1_, const T1 &x2_) const {
    return this->template eq_sigT_rect<T1>(x1_, x2_);
  }

  template <typename T1>
  T1 eq_sigT_rect_existT_l(const A &u1, const P &u2, const T1 &f) const {
    return SigT<A, P>::existt(u1, u2).template eq_sigT_rect<T1>(*this, f);
  }

  template <typename T1>
  T1 eq_sigT_rect_existT_r(const A &v1, const P &v2, const T1 &f) const {
    return this->template eq_sigT_rect<T1>(SigT<A, P>::existt(v1, v2), f);
  }

  template <typename T1>
  T1 eq_sigT_rect_uncurried(const SigT<A, P> &v, T1 f) const {
    return this->template eq_sigT_rect<T1>(
        v, [=, f = std::move(f)]() { return f; }());
  }

  template <typename T1>
  T1 eq_sigT_rec_uncurried(const SigT<A, P> &x1_, T1 x2_) const {
    return this->template eq_sigT_rect_uncurried<T1>(x1_, std::move(x2_));
  }
};

template <typename A, typename P, typename Q> struct SigT2 {
  // DATA
  A x;
  P a1;
  Q a2;

  // ACCESSORS
  SigT2<A, P, Q> clone() const { return {x, a1, a2}; }

  template <typename CraneU0, typename CraneU1, typename CraneU2>
  operator SigT2<CraneU0, CraneU1, CraneU2>() const {
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
  static SigT2<A, P, Q> existt2(A x, P a1, Q a2) {
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

  SigT<A, P> sigT_of_sigT2() const {
    return SigT<A, P>::existt(
        [&]() {
          const auto &[x0, _, _] = *this;
          return x0;
        }(),
        [&]() {
          const auto &[_, a10, _] = *this;
          return a10;
        }());
  }

  Q projT3() const {
    const auto &[_, _, a2] = *this;
    return a2;
  }

  A sig2_of_sigT2() const { return this->sigT_of_sigT2().projT1(); }

  template <typename T1>
  T1 eq_sigT2_rect(const SigT2<A, P, Q> &, const T1 &f) const {
    return f;
  }

  template <typename T1>
  T1 eq_sigT2_rec(const SigT2<A, P, Q> &x1_, const T1 &x2_) const {
    return this->template eq_sigT2_rect<T1>(x1_, x2_);
  }

  template <typename T1>
  T1 eq_sigT2_rect_existT2_l(const A &u1, const P &u2, const Q &u3,
                             const T1 &f) const {
    return SigT2<A, P, Q>::existt2(u1, u2, u3).template eq_sigT2_rect<T1>(*this,
                                                                          f);
  }

  template <typename T1>
  T1 eq_sigT2_rect_existT2_r(const A &v1, const P &v2, const Q &v3,
                             const T1 &f) const {
    return this->template eq_sigT2_rect<T1>(SigT2<A, P, Q>::existt2(v1, v2, v3),
                                            f);
  }

  template <typename T1>
  T1 eq_sigT2_rect_uncurried(const SigT2<A, P, Q> &v, T1 f) const {
    return this->template eq_sigT2_rect<T1>(
        v, [=, f = std::move(f)]() { return f; }());
  }

  template <typename T1>
  T1 eq_sigT2_rec_uncurried(const SigT2<A, P, Q> &x1_, T1 x2_) const {
    return this->template eq_sigT2_rect_uncurried<T1>(x1_, std::move(x2_));
  }
};

template <typename T1> T1 sig_of_sig2(const T1 &x) {
  const T1 &a = x;
  return crane_any_cast<T1>(a);
}

template <typename T1> SigT<T1, crane::obj> sigT_of_sig(const T1 &x) {
  // Precondition: P
  return SigT<T1, crane::obj>::existt(x, crane::obj());
}

template <typename T1>
SigT2<T1, crane::obj, crane::obj> sigT2_of_sig2(const T1 &x) {
  return SigT2<T1, crane::obj, crane::obj>::existt2(sig_of_sig2<T1>(x),
                                                    crane::obj(), crane::obj());
}

template <typename T1, typename T2>
SigT<T1, T2> sigT_of_prod(const std::pair<T1, T2> &p) {
  return SigT<T1, T2>::existt(p.first, p.second);
}

template <typename T1, typename T2, typename T3>
T3 eq_sigT_rect_existT(const T1 &u1, const T2 &u2, const T1 &v1, const T2 &v2,
                       const T3 &f) {
  return SigT<T1, T2>::existt(u1, u2).template eq_sigT_rect<T3>(
      SigT<T1, T2>::existt(v1, v2), f);
}

template <typename T1, typename T2>
T2 eq_sig_rect(const T1 &u, const T1 &, const T2 &f) {
  // Precondition: (P a)
  // Precondition: (P a)
  T2 f0 = f;
  const T1 &_x0 = u;
  return f0;
}

template <typename T1, typename T2>
T2 eq_sig_rec(const T1 &x0_, const T1 &x1_, const T2 &x2_) {
  // Precondition: (P a)
  // Precondition: (P a)
  return eq_sig_rect<T1, T2>(x0_, x1_, x2_);
}

template <typename T1, typename T2>
T2 eq_sig_rect_exist_l(const T1 &u1, const T1 &v, const T2 &f) {
  // Precondition: (P a)
  return eq_sig_rect<T1, T2>(u1, v, f);
}

template <typename T1, typename T2>
T2 eq_sig_rect_exist_r(const T1 &u, const T1 &v1, const T2 &f) {
  // Precondition: (P a)
  return eq_sig_rect<T1, T2>(u, v1, f);
}

template <typename T1, typename T2>
T2 eq_sig_rect_exist(const T1 &u1, const T1 &v1, const T2 &f) {
  return eq_sig_rect<T1, T2>(u1, v1, f);
}

template <typename T1, typename T2>
T2 eq_sig_rect_uncurried(const T1 &u, const T1 &v, T2 f) {
  // Precondition: (P a)
  // Precondition: (P a)
  return eq_sig_rect<T1, T2>(u, v, [=, f = std::move(f)]() { return f; }());
}

template <typename T1, typename T2>
T2 eq_sig_rec_uncurried(const T1 &x0_, const T1 &x1_, T2 x2_) {
  // Precondition: (P a)
  // Precondition: (P a)
  return eq_sig_rect_uncurried<T1, T2>(x0_, x1_, std::move(x2_));
}

template <typename T1, typename T2, typename T3, typename T4>
T4 eq_sigT2_rect_existT2(const T1 &u1, const T2 &u2, const T3 &u3, const T1 &v1,
                         const T2 &v2, const T3 &v3, const T4 &f) {
  return SigT2<T1, T2, T3>::existt2(u1, u2, u3).template eq_sigT2_rect<T4>(
      SigT2<T1, T2, T3>::existt2(v1, v2, v3), f);
}

template <typename T1, typename T2>
T2 eq_sig2_rect(const T1 &u, const T1 &, const T2 &f) {
  T2 f0 = f;
  const T1 &_x0 = u;
  return f0;
}

template <typename T1, typename T2>
T2 eq_sig2_rec(const T1 &x0_, const T1 &x1_, const T2 &x2_) {
  return eq_sig2_rect<T1, T2>(x0_, x1_, x2_);
}

template <typename T1, typename T2>
T2 eq_sig2_rect_exist2_l(const T1 &u1, const T1 &v, const T2 &f) {
  return eq_sig2_rect<T1, T2>(u1, v, f);
}

template <typename T1, typename T2>
T2 eq_sig2_rect_exist2_r(const T1 &u, const T1 &v1, const T2 &f) {
  return eq_sig2_rect<T1, T2>(u, v1, f);
}

template <typename T1, typename T2>
T2 eq_sig2_rect_exist2(const T1 &u1, const T1 &v1, const T2 &f) {
  return eq_sig2_rect<T1, T2>(u1, v1, f);
}

template <typename T1, typename T2>
T2 eq_sig2_rect_uncurried(const T1 &u, const T1 &v, T2 f) {
  return eq_sig2_rect<T1, T2>(u, v, [=, f = std::move(f)]() { return f; }());
}

template <typename T1, typename T2>
T2 eq_sig2_rec_uncurried(const T1 &x0_, const T1 &x1_, T2 x2_) {
  return eq_sig2_rect_uncurried<T1, T2>(x0_, x1_, std::move(x2_));
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
  Sumor(const Sumor<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Sumor<CraneU>::Inleft>(_other.v())) {
            const auto &[a0] =
                std::get<typename Sumor<CraneU>::Inleft>(_other.v());
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

  static Sumor<A> inleft(A a0) { return Sumor<A>(Inleft{std::move(a0)}); }

  static Sumor<A> inright() { return Sumor<A>(Inright{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  T1 sumor_rect(F0 &&f, const T1 &f0) const {
    if (std::holds_alternative<typename Sumor<A>::Inleft>(this->v())) {
      const auto &[a0] = std::get<typename Sumor<A>::Inleft>(this->v());
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
crane::fn<T2(T1)> Choice(std::type_identity_t<crane::fn<T2(T1)>> h) {
  return [=, h = std::move(h)](const T1 &z) { return h(z); };
}

template <typename T1, typename T2, typename T3>
SigT<crane::fn<T2(T1)>, crane::fn<T3(T1)>>
Choice2(std::type_identity_t<crane::fn<SigT<T2, T3>(T1)>> h) {
  return SigT<crane::fn<T2(T1)>, crane::fn<T3(T1)>>::existt(
      [=](const T1 &z) { return h(z).projT1(); }, [=](const T1 &z) {
        SigT<T2, T3> s = h(z);
        auto &[_, a1] = s;
        return std::move(a1);
      });
}

template <typename T1>
crane::fn<bool(T1)> bool_choice(std::type_identity_t<crane::fn<bool(T1)>> h) {
  return [=, h = std::move(h)](const T1 &z) -> bool {
    if (h(z)) {
      return true;
    } else {
      return false;
    }
  };
}

template <typename T1>
crane::fn<T1(uint64_t)>
dependent_choice(std::type_identity_t<crane::fn<T1(T1)>> h, T1 x0) {
  auto f_impl =
      [=, h = std::move(h), x0 = std::move(x0)](auto &_self_f,
                                                uint64_t n)
           -> T1 {
        if (n <= 0) {
          return x0;
        } else {
          uint64_t n_ = n - 1;
          return h(_self_f(_self_f, n_));
        }
      };
  auto f =
      [=, f_impl = std::move(f_impl)](uint64_t n) -> T1 {
        return f_impl(f_impl, n);
      };
  return f;
}

template <typename a> using Exc = std::optional<a>;

template <typename T1> std::optional<T1> value(const T1 &x) {
  return std::make_optional<T1>(x);
}

template <typename T1> const std::optional<T1> error = std::optional<T1>();

template <typename T1> T1 except() { throw std::logic_error("absurd case"); }

template <typename T1>
const T1 absurd_set = [](crane::obj) { return except<T1>(); };
} // namespace Specif
