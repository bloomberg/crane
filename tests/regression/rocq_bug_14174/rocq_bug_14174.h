#ifndef INCLUDED_ROCQ_BUG_14174
#define INCLUDED_ROCQ_BUG_14174

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

enum class Bool0;
struct Nat;
template <typename A> struct Option;
template <typename A, typename B> struct Prod;
template <typename A> struct Sig;
template <typename A> struct Sig2;
template <typename A, typename P> struct SigT;
template <typename A, typename P, typename Q> struct SigT2;
enum class Sumbool;
template <typename A> struct Sumor;

struct SigTNotations {};
enum class Bool0 { TRUE_, FALSE_ };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct Option {
  // TYPES
  struct Some {
    A a;
  };

  struct None {};

  using variant_t = std::variant<Some, None>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Option() {}

  explicit Option(Some _v) : v_(std::move(_v)) {}

  explicit Option(None _v) : v_(_v) {}

  template <typename CraneU>
  Option(const Option<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Option<CraneU>::Some>(
                  _other.v())) {
            const auto &[a] =
                std::get<typename Option<CraneU>::Some>(_other.v());
            return Some{[&]() -> A {
              if constexpr (crane_convertible<A, const CraneU &>) {
                return crane_convert<A>(a);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            return None{};
          }
        }()) {}

  static Option<A> some(A a) { return Option<A>(Some{std::move(a)}); }

  static Option<A> none() { return Option<A>(None{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename B> struct Prod {
  // DATA
  A a0;
  B a1;

  // ACCESSORS
  Prod<A, B> clone() const { return {a0, a1}; }

  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const B &>
  operator Prod<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(a0), crane_convert<CraneU1>(a1)};
  }

  // CREATORS
  static Prod<A, B> pair(A a0, B a1) { return {std::move(a0), std::move(a1)}; }

  A fst() const {
    auto &[a0, a1] = *this;
    return a0;
  }

  B snd() const {
    auto &[a0, a1] = *this;
    return a1;
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU>
    requires crane_convertible<CraneU, const A &>
  operator Sig<CraneU>() const {
    return {crane_convert<CraneU>(x)};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

template <typename A> struct Sig2 {
  // DATA
  A x;

  // ACCESSORS
  Sig2<A> clone() const { return {x}; }

  template <typename CraneU>
    requires crane_convertible<CraneU, const A &>
  operator Sig2<CraneU>() const {
    return {crane_convert<CraneU>(x)};
  }

  // CREATORS
  static Sig2<A> exist2(A x) { return {std::move(x)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &>
  operator SigT<CraneU0, CraneU1>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

template <typename A, typename P, typename Q> struct SigT2 {
  // DATA
  A x;
  P a1;
  Q a2;

  // ACCESSORS
  SigT2<A, P, Q> clone() const { return {x, a1, a2}; }

  template <typename CraneU0, typename CraneU1, typename CraneU2>
    requires crane_convertible<CraneU0, const A &> &&
             crane_convertible<CraneU1, const P &> &&
             crane_convertible<CraneU2, const Q &>
  operator SigT2<CraneU0, CraneU1, CraneU2>() const {
    return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1),
            crane_convert<CraneU2>(a2)};
  }

  // CREATORS
  static SigT2<A, P, Q> existt2(A x, P a1, Q a2) {
    return {std::move(x), std::move(a1), std::move(a2)};
  }
};
enum class Sumbool { LEFT, RIGHT };

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
          if (std::holds_alternative<typename Sumor<CraneU>::Inleft>(
                  _other.v())) {
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
};

struct RocqBug14174 {
  struct A {
    template <typename A> struct sig {
      // DATA
      A x;

      // ACCESSORS
      sig<A> clone() const { return {x}; }

      template <typename CraneU>
        requires crane_convertible<CraneU, const A &>
      operator sig<CraneU>() const {
        return {crane_convert<CraneU>(x)};
      }

      // CREATORS
      static sig<A> exist(A x) { return {std::move(x)}; }

      template <typename T1>
      T1 eq_sig_rec_uncurried(const sig<A> &x1_, const T1 &x2_) const {
        return this->template eq_sig_rect_uncurried<crane::obj>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sig_rect_uncurried(const sig<A> &v, T1 f) const {
        return this->template eq_sig_rect<crane::obj>(v, [=]() { return f; }());
      }

      template <typename T1>
      T1 eq_sig_rect_exist_r(const A &v1, const T1 &f) const {
        return this->template eq_sig_rect<crane::obj>(sig<A>::exist(v1), f);
      }

      template <typename T1>
      T1 eq_sig_rect_exist_l(const A &u1, const T1 &f) const {
        return sig<A>::exist(u1).template eq_sig_rect<crane::obj>(*this, f);
      }

      template <typename T1>
      T1 eq_sig_rec(const sig<A> &x1_, const T1 &x2_) const {
        return this->template eq_sig_rect<crane::obj>(x1_, x2_);
      }

      template <typename T1> T1 eq_sig_rect(const sig<A> &, const T1 &f) const {
        return f;
      }

      A proj1_sig() const {
        const auto &[x] = *this;
        return x;
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &>
      T1 sig_rec(F0 &&f) const {
        const auto &[x0] = *this;
        return f(x0);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &>
      T1 sig_rect(F0 &&f) const {
        const auto &[x0] = *this;
        return f(x0);
      }
    };

    template <typename A> struct sig2 {
      // DATA
      A x;

      // ACCESSORS
      sig2<A> clone() const { return {x}; }

      template <typename CraneU>
        requires crane_convertible<CraneU, const A &>
      operator sig2<CraneU>() const {
        return {crane_convert<CraneU>(x)};
      }

      // CREATORS
      static sig2<A> exist2(A x) { return {std::move(x)}; }

      template <typename T1>
      T1 eq_sig2_rec_uncurried(const sig2<A> &x1_, const T1 &x2_) const {
        return this->template eq_sig2_rect_uncurried<crane::obj>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sig2_rect_uncurried(const sig2<A> &v, T1 f) const {
        return this->template eq_sig2_rect<crane::obj>(v,
                                                       [=]() { return f; }());
      }

      template <typename T1>
      T1 eq_sig2_rect_exist2_r(const A &v1, const T1 &f) const {
        return this->template eq_sig2_rect<crane::obj>(sig2<A>::exist2(v1), f);
      }

      template <typename T1>
      T1 eq_sig2_rect_exist2_l(const A &u1, const T1 &f) const {
        return sig2<A>::exist2(u1).template eq_sig2_rect<crane::obj>(*this, f);
      }

      template <typename T1>
      T1 eq_sig2_rec(const sig2<A> &x1_, const T1 &x2_) const {
        return this->template eq_sig2_rect<crane::obj>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sig2_rect(const sig2<A> &, const T1 &f) const {
        return f;
      }

      sig<A> sig_of_sig2() const {
        return sig<A>::exist([&]() {
          const auto &[x0] = *this;
          return x0;
        }());
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &>
      T1 sig2_rec(F0 &&f) const {
        const auto &[x0] = *this;
        return f(x0);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &>
      T1 sig2_rect(F0 &&f) const {
        const auto &[x0] = *this;
        return f(x0);
      }
    };

    template <typename A, typename P> struct sigT {
      // DATA
      A x;
      P a1;

      // ACCESSORS
      sigT<A, P> clone() const { return {x, a1}; }

      template <typename CraneU0, typename CraneU1>
        requires crane_convertible<CraneU0, const A &> &&
                 crane_convertible<CraneU1, const P &>
      operator sigT<CraneU0, CraneU1>() const {
        return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1)};
      }

      // CREATORS
      static sigT<A, P> existt(A x, P a1) {
        return {std::move(x), std::move(a1)};
      }

      template <typename T1>
      T1 eq_sigT_rec_uncurried(const sigT<A, P> &x1_, const T1 &x2_) const {
        return this->template eq_sigT_rect_uncurried<T1>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sigT_rect_uncurried(const sigT<A, P> &v, T1 f) const {
        return this->template eq_sigT_rect<T1>(v, [=]() { return f; }());
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_r(const A &v1, const P &v2, const T1 &f) const {
        return this->template eq_sigT_rect<T1>(sigT<A, P>::existt(v1, v2), f);
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_l(const A &u1, const P &u2, const T1 &f) const {
        return sigT<A, P>::existt(u1, u2).template eq_sigT_rect<T1>(*this, f);
      }

      template <typename T1>
      T1 eq_sigT_rec(const sigT<A, P> &x1_, const T1 &x2_) const {
        return this->template eq_sigT_rect<T1>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sigT_rect(const sigT<A, P> &, const T1 &f) const {
        return f;
      }

      Prod<A, P> prod_of_sigT() const {
        return Prod<A, P>::pair(this->projT1(), this->projT2());
      }

      P projT2() const {
        const auto &[x0, a1] = *this;
        return a1;
      }

      A projT1() const {
        const auto &[x0, a1] = *this;
        return x0;
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &, const P &>
      T1 sigT_rec(F0 &&f) const {
        const auto &[x0, a1] = *this;
        return f(x0, a1);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &, const P &>
      T1 sigT_rect(F0 &&f) const {
        const auto &[x0, a1] = *this;
        return f(x0, a1);
      }
    };

    template <typename A, typename P, typename Q> struct sigT2 {
      // DATA
      A x;
      P a1;
      Q a2;

      // ACCESSORS
      sigT2<A, P, Q> clone() const { return {x, a1, a2}; }

      template <typename CraneU0, typename CraneU1, typename CraneU2>
        requires crane_convertible<CraneU0, const A &> &&
                 crane_convertible<CraneU1, const P &> &&
                 crane_convertible<CraneU2, const Q &>
      operator sigT2<CraneU0, CraneU1, CraneU2>() const {
        return {crane_convert<CraneU0>(x), crane_convert<CraneU1>(a1),
                crane_convert<CraneU2>(a2)};
      }

      // CREATORS
      static sigT2<A, P, Q> existt2(A x, P a1, Q a2) {
        return {std::move(x), std::move(a1), std::move(a2)};
      }

      template <typename T1>
      T1 eq_sigT2_rec_uncurried(const sigT2<A, P, Q> &x1_,
                                const T1 &x2_) const {
        return this->template eq_sigT2_rect_uncurried<T1>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sigT2_rect_uncurried(const sigT2<A, P, Q> &v, T1 f) const {
        return this->template eq_sigT2_rect<T1>(v, [=]() { return f; }());
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_r(const A &v1, const P &v2, const Q &v3,
                                 const T1 &f) const {
        return this->template eq_sigT2_rect<T1>(
            sigT2<A, P, Q>::existt2(v1, v2, v3), f);
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_l(const A &u1, const P &u2, const Q &u3,
                                 const T1 &f) const {
        return sigT2<A, P, Q>::existt2(u1, u2, u3)
            .template eq_sigT2_rect<T1>(*this, f);
      }

      template <typename T1>
      T1 eq_sigT2_rec(const sigT2<A, P, Q> &x1_, const T1 &x2_) const {
        return this->template eq_sigT2_rect<T1>(x1_, x2_);
      }

      template <typename T1>
      T1 eq_sigT2_rect(const sigT2<A, P, Q> &, const T1 &f) const {
        return f;
      }

      Q projT3() const {
        const auto &[x, a1, a2] = *this;
        return a2;
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

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &, const P &,
                                       const Q &>
      T1 sigT2_rec(F0 &&f) const {
        const auto &[x0, a1, a2] = *this;
        return f(x0, a1, a2);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, const A &, const P &,
                                       const Q &>
      T1 sigT2_rect(F0 &&f) const {
        const auto &[x0, a1, a2] = *this;
        return f(x0, a1, a2);
      }
    };

    using SigTNotations = SigTNotations;

    template <typename T1>
    static sig<T1> sig_of_sigT(const sigT<T1, crane::obj> &x) {
      return sig<T1>::exist(x.projT1());
    }

    template <typename T1>
    static sigT<T1, crane::obj> sigT_of_sig(const sig<T1> &x) {
      return sigT<T1, crane::obj>::existt(x.proj1_sig(), crane::obj());
    }

    template <typename T1>
    static sig2<T1> sig2_of_sigT2(const sigT2<T1, crane::obj, crane::obj> &x) {
      return sig2<T1>::exist2(x.sigT_of_sigT2().projT1());
    }

    template <typename T1>
    static sigT2<T1, crane::obj, crane::obj> sigT2_of_sig2(const sig2<T1> &x) {
      return sigT2<T1, crane::obj, crane::obj>::existt2(
          x.sig_of_sig2().proj1_sig(), crane::obj(), crane::obj());
    }

    template <typename T1, typename T2>
    static sigT<T1, T2> sigT_of_prod(const Prod<T1, T2> &p) {
      return sigT<T1, T2>::existt(p.fst(), p.snd());
    }

    template <typename T1, typename T2, typename T3>
    static T3 eq_sigT_rect_existT(const T1 &u1, const T2 &u2, const T1 &v1,
                                  const T2 &v2, const T3 &f) {
      return sigT<T1, T2>::existt(u1, u2).template eq_sigT_rect<T3>(
          sigT<T1, T2>::existt(v1, v2), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig_rect_exist(const T1 &u1, const T1 &v1, const T2 &f) {
      return sig<T1>::exist(u1).template eq_sig_rect<T2>(sig<T1>::exist(v1), f);
    }

    template <typename T1, typename T2, typename T3, typename T4>
    static T4 eq_sigT2_rect_existT2(const T1 &u1, const T2 &u2, const T3 &u3,
                                    const T1 &v1, const T2 &v2, const T3 &v3,
                                    const T4 &f) {
      return sigT2<T1, T2, T3>::existt2(u1, u2, u3)
          .template eq_sigT2_rect<T4>(sigT2<T1, T2, T3>::existt2(v1, v2, v3),
                                      f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig2_rect_exist2(const T1 &u1, const T1 &v1, const T2 &f) {
      return sig2<T1>::exist2(u1).template eq_sig2_rect<T2>(
          sig2<T1>::exist2(v1), f);
    }
    enum class Sumbool { LEFT, RIGHT };

    template <typename T1>
    static T1 sumbool_rect(const T1 &f, const T1 &f0, Sumbool s) {
      switch (s) {
      case Sumbool::LEFT: {
        return f;
      }
      case Sumbool::RIGHT: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1>
    static T1 sumbool_rec(const T1 &f, const T1 &f0, Sumbool s) {
      switch (s) {
      case Sumbool::LEFT: {
        return f;
      }
      case Sumbool::RIGHT: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename A> struct sumor {
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
      sumor() {}

      explicit sumor(Inleft _v) : v_(std::move(_v)) {}

      explicit sumor(Inright _v) : v_(_v) {}

      template <typename CraneU>
      sumor(const sumor<CraneU> &_other)
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
      T1 sumor_rec(F0 &&f, const T1 &f0) const {
        if (std::holds_alternative<typename sumor<A>::Inleft>(this->v())) {
          const auto &[a0] = std::get<typename sumor<A>::Inleft>(this->v());
          return f(a0);
        } else {
          return f0;
        }
      }

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
    };

    template <typename T1, typename T2>
    static sig<crane::fn<T2(T1)>>
    Choice(std::type_identity_t<crane::fn<sig<T2>(T1)>> h) {
      return sig<crane::fn<T2(T1)>>::exist(
          [=](const T1 &z) { return h(z).proj1_sig(); });
    }

    template <typename T1, typename T2, typename T3>
    static sigT<crane::fn<T2(T1)>, crane::fn<T3(T1)>>
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
    static sig<crane::fn<Bool0(T1)>>
    bool_choice(std::type_identity_t<crane::fn<Sumbool(T1)>> h) {
      return sig<crane::fn<Bool0(T1)>>::exist([=](const T1 &z) {
        switch (h(z)) {
        case Sumbool::LEFT: {
          return Bool0::TRUE_;
        }
        case Sumbool::RIGHT: {
          return Bool0::FALSE_;
        }
        default:
          std::unreachable();
        }
      });
    }

    template <typename T1>
    static sig<crane::fn<T1(Nat)>>
    dependent_choice(std::type_identity_t<crane::fn<sig<T1>(T1)>> h, T1 x0) {
      auto f_impl = [=](auto &_self_f, Nat n) -> T1 {
        if (std::holds_alternative<typename Nat::O>(n.v())) {
          return x0;
        } else {
          const auto &[a0] = std::get<typename Nat::S>(n.v());
          return h(_self_f(_self_f, *a0)).proj1_sig();
        }
      };
      auto f = [=](Nat n) -> T1 { return f_impl(f_impl, n); };
      return sig<crane::fn<T1(Nat)>>::exist(std::move(f));
    }

    template <typename a> using Exc = Option<a>;

    template <typename T1> static Option<T1> value(const T1 &x) {
      return Option<T1>::some(x);
    }

    template <typename T1> static const Option<T1> &error() {
      static const Option<T1> v = Option<T1>::none();
      return v;
    }

    template <typename T1> static T1 except() {
      throw std::logic_error("absurd case");
    }

    template <typename T1> static T1 absurd_set() {
      throw std::logic_error("absurd case");
    }
  };
};

#endif // INCLUDED_ROCQ_BUG_14174
