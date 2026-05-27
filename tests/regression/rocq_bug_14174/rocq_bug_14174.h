#ifndef INCLUDED_ROCQ_BUG_14174
#define INCLUDED_ROCQ_BUG_14174

#include <any>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename _U> explicit Option(const Option<_U> &_other) {
    if (std::holds_alternative<typename Option<_U>::Some>(_other.v())) {
      const auto &[a] = std::get<typename Option<_U>::Some>(_other.v());
      this->v_ = Some{[&]() -> A {
        if constexpr (std::is_same_v<_U, std::any>) {
          if (a.type() == typeid(A))
            return std::any_cast<A>(a);
          if constexpr (requires {
                          typename A::first_type;
                          typename A::second_type;
                        }) {
            const auto &[_k, _v] =
                std::any_cast<std::pair<std::any, std::any>>(a);
            return A{[&]() -> typename A::first_type {
                       if constexpr (std::is_same_v<typename A::first_type,
                                                    std::any>)
                         return _k;
                       else
                         return std::any_cast<typename A::first_type>(_k);
                     }(),
                     [&]() -> typename A::second_type {
                       if constexpr (std::is_same_v<typename A::second_type,
                                                    std::any>)
                         return _v;
                       else
                         return std::any_cast<typename A::second_type>(_v);
                     }()};
          }
          return std::any_cast<A>(a);
        } else
          return A(a);
      }()};
    } else {
      this->v_ = None{};
    }
  }

  static Option<A> some(A a) { return Option(Some{std::move(a)}); }

  static Option<A> none() { return Option(None{}); }

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

  // CREATORS
  static Sig<A> exist0(A x) { return {std::move(x)}; }
};

template <typename A> struct Sig2 {
  // DATA
  A x;

  // ACCESSORS
  Sig2<A> clone() const { return {x}; }

  // CREATORS
  static Sig2<A> exist1(A x) { return {std::move(x)}; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt0(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

template <typename A, typename P, typename Q> struct SigT2 {
  // DATA
  A x;
  P a1;
  Q a2;

  // ACCESSORS
  SigT2<A, P, Q> clone() const { return {x, a1, a2}; }

  // CREATORS
  static SigT2<A, P, Q> existt1(A x, P a1, Q a2) {
    return {std::move(x), std::move(a1), std::move(a2)};
  }
};

struct SigTNotations {};
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

  template <typename _U> explicit Sumor(const Sumor<_U> &_other) {
    if (std::holds_alternative<typename Sumor<_U>::Inleft>(_other.v())) {
      const auto &[a0] = std::get<typename Sumor<_U>::Inleft>(_other.v());
      this->v_ = Inleft{[&]() -> A {
        if constexpr (std::is_same_v<_U, std::any>) {
          if (a0.type() == typeid(A))
            return std::any_cast<A>(a0);
          if constexpr (requires {
                          typename A::first_type;
                          typename A::second_type;
                        }) {
            const auto &[_k, _v] =
                std::any_cast<std::pair<std::any, std::any>>(a0);
            return A{[&]() -> typename A::first_type {
                       if constexpr (std::is_same_v<typename A::first_type,
                                                    std::any>)
                         return _k;
                       else
                         return std::any_cast<typename A::first_type>(_k);
                     }(),
                     [&]() -> typename A::second_type {
                       if constexpr (std::is_same_v<typename A::second_type,
                                                    std::any>)
                         return _v;
                       else
                         return std::any_cast<typename A::second_type>(_v);
                     }()};
          }
          return std::any_cast<A>(a0);
        } else
          return A(a0);
      }()};
    } else {
      this->v_ = Inright{};
    }
  }

  static Sumor<A> inleft(A a0) { return Sumor(Inleft{std::move(a0)}); }

  static Sumor<A> inright() { return Sumor(Inright{}); }

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

      // CREATORS
      static sig<A> exist(A x) { return {std::move(x)}; }

      template <typename T1>
      T1 eq_sig_rec_uncurried(const sig<A> &_x1, const T1 &_x2) const {
        return this->eq_sig_rect_uncurried(_x1, _x2);
      }

      template <typename T1>
      T1 eq_sig_rect_uncurried(const sig<A> &v, T1 f) const {
        return this->eq_sig_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1> T1 eq_sig_rect_exist_r(A v1, const T1 &f) const {
        return this->eq_sig_rect(sig<A>::exist(v1), f);
      }

      template <typename T1> T1 eq_sig_rect_exist_l(A u1, const T1 &f) const {
        return sig<A>::exist(u1).eq_sig_rect(*this, f);
      }

      template <typename T1>
      T1 eq_sig_rec(const sig<A> &_x1, const T1 &_x2) const {
        return this->eq_sig_rect(_x1, _x2);
      }

      template <typename T1> T1 eq_sig_rect(const sig<A> &, const T1 &f) const {
        return f;
      }

      A proj1_sig() const {
        const auto &[x] = *this;
        return x;
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &>
      T1 sig_rec(F0 &&f) const {
        const auto &[x0] = *this;
        return f(x0);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &>
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

      // CREATORS
      static sig2<A> exist2(A x) { return {std::move(x)}; }

      template <typename T1>
      T1 eq_sig2_rec_uncurried(const sig2<A> &_x1, const T1 &_x2) const {
        return this->eq_sig2_rect_uncurried(_x1, _x2);
      }

      template <typename T1>
      T1 eq_sig2_rect_uncurried(const sig2<A> &v, T1 f) const {
        return this->eq_sig2_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1> T1 eq_sig2_rect_exist2_r(A v1, const T1 &f) const {
        return this->eq_sig2_rect(sig2<A>::exist2(v1), f);
      }

      template <typename T1> T1 eq_sig2_rect_exist2_l(A u1, const T1 &f) const {
        return sig2<A>::exist2(u1).eq_sig2_rect(*this, f);
      }

      template <typename T1>
      T1 eq_sig2_rec(const sig2<A> &_x1, const T1 &_x2) const {
        return this->eq_sig2_rect(_x1, _x2);
      }

      template <typename T1>
      T1 eq_sig2_rect(const sig2<A> &, const T1 &f) const {
        return f;
      }

      sig<A> sig_of_sig2() const {
        sig2<A> _self_val = *this;
        return sig<A>::exist([=]() mutable {
          const auto &[x0] = _self_val;
          return x0;
        }());
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &>
      T1 sig2_rec(F0 &&f) const {
        const auto &[x0] = *this;
        return f(x0);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &>
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

      // CREATORS
      static sigT<A, P> existt(A x, P a1) {
        return {std::move(x), std::move(a1)};
      }

      template <typename T1>
      T1 eq_sigT_rec_uncurried(const sigT<A, P> &_x1, const T1 &_x2) const {
        return this->eq_sigT_rect_uncurried(_x1, _x2);
      }

      template <typename T1>
      T1 eq_sigT_rect_uncurried(const sigT<A, P> &v, T1 f) const {
        return this->eq_sigT_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_r(A v1, P v2, const T1 &f) const {
        return this->eq_sigT_rect(sigT<A, P>::existt(v1, v2), f);
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_l(A u1, P u2, const T1 &f) const {
        return sigT<A, P>::existt(u1, u2).eq_sigT_rect(*this, f);
      }

      template <typename T1>
      T1 eq_sigT_rec(const sigT<A, P> &_x1, const T1 &_x2) const {
        return this->eq_sigT_rect(_x1, _x2);
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
        requires std::is_invocable_r_v<T1, F0 &, A &, P &>
      T1 sigT_rec(F0 &&f) const {
        const auto &[x0, a1] = *this;
        return f(x0, a1);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &, P &>
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

      // CREATORS
      static sigT2<A, P, Q> existt2(A x, P a1, Q a2) {
        return {std::move(x), std::move(a1), std::move(a2)};
      }

      template <typename T1>
      T1 eq_sigT2_rec_uncurried(const sigT2<A, P, Q> &_x1,
                                const T1 &_x2) const {
        return this->eq_sigT2_rect_uncurried(_x1, _x2);
      }

      template <typename T1>
      T1 eq_sigT2_rect_uncurried(const sigT2<A, P, Q> &v, T1 f) const {
        return this->eq_sigT2_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_r(A v1, P v2, Q v3, const T1 &f) const {
        return this->eq_sigT2_rect(sigT2<A, P, Q>::existt2(v1, v2, v3), f);
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_l(A u1, P u2, Q u3, const T1 &f) const {
        return sigT2<A, P, Q>::existt2(u1, u2, u3).eq_sigT2_rect(*this, f);
      }

      template <typename T1>
      T1 eq_sigT2_rec(const sigT2<A, P, Q> &_x1, const T1 &_x2) const {
        return this->eq_sigT2_rect(_x1, _x2);
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
        sigT2<A, P, Q> _self_val = *this;
        return sigT<A, P>::existt(
            [=]() mutable {
              const auto &[x0, a1, a2] = _self_val;
              return x0;
            }(),
            [=]() mutable {
              const auto &[x0, a10, a20] = _self_val;
              return a10;
            }());
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &, P &, Q &>
      T1 sigT2_rec(F0 &&f) const {
        const auto &[x0, a1, a2] = *this;
        return f(x0, a1, a2);
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &, P &, Q &>
      T1 sigT2_rect(F0 &&f) const {
        const auto &[x0, a1, a2] = *this;
        return f(x0, a1, a2);
      }
    };

    using SigTNotations = SigTNotations;

    template <typename T1>
    static sig<T1> sig_of_sigT(const sigT<T1, std::any> &x) {
      return sig<T1>::exist(x.projT1());
    }

    template <typename T1>
    static sigT<T1, std::any> sigT_of_sig(const sig<T1> &x) {
      return sigT<T1, std::any>::existt(x.proj1_sig(), std::any{});
    }

    template <typename T1>
    static sig2<T1> sig2_of_sigT2(const sigT2<T1, std::any, std::any> &x) {
      return sig2<T1>::exist2(x.sigT_of_sigT2().projT1());
    }

    template <typename T1>
    static sigT2<T1, std::any, std::any> sigT2_of_sig2(const sig2<T1> &x) {
      return sigT2<T1, std::any, std::any>::existt2(x.sig_of_sig2().proj1_sig(),
                                                    std::any{}, std::any{});
    }

    template <typename T1, typename T2>
    static sigT<T1, T2> sigT_of_prod(const Prod<T1, T2> &p) {
      return sigT<T1, T2>::existt(p.fst(), p.snd());
    }

    template <typename T1, typename T2, typename T3>
    static T3 eq_sigT_rect_existT(T1 u1, T2 u2, T1 v1, T2 v2, const T3 &f) {
      return sigT<T1, T2>::existt(u1, u2).eq_sigT_rect(
          sigT<T1, T2>::existt(v1, v2), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig_rect_exist(T1 u1, T1 v1, const T2 &f) {
      return sig<T1>::exist(u1).eq_sig_rect(sig<T1>::exist(v1), f);
    }

    template <typename T1, typename T2, typename T3, typename T4>
    static T4 eq_sigT2_rect_existT2(T1 u1, T2 u2, T3 u3, T1 v1, T2 v2, T3 v3,
                                    const T4 &f) {
      return sigT2<T1, T2, T3>::existt2(u1, u2, u3)
          .eq_sigT2_rect(sigT2<T1, T2, T3>::existt2(v1, v2, v3), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig2_rect_exist2(T1 u1, T1 v1, const T2 &f) {
      return sig2<T1>::exist2(u1).eq_sig2_rect(sig2<T1>::exist2(v1), f);
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

      template <typename _U> explicit sumor(const sumor<_U> &_other) {
        if (std::holds_alternative<typename sumor<_U>::Inleft>(_other.v())) {
          const auto &[a0] = std::get<typename sumor<_U>::Inleft>(_other.v());
          this->v_ = Inleft{[&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a0.type() == typeid(A))
                return std::any_cast<A>(a0);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a0);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a0);
            } else
              return A(a0);
          }()};
        } else {
          this->v_ = Inright{};
        }
      }

      static sumor<A> inleft(A a0) { return sumor(Inleft{std::move(a0)}); }

      static sumor<A> inright() { return sumor(Inright{}); }

      // MANIPULATORS
      inline variant_t &v_mut() { return v_; }

      // ACCESSORS
      const variant_t &v() const { return v_; }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &>
      T1 sumor_rec(F0 &&f, const T1 &f0) const {
        if (std::holds_alternative<typename sumor<A>::Inleft>(this->v())) {
          const auto &[a0] = std::get<typename sumor<A>::Inleft>(this->v());
          return f(a0);
        } else {
          return f0;
        }
      }

      template <typename T1, typename F0>
        requires std::is_invocable_r_v<T1, F0 &, A &>
      T1 sumor_rect(F0 &&f, const T1 &f0) const {
        if (std::holds_alternative<typename sumor<A>::Inleft>(this->v())) {
          const auto &[a0] = std::get<typename sumor<A>::Inleft>(this->v());
          return f(a0);
        } else {
          return f0;
        }
      }
    };

    template <typename T1, typename T2, typename F0>
      requires std::is_invocable_r_v<sig<T2>, F0 &, T1 &>
    static sig<std::function<T2(T1)>> Choice(F0 &&h) {
      return sig<std::function<T2(T1)>>::exist(
          [=](const T1 &z) mutable { return h(z).proj1_sig(); });
    }

    template <typename T1, typename T2, typename T3, typename F0>
      requires std::is_invocable_r_v<sigT<T2, T3>, F0 &, T1 &>
    static sigT<std::function<T2(T1)>, std::function<T3(T1)>> Choice2(F0 &&h) {
      return sigT<std::function<T2(T1)>, std::function<T3(T1)>>::existt(
          [=](const T1 &z) mutable { return h(z).projT1(); },
          [=](const T1 &z) mutable {
            sigT<T2, T3> s = h(z);
            auto &[x, a1] = s;
            return a1;
          });
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<Sumbool, F0 &, T1 &>
    static sig<std::function<Bool0(T1)>> bool_choice(F0 &&h) {
      return sig<std::function<Bool0(T1)>>::exist([=](const T1 &z) mutable {
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

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<sig<T1>, F0 &, T1 &>
    static sig<std::function<T1(Nat)>> dependent_choice(F0 &&h, T1 x0) {
      auto f_impl = [=](auto &_self_f, Nat n) mutable -> T1 {
        if (std::holds_alternative<typename Nat::O>(n.v())) {
          return x0;
        } else {
          const auto &[a0] = std::get<typename Nat::S>(n.v());
          return h(_self_f(_self_f, *a0)).proj1_sig();
        }
      };
      auto f = [=](Nat n) mutable -> T1 { return f_impl(f_impl, n); };
      return sig<std::function<T1(Nat)>>::exist(f);
    }

    template <typename a> using Exc = Option<a>;

    template <typename T1> static Option<T1> value(T1 x) {
      return Option<T1>::some(x);
    }

    template <typename T1> static const Option<T1> &error() {
      static const Option<T1> v = Option<T1>::none();
      return v;
    }

    template <typename T1> static const T1 &except() {
      static const T1 v = []() { throw std::logic_error("absurd case"); }();
      return v;
    }

    template <typename T1> static const T1 &absurd_set() {
      static const T1 v = []() { throw std::logic_error("absurd case"); }();
      return v;
    }
  };
};

#endif // INCLUDED_ROCQ_BUG_14174
