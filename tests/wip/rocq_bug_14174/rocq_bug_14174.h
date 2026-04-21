#ifndef INCLUDED_ROCQ_BUG_14174
#define INCLUDED_ROCQ_BUG_14174

#include <any>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

enum class Bool0 { e_TRUE0, e_FALSE0 };

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Nat> o() { return std::make_shared<Nat>(O{}); }

  static std::shared_ptr<Nat> s(const std::shared_ptr<Nat> &a0) {
    return std::make_shared<Nat>(S{a0});
  }

  static std::shared_ptr<Nat> s(std::shared_ptr<Nat> &&a0) {
    return std::make_shared<Nat>(S{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Option {
  // TYPES
  struct Some {
    t_A d_a0;
  };

  struct None {};

  using variant_t = std::variant<Some, None>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Option(Some _v) : d_v_(std::move(_v)) {}

  explicit Option(None _v) : d_v_(_v) {}

  static std::shared_ptr<Option<t_A>> some(t_A a0) {
    return std::make_shared<Option<t_A>>(Some{std::move(a0)});
  }

  static std::shared_ptr<Option<t_A>> none() {
    return std::make_shared<Option<t_A>>(None{});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_B> struct Prod {
  // TYPES
  struct Pair {
    t_A d_a0;
    t_B d_a1;
  };

  using variant_t = std::variant<Pair>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Prod(Pair _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Prod<t_A, t_B>> pair(t_A a0, t_B a1) {
    return std::make_shared<Prod<t_A, t_B>>(Pair{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  t_A fst() const {
    const auto &[d_a0, d_a1] =
        std::get<typename Prod<t_A, t_B>::Pair>(this->v());
    return d_a0;
  }

  t_B snd() const {
    const auto &[d_a0, d_a1] =
        std::get<typename Prod<t_A, t_B>::Pair>(this->v());
    return d_a1;
  }
};

template <typename t_A> struct Sig {
  // TYPES
  struct Exist0 {
    t_A d_x;
  };

  using variant_t = std::variant<Exist0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sig(Exist0 _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig<t_A>> exist0(t_A x) {
    return std::make_shared<Sig<t_A>>(Exist0{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct Sig2 {
  // TYPES
  struct Exist1 {
    t_A d_x;
  };

  using variant_t = std::variant<Exist1>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sig2(Exist1 _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig2<t_A>> exist1(t_A x) {
    return std::make_shared<Sig2<t_A>>(Exist1{std::move(x)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT0 {
    t_A d_x;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT0>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit SigT(ExistT0 _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<SigT<t_A, t_P>> existt0(t_A x, t_P a1) {
    return std::make_shared<SigT<t_A, t_P>>(
        ExistT0{std::move(x), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A, typename t_P, typename t_Q> struct SigT2 {
  // TYPES
  struct ExistT1 {
    t_A d_x;
    t_P d_a1;
    t_Q d_a2;
  };

  using variant_t = std::variant<ExistT1>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit SigT2(ExistT1 _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<SigT2<t_A, t_P, t_Q>> existt1(t_A x, t_P a1, t_Q a2) {
    return std::make_shared<SigT2<t_A, t_P, t_Q>>(
        ExistT1{std::move(x), std::move(a1), std::move(a2)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};
enum class Sumbool { e_LEFT0, e_RIGHT0 };

template <typename t_A> struct Sumor {
  // TYPES
  struct Inleft {
    t_A d_a0;
  };

  struct Inright {};

  using variant_t = std::variant<Inleft, Inright>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sumor(Inleft _v) : d_v_(std::move(_v)) {}

  explicit Sumor(Inright _v) : d_v_(_v) {}

  static std::shared_ptr<Sumor<t_A>> inleft(t_A a0) {
    return std::make_shared<Sumor<t_A>>(Inleft{std::move(a0)});
  }

  static std::shared_ptr<Sumor<t_A>> inright() {
    return std::make_shared<Sumor<t_A>>(Inright{});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct RocqBug14174 {
  struct A {
    template <typename t_A> struct sig {
      // TYPES
      struct Exist {
        t_A d_x;
      };

      using variant_t = std::variant<Exist>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit sig(Exist _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<sig<t_A>> exist(t_A x) {
        return std::make_shared<sig<t_A>>(Exist{std::move(x)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sig_rec_uncurried() const {
        return this->eq_sig_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sig_rect_uncurried(const std::shared_ptr<sig<t_A>> &v,
                               const T1 f) const {
        return this->eq_sig_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sig_rect_exist_r(const t_A v1, const T1 f) const {
        return this->eq_sig_rect(sig<t_A>::exist(v1), f);
      }

      template <typename T1>
      T1 eq_sig_rect_exist_l(const t_A u1, const T1 f) const {
        return sig<t_A>::exist(u1)->eq_sig_rect(this, f);
      }

      template <typename T1> T1 eq_sig_rec() const {
        return this->eq_sig_rect();
      }

      template <typename T1>
      T1 eq_sig_rect(const std::shared_ptr<sig<t_A>> &, const T1 f) const {
        return f;
      }

      t_A proj1_sig() const {
        const auto &[d_x] = std::get<typename sig<t_A>::Exist>(this->v());
        return d_x;
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig_rec(F0 &&f) const {
        const auto &[d_x] = std::get<typename sig<t_A>::Exist>(this->v());
        return f(d_x);
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig_rect(F0 &&f) const {
        const auto &[d_x] = std::get<typename sig<t_A>::Exist>(this->v());
        return f(d_x);
      }
    };

    template <typename t_A> struct sig2 {
      // TYPES
      struct Exist2 {
        t_A d_x;
      };

      using variant_t = std::variant<Exist2>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit sig2(Exist2 _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<sig2<t_A>> exist2(t_A x) {
        return std::make_shared<sig2<t_A>>(Exist2{std::move(x)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sig2_rec_uncurried() const {
        return this->eq_sig2_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sig2_rect_uncurried(const std::shared_ptr<sig2<t_A>> &v,
                                const T1 f) const {
        return this->eq_sig2_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sig2_rect_exist2_r(const t_A v1, const T1 f) const {
        return this->eq_sig2_rect(sig2<t_A>::exist2(v1), f);
      }

      template <typename T1>
      T1 eq_sig2_rect_exist2_l(const t_A u1, const T1 f) const {
        return sig2<t_A>::exist2(u1)->eq_sig2_rect(this, f);
      }

      template <typename T1> T1 eq_sig2_rec() const {
        return this->eq_sig2_rect();
      }

      template <typename T1>
      T1 eq_sig2_rect(const std::shared_ptr<sig2<t_A>> &, const T1 f) const {
        return f;
      }

      std::shared_ptr<sig<t_A>> sig_of_sig2() const {
        return sig<t_A>::exist([&]() {
          const auto &[d_x] = std::get<typename sig2<t_A>::Exist2>(this->v());
          return d_x;
        }());
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig2_rec(F0 &&f) const {
        const auto &[d_x] = std::get<typename sig2<t_A>::Exist2>(this->v());
        return f(d_x);
      }

      template <typename T1, MapsTo<T1, t_A> F0> T1 sig2_rect(F0 &&f) const {
        const auto &[d_x] = std::get<typename sig2<t_A>::Exist2>(this->v());
        return f(d_x);
      }
    };

    template <typename t_A, typename t_P>
    struct sigT : public std::enable_shared_from_this<sigT<t_A, t_P>> {
      // TYPES
      struct ExistT {
        t_A d_x;
        t_P d_a1;
      };

      using variant_t = std::variant<ExistT>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit sigT(ExistT _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<sigT<t_A, t_P>> existt(t_A x, t_P a1) {
        return std::make_shared<sigT<t_A, t_P>>(
            ExistT{std::move(x), std::move(a1)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sigT_rec_uncurried() const {
        return this->eq_sigT_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sigT_rect_uncurried(const std::shared_ptr<sigT<t_A, t_P>> &v,
                                const T1 f) const {
        return this->eq_sigT_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_r(const t_A v1, const t_P v2, const T1 f) const {
        return this->eq_sigT_rect(sigT<t_A, t_P>::existt(v1, v2), f);
      }

      template <typename T1>
      T1 eq_sigT_rect_existT_l(const t_A u1, const t_P u2, const T1 f) const {
        return sigT<t_A, t_P>::existt(u1, u2)->eq_sigT_rect(this, f);
      }

      template <typename T1> T1 eq_sigT_rec() const {
        return this->eq_sigT_rect();
      }

      template <typename T1>
      T1 eq_sigT_rect(const std::shared_ptr<sigT<t_A, t_P>> &,
                      const T1 f) const {
        return f;
      }

      std::shared_ptr<Prod<t_A, t_P>> prod_of_sigT() const {
        return Prod<t_A, t_P>::pair(
            std::const_pointer_cast<sigT<t_A, t_P>>(this->shared_from_this())
                ->projT1(),
            std::const_pointer_cast<sigT<t_A, t_P>>(this->shared_from_this())
                ->projT2());
      }

      t_P projT2() const {
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(this->v());
        return d_a1;
      }

      t_A projT1() const {
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(this->v());
        return d_x;
      }

      template <typename T1, MapsTo<T1, t_A, t_P> F0>
      T1 sigT_rec(F0 &&f) const {
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(this->v());
        return f(d_x, d_a1);
      }

      template <typename T1, MapsTo<T1, t_A, t_P> F0>
      T1 sigT_rect(F0 &&f) const {
        const auto &[d_x, d_a1] =
            std::get<typename sigT<t_A, t_P>::ExistT>(this->v());
        return f(d_x, d_a1);
      }
    };

    template <typename t_A, typename t_P, typename t_Q> struct sigT2 {
      // TYPES
      struct ExistT2 {
        t_A d_x;
        t_P d_a1;
        t_Q d_a2;
      };

      using variant_t = std::variant<ExistT2>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit sigT2(ExistT2 _v) : d_v_(std::move(_v)) {}

      static std::shared_ptr<sigT2<t_A, t_P, t_Q>> existt2(t_A x, t_P a1,
                                                           t_Q a2) {
        return std::make_shared<sigT2<t_A, t_P, t_Q>>(
            ExistT2{std::move(x), std::move(a1), std::move(a2)});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }

      template <typename T1> T1 eq_sigT2_rec_uncurried() const {
        return this->eq_sigT2_rect_uncurried();
      }

      template <typename T1>
      T1 eq_sigT2_rect_uncurried(const std::shared_ptr<sigT2<t_A, t_P, t_Q>> &v,
                                 const T1 f) const {
        return this->eq_sigT2_rect(v, [=]() mutable { return f; }());
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_r(const t_A v1, const t_P v2, const t_Q v3,
                                 const T1 f) const {
        return this->eq_sigT2_rect(sigT2<t_A, t_P, t_Q>::existt2(v1, v2, v3),
                                   f);
      }

      template <typename T1>
      T1 eq_sigT2_rect_existT2_l(const t_A u1, const t_P u2, const t_Q u3,
                                 const T1 f) const {
        return sigT2<t_A, t_P, t_Q>::existt2(u1, u2, u3)
            ->eq_sigT2_rect(this, f);
      }

      template <typename T1> T1 eq_sigT2_rec() const {
        return this->eq_sigT2_rect();
      }

      template <typename T1>
      T1 eq_sigT2_rect(const std::shared_ptr<sigT2<t_A, t_P, t_Q>> &,
                       const T1 f) const {
        return f;
      }

      t_Q projT3() const {
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(this->v());
        return d_a2;
      }

      std::shared_ptr<sigT<t_A, t_P>> sigT_of_sigT2() const {
        return sigT<t_A, t_P>::existt(
            [&]() {
              const auto &[d_x, d_a1, d_a2] =
                  std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(this->v());
              return d_x;
            }(),
            [&]() {
              const auto &[d_x0, d_a10, d_a20] =
                  std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(this->v());
              return d_a10;
            }());
      }

      template <typename T1, MapsTo<T1, t_A, t_P, t_Q> F0>
      T1 sigT2_rec(F0 &&f) const {
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(this->v());
        return f(d_x, d_a1, d_a2);
      }

      template <typename T1, MapsTo<T1, t_A, t_P, t_Q> F0>
      T1 sigT2_rect(F0 &&f) const {
        const auto &[d_x, d_a1, d_a2] =
            std::get<typename sigT2<t_A, t_P, t_Q>::ExistT2>(this->v());
        return f(d_x, d_a1, d_a2);
      }
    };

    using SigTNotations = Coq__1;

    template <typename T1>
    static std::shared_ptr<sig<T1>>
    sig_of_sigT(const std::shared_ptr<sigT<T1, std::any>> &x) {
      return sig<T1>::exist(x->projT1());
    }

    template <typename T1>
    static std::shared_ptr<sigT<T1, std::any>>
    sigT_of_sig(const std::shared_ptr<sig<T1>> &x) {
      return sigT<T1, std::any>::existt(x->proj1_sig(), std::any{});
    }

    template <typename T1>
    static std::shared_ptr<sig2<T1>>
    sig2_of_sigT2(const std::shared_ptr<sigT2<T1, std::any, std::any>> &x) {
      return sig2<T1>::exist2(x->sigT_of_sigT2()->projT1());
    }

    template <typename T1>
    static std::shared_ptr<sigT2<T1, std::any, std::any>>
    sigT2_of_sig2(const std::shared_ptr<sig2<T1>> &x) {
      return sigT2<T1, std::any, std::any>::existt2(
          x->sig_of_sig2()->proj1_sig(), std::any{}, std::any{});
    }

    template <typename T1, typename T2>
    static std::shared_ptr<sigT<T1, T2>>
    sigT_of_prod(const std::shared_ptr<Prod<T1, T2>> &p) {
      return sigT<T1, T2>::existt(p->fst(), p->snd());
    }

    template <typename T1, typename T2, typename T3>
    static T3 eq_sigT_rect_existT(const T1 u1, const T2 u2, const T1 v1,
                                  const T2 v2, const T3 f) {
      return sigT<T1, T2>::existt(u1, u2)->eq_sigT_rect(
          sigT<T1, T2>::existt(v1, v2), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig_rect_exist(const T1 u1, const T1 v1, const T2 f) {
      return sig<T1>::exist(u1)->eq_sig_rect(sig<T1>::exist(v1), f);
    }

    template <typename T1, typename T2, typename T3, typename T4>
    static T4 eq_sigT2_rect_existT2(const T1 u1, const T2 u2, const T3 u3,
                                    const T1 v1, const T2 v2, const T3 v3,
                                    const T4 f) {
      return sigT2<T1, T2, T3>::existt2(u1, u2, u3)
          ->eq_sigT2_rect(sigT2<T1, T2, T3>::existt2(v1, v2, v3), f);
    }

    template <typename T1, typename T2>
    static T2 eq_sig2_rect_exist2(const T1 u1, const T1 v1, const T2 f) {
      return sig2<T1>::exist2(u1)->eq_sig2_rect(sig2<T1>::exist2(v1), f);
    }
    enum class Sumbool { e_LEFT, e_RIGHT };

    template <typename T1>
    static T1 sumbool_rect(const T1 f, const T1 f0, const Sumbool s) {
      switch (s) {
      case Sumbool::e_LEFT: {
        return f;
      }
      case Sumbool::e_RIGHT: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename T1>
    static T1 sumbool_rec(const T1 f, const T1 f0, const Sumbool s) {
      switch (s) {
      case Sumbool::e_LEFT: {
        return f;
      }
      case Sumbool::e_RIGHT: {
        return f0;
      }
      default:
        std::unreachable();
      }
    }

    template <typename t_A> struct sumor {
      // TYPES
      struct Inleft {
        t_A d_a0;
      };

      struct Inright {};

      using variant_t = std::variant<Inleft, Inright>;

    private:
      // DATA
      variant_t d_v_;

    public:
      // CREATORS
      explicit sumor(Inleft _v) : d_v_(std::move(_v)) {}

      explicit sumor(Inright _v) : d_v_(_v) {}

      static std::shared_ptr<sumor<t_A>> inleft(t_A a0) {
        return std::make_shared<sumor<t_A>>(Inleft{std::move(a0)});
      }

      static std::shared_ptr<sumor<t_A>> inright() {
        return std::make_shared<sumor<t_A>>(Inright{});
      }

      // MANIPULATORS
      __attribute__((pure)) variant_t &v_mut() { return d_v_; }

      // ACCESSORS
      __attribute__((pure)) const variant_t &v() const { return d_v_; }

      template <typename T1, MapsTo<T1, t_A> F0>
      T1 sumor_rec(F0 &&f, const T1 f0) const {
        if (std::holds_alternative<typename sumor<t_A>::Inleft>(this->v())) {
          const auto &[d_a0] = std::get<typename sumor<t_A>::Inleft>(this->v());
          return f(d_a0);
        } else {
          return f0;
        }
      }

      template <typename T1, MapsTo<T1, t_A> F0>
      T1 sumor_rect(F0 &&f, const T1 f0) const {
        if (std::holds_alternative<typename sumor<t_A>::Inleft>(this->v())) {
          const auto &[d_a0] = std::get<typename sumor<t_A>::Inleft>(this->v());
          return f(d_a0);
        } else {
          return f0;
        }
      }
    };

    template <typename T1, typename T2, MapsTo<std::shared_ptr<sig<T2>>, T1> F0>
    static std::shared_ptr<sig<std::function<T2(T1)>>> Choice(F0 &&h) {
      return sig<std::function<T2(T1)>>::exist(
          [=](const T1 z) mutable { return h(z)->proj1_sig(); });
    }

    template <typename T1, typename T2, typename T3,
              MapsTo<std::shared_ptr<sigT<T2, T3>>, T1> F0>
    static std::shared_ptr<sigT<std::function<T2(T1)>, std::function<T3(T1)>>>
    Choice2(F0 &&h) {
      return sigT<std::function<T2(T1)>, std::function<T3(T1)>>::existt(
          [=](const T1 z) mutable { return h(z)->projT1(); },
          [=](const T1 z) mutable {
            std::shared_ptr<sigT<T2, T3>> s = h(z);
            const auto &[d_x, d_a1] =
                std::get<typename sigT<T2, T3>::ExistT>(s->v());
            return d_a1;
          });
    }

    template <typename T1, MapsTo<Sumbool, T1> F0>
    static std::shared_ptr<sig<std::function<Bool0(T1)>>> bool_choice(F0 &&h) {
      return sig<std::function<Bool0(T1)>>::exist([=](const T1 z) mutable {
        switch (h(z)) {
        case Sumbool::e_LEFT: {
          return Bool0::e_TRUE0;
        }
        case Sumbool::e_RIGHT: {
          return Bool0::e_FALSE0;
        }
        default:
          std::unreachable();
        }
      });
    }

    template <typename T1, MapsTo<std::shared_ptr<sig<T1>>, T1> F0>
    static std::shared_ptr<sig<std::function<T1(std::shared_ptr<Nat>)>>>
    dependent_choice(F0 &&h, const T1 x0) {
      auto f = std::make_shared<std::function<T1(std::shared_ptr<Nat>)>>();
      *f = [=](std::shared_ptr<Nat> n) mutable -> T1 {
        if (std::holds_alternative<typename Nat::O>(n->v())) {
          return x0;
        } else {
          const auto &[d_a0] = std::get<typename Nat::S>(n->v());
          return h((*f)(d_a0))->proj1_sig();
        }
      };
      return sig<std::function<T1(std::shared_ptr<Nat>)>>::exist(*f);
    }

    template <typename a> using Exc = std::shared_ptr<Option<a>>;

    template <typename T1>
    static std::shared_ptr<Option<T1>> value(const T1 x) {
      return Option<T1>::some(x);
    }

    template <typename T1> static const std::shared_ptr<Option<T1>> &error() {
      static const std::shared_ptr<Option<T1>> v = Option<T1>::none();
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
