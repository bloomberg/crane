#ifndef INCLUDED_FOLD_SEQUENCE_STATE_TRACE
#define INCLUDED_FOLD_SEQUENCE_STATE_TRACE

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A, typename t_B> struct Sum {
  // TYPES
  struct Inl {
    t_A d_a0;
  };

  struct Inr {
    t_B d_a0;
  };

  using variant_t = std::variant<Inl, Inr>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sum(Inl _v) : d_v_(std::move(_v)) {}

  explicit Sum(Inr _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sum<t_A, t_B>> inl(t_A a0) {
    return std::make_shared<Sum<t_A, t_B>>(Inl{std::move(a0)});
  }

  static std::shared_ptr<Sum<t_A, t_B>> inr(t_B a0) {
    return std::make_shared<Sum<t_A, t_B>>(Inr{std::move(a0)});
  }

  static std::unique_ptr<Sum<t_A, t_B>> inl_uptr(t_A a0) {
    return std::make_unique<Sum<t_A, t_B>>(Inl{std::move(a0)});
  }

  static std::unique_ptr<Sum<t_A, t_B>> inr_uptr(t_B a0) {
    return std::make_unique<Sum<t_A, t_B>>(Inr{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<List<t_A>> nil_uptr() {
    return std::make_unique<List<t_A>>(Nil{});
  }

  static std::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              std::shared_ptr<List<t_A>> &&a1) {
    return std::make_unique<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) unsigned int length() const {
    return std::visit(
        Overloaded{[](const typename List<t_A>::Nil _args) -> unsigned int {
                     return 0u;
                   },
                   [](const typename List<t_A>::Cons _args) -> unsigned int {
                     return (_args.d_a1->length() + 1);
                   }},
        this->v());
  }
};
enum class Comparison { e_EQ, e_LT, e_GT };

template <typename t_A> struct Sig {
  // TYPES
  struct Exist {
    t_A d_a0;
  };

  using variant_t = std::variant<Exist>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Sig(Exist _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sig<t_A>> exist(t_A a0) {
    return std::make_shared<Sig<t_A>>(Exist{std::move(a0)});
  }

  static std::unique_ptr<Sig<t_A>> exist_uptr(t_A a0) {
    return std::make_unique<Sig<t_A>>(Exist{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

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

  explicit Sumor(Inright _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Sumor<t_A>> inleft(t_A a0) {
    return std::make_shared<Sumor<t_A>>(Inleft{std::move(a0)});
  }

  static std::shared_ptr<Sumor<t_A>> inright() {
    return std::make_shared<Sumor<t_A>>(Inright{});
  }

  static std::unique_ptr<Sumor<t_A>> inleft_uptr(t_A a0) {
    return std::make_unique<Sumor<t_A>>(Inleft{std::move(a0)});
  }

  static std::unique_ptr<Sumor<t_A>> inright_uptr() {
    return std::make_unique<Sumor<t_A>>(Inright{});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct PeanoNat {
  __attribute__((pure)) static unsigned int add(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static unsigned int mul(const unsigned int n,
                                                const unsigned int m);
  __attribute__((pure)) static bool eqb(const unsigned int n,
                                        const unsigned int m);
  __attribute__((pure)) static unsigned int pow(const unsigned int n,
                                                const unsigned int m);
};

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> d_a0;
  };

  struct XO {
    std::shared_ptr<Positive> d_a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Positive(XI _v) : d_v_(std::move(_v)) {}

  explicit Positive(XO _v) : d_v_(std::move(_v)) {}

  explicit Positive(XH _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Positive> xi(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Positive>(XI{a0});
  }

  static std::shared_ptr<Positive> xi(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Positive>(XI{std::move(a0)});
  }

  static std::shared_ptr<Positive> xo(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Positive>(XO{a0});
  }

  static std::shared_ptr<Positive> xo(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Positive>(XO{std::move(a0)});
  }

  static std::shared_ptr<Positive> xh() {
    return std::make_shared<Positive>(XH{});
  }

  static std::unique_ptr<Positive>
  xi_uptr(const std::shared_ptr<Positive> &a0) {
    return std::make_unique<Positive>(XI{a0});
  }

  static std::unique_ptr<Positive> xi_uptr(std::shared_ptr<Positive> &&a0) {
    return std::make_unique<Positive>(XI{std::move(a0)});
  }

  static std::unique_ptr<Positive>
  xo_uptr(const std::shared_ptr<Positive> &a0) {
    return std::make_unique<Positive>(XO{a0});
  }

  static std::unique_ptr<Positive> xo_uptr(std::shared_ptr<Positive> &&a0) {
    return std::make_unique<Positive>(XO{std::move(a0)});
  }

  static std::unique_ptr<Positive> xh_uptr() {
    return std::make_unique<Positive>(XH{});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    std::shared_ptr<Positive> d_a0;
  };

  struct Zneg {
    std::shared_ptr<Positive> d_a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit Z(Z0 _v) : d_v_(std::move(_v)) {}

  explicit Z(Zpos _v) : d_v_(std::move(_v)) {}

  explicit Z(Zneg _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<Z> z0() { return std::make_shared<Z>(Z0{}); }

  static std::shared_ptr<Z> zpos(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Z>(Zpos{a0});
  }

  static std::shared_ptr<Z> zpos(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Z>(Zpos{std::move(a0)});
  }

  static std::shared_ptr<Z> zneg(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<Z>(Zneg{a0});
  }

  static std::shared_ptr<Z> zneg(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<Z>(Zneg{std::move(a0)});
  }

  static std::unique_ptr<Z> z0_uptr() { return std::make_unique<Z>(Z0{}); }

  static std::unique_ptr<Z> zpos_uptr(const std::shared_ptr<Positive> &a0) {
    return std::make_unique<Z>(Zpos{a0});
  }

  static std::unique_ptr<Z> zpos_uptr(std::shared_ptr<Positive> &&a0) {
    return std::make_unique<Z>(Zpos{std::move(a0)});
  }

  static std::unique_ptr<Z> zneg_uptr(const std::shared_ptr<Positive> &a0) {
    return std::make_unique<Z>(Zneg{a0});
  }

  static std::unique_ptr<Z> zneg_uptr(std::shared_ptr<Positive> &&a0) {
    return std::make_unique<Z>(Zneg{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  __attribute__((pure)) bool Z_lt_le_dec(const std::shared_ptr<Z> &y) const {
    if (this->Z_lt_ge_dec(y)) {
      return true;
    } else {
      return false;
    }
  }

  __attribute__((pure)) bool Z_lt_ge_dec() const { return this->Z_lt_dec(); }

  __attribute__((pure)) bool Z_lt_dec(const std::shared_ptr<Z> &y) const {
    return [&](void) {
      switch (BinInt::compare(this, y)) {
      case Comparison::e_EQ: {
        return false;
      }
      case Comparison::e_LT: {
        return true;
      }
      case Comparison::e_GT: {
        return false;
      }
      }
    }();
  }
};

struct Pos {
  static std::shared_ptr<Positive> succ(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<Positive> add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  add_carry(const std::shared_ptr<Positive> &x,
            const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  pred_double(const std::shared_ptr<Positive> &x);

  struct mask {
    // TYPES
    struct IsNul0 {};

    struct IsPos0 {
      std::shared_ptr<Positive> d_a0;
    };

    struct IsNeg0 {};

    using variant_t = std::variant<IsNul0, IsPos0, IsNeg0>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mask(IsNul0 _v) : d_v_(std::move(_v)) {}

    explicit mask(IsPos0 _v) : d_v_(std::move(_v)) {}

    explicit mask(IsNeg0 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mask> isnul0() {
      return std::make_shared<mask>(IsNul0{});
    }

    static std::shared_ptr<mask> ispos0(const std::shared_ptr<Positive> &a0) {
      return std::make_shared<mask>(IsPos0{a0});
    }

    static std::shared_ptr<mask> ispos0(std::shared_ptr<Positive> &&a0) {
      return std::make_shared<mask>(IsPos0{std::move(a0)});
    }

    static std::shared_ptr<mask> isneg0() {
      return std::make_shared<mask>(IsNeg0{});
    }

    static std::unique_ptr<mask> isnul0_uptr() {
      return std::make_unique<mask>(IsNul0{});
    }

    static std::unique_ptr<mask>
    ispos0_uptr(const std::shared_ptr<Positive> &a0) {
      return std::make_unique<mask>(IsPos0{a0});
    }

    static std::unique_ptr<mask> ispos0_uptr(std::shared_ptr<Positive> &&a0) {
      return std::make_unique<mask>(IsPos0{std::move(a0)});
    }

    static std::unique_ptr<mask> isneg0_uptr() {
      return std::make_unique<mask>(IsNeg0{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  static std::shared_ptr<Positive> mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
               const std::shared_ptr<Positive> &y);
  __attribute__((pure)) static Comparison
  compare(const std::shared_ptr<Positive> &_x0,
          const std::shared_ptr<Positive> &_x1);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive> &p, const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::XI _args) -> T1 {
                     return op(a, iter_op<T1>(op, _args.d_a0, op(a, a)));
                   },
                   [&](const typename Positive::XO _args) -> T1 {
                     return iter_op<T1>(op, _args.d_a0, op(a, a));
                   },
                   [&](const typename Positive::XH _args) -> T1 { return a; }},
        p->v());
  }

  __attribute__((pure)) static unsigned int
  to_nat(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<Positive> of_succ_nat(const unsigned int n);
};

struct Coq_Pos {
  static std::shared_ptr<Positive> succ(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<Positive> add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  add_carry(const std::shared_ptr<Positive> &x,
            const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  pred_double(const std::shared_ptr<Positive> &x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      std::shared_ptr<Positive> d_a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit mask(IsNul _v) : d_v_(std::move(_v)) {}

    explicit mask(IsPos _v) : d_v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<mask> isnul() {
      return std::make_shared<mask>(IsNul{});
    }

    static std::shared_ptr<mask> ispos(const std::shared_ptr<Positive> &a0) {
      return std::make_shared<mask>(IsPos{a0});
    }

    static std::shared_ptr<mask> ispos(std::shared_ptr<Positive> &&a0) {
      return std::make_shared<mask>(IsPos{std::move(a0)});
    }

    static std::shared_ptr<mask> isneg() {
      return std::make_shared<mask>(IsNeg{});
    }

    static std::unique_ptr<mask> isnul_uptr() {
      return std::make_unique<mask>(IsNul{});
    }

    static std::unique_ptr<mask>
    ispos_uptr(const std::shared_ptr<Positive> &a0) {
      return std::make_unique<mask>(IsPos{a0});
    }

    static std::unique_ptr<mask> ispos_uptr(std::shared_ptr<Positive> &&a0) {
      return std::make_unique<mask>(IsPos{std::move(a0)});
    }

    static std::unique_ptr<mask> isneg_uptr() {
      return std::make_unique<mask>(IsNeg{});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  static std::shared_ptr<mask> succ_double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask> double_mask(const std::shared_ptr<mask> &x);
  static std::shared_ptr<mask>
  double_pred_mask(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<mask> sub_mask(const std::shared_ptr<Positive> &x,
                                        const std::shared_ptr<Positive> &y);
  static std::shared_ptr<mask>
  sub_mask_carry(const std::shared_ptr<Positive> &x,
                 const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive> sub(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive> mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const std::shared_ptr<Positive> &x,
               const std::shared_ptr<Positive> &y);
  __attribute__((pure)) static Comparison
  compare(const std::shared_ptr<Positive> &_x0,
          const std::shared_ptr<Positive> &_x1);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive> &p, const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::XI _args) -> T1 {
                     return op(a, iter_op<T1>(op, _args.d_a0, op(a, a)));
                   },
                   [&](const typename Positive::XO _args) -> T1 {
                     return iter_op<T1>(op, _args.d_a0, op(a, a));
                   },
                   [&](const typename Positive::XH _args) -> T1 { return a; }},
        p->v());
  }

  __attribute__((pure)) static unsigned int
  to_nat(const std::shared_ptr<Positive> &x);
  __attribute__((pure)) static unsigned int
  size_nat(const std::shared_ptr<Positive> &p);
  __attribute__((pure)) static std::pair<
      std::shared_ptr<Positive>,
      std::pair<std::shared_ptr<Positive>, std::shared_ptr<Positive>>>
  ggcdn(const unsigned int n, std::shared_ptr<Positive> a,
        std::shared_ptr<Positive> b);
  __attribute__((pure)) static std::pair<
      std::shared_ptr<Positive>,
      std::pair<std::shared_ptr<Positive>, std::shared_ptr<Positive>>>
  ggcd(const std::shared_ptr<Positive> &a, const std::shared_ptr<Positive> &b);
  static std::shared_ptr<Positive> of_nat(const unsigned int n);
};

struct BinInt {
  static std::shared_ptr<Z> double_(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> succ_double(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> pred_double(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> pos_sub(const std::shared_ptr<Positive> &x,
                                    const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Z> add(std::shared_ptr<Z> x, std::shared_ptr<Z> y);
  static std::shared_ptr<Z> opp(const std::shared_ptr<Z> &x);
  static std::shared_ptr<Z> sub(const std::shared_ptr<Z> &m,
                                const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> mul(const std::shared_ptr<Z> &x,
                                const std::shared_ptr<Z> &y);
  __attribute__((pure)) static Comparison compare(const std::shared_ptr<Z> &x,
                                                  const std::shared_ptr<Z> &y);
  static std::shared_ptr<Z> max(std::shared_ptr<Z> n, std::shared_ptr<Z> m);
  __attribute__((pure)) static unsigned int to_nat(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> of_nat(const unsigned int n);
  static std::shared_ptr<Positive> to_pos(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> sgn(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> abs(const std::shared_ptr<Z> &z);
  __attribute__((pure)) static std::pair<
      std::shared_ptr<Z>, std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>>
  ggcd(std::shared_ptr<Z> a, std::shared_ptr<Z> b);
};

struct Ring_theory {
  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 pow_pos(F0 &&rmul, const T1 x, const std::shared_ptr<Positive> &i);
};

struct ConstructiveExtra {
  static std::shared_ptr<Z> Z_inj_nat_rev(const unsigned int n);
};

struct Q {
  std::shared_ptr<Z> Qnum;
  std::shared_ptr<Positive> Qden;
};

struct Qreduction {
  static std::shared_ptr<Q> Qred(const std::shared_ptr<Q> &q);
};

struct Qabs {
  static std::shared_ptr<Q> Qabs(const std::shared_ptr<Q> &x);
};

struct QExtra {
  static std::shared_ptr<Positive>
  Pos_log2floor_plus1(const std::shared_ptr<Positive> &p);
  static std::shared_ptr<Z> Qbound_lt_ZExp2(const std::shared_ptr<Q> &q);
  static std::shared_ptr<Z> Qbound_ltabs_ZExp2(const std::shared_ptr<Q> &q);
};

struct CReal {
  std::function<std::shared_ptr<Q>(std::shared_ptr<Z>)> seq;
  std::shared_ptr<Z> scale;
};

using CRealLt = std::shared_ptr<Sig<std::shared_ptr<Z>>>;
using DReal = std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>>;

struct ConstructiveCauchyRealsMult {
  static std::shared_ptr<Q> CReal_mult_seq(const std::shared_ptr<CReal> &x,
                                           const std::shared_ptr<CReal> &y,
                                           const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> CReal_mult_scale(const std::shared_ptr<CReal> &x,
                                             const std::shared_ptr<CReal> &y);
  static std::shared_ptr<CReal> CReal_mult(std::shared_ptr<CReal> x,
                                           std::shared_ptr<CReal> y);
};

template <typename M>
concept RbaseSymbolsSig = requires {
  typename M::R;
  {
    M::Rabst(std::declval<std::shared_ptr<typename M::CReal>>())
  } -> std::same_as<typename M::R>;
  {
    M::Rrepr(std::declval<typename M::R>())
  } -> std::same_as<std::shared_ptr<typename M::CReal>>;
  requires(
      requires {
        { M::R0 } -> std::convertible_to<typename M::R>;
      } ||
      requires {
        { M::R0() } -> std::convertible_to<typename M::R>;
      });
  requires(
      requires {
        { M::R1 } -> std::convertible_to<typename M::R>;
      } ||
      requires {
        { M::R1() } -> std::convertible_to<typename M::R>;
      });
  {
    M::Rplus(std::declval<typename M::R>(), std::declval<typename M::R>())
  } -> std::same_as<typename M::R>;
  {
    M::Rmult(std::declval<typename M::R>(), std::declval<typename M::R>())
  } -> std::same_as<typename M::R>;
  { M::Ropp(std::declval<typename M::R>()) } -> std::same_as<typename M::R>;
};

struct RbaseSymbolsImpl {
  using R = DReal;
  __attribute__((pure)) static DReal Rabst(const std::shared_ptr<CReal> &_x0);
  static std::shared_ptr<CReal> Rrepr(const DReal _x0);
  static inline const std::any Rquot1 =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const std::any Rquot2 =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const R R0 = Rabst(ConstructiveCauchyReals::inject_Q(
      std::make_shared<Q>(Q{Z::z0(), Positive::xh()})));
  static inline const R R1 = Rabst(ConstructiveCauchyReals::inject_Q(
      std::make_shared<Q>(Q{Z::zpos(Positive::xh()), Positive::xh()})));
  __attribute__((pure)) static R
  Rplus(const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
        const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &y);
  __attribute__((pure)) static R
  Rmult(const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
        const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &y);
  __attribute__((pure)) static R
  Ropp(const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x);
  static inline const std::any R0_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const std::any R1_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const std::any Rplus_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const std::any Rmult_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const std::any Ropp_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
  static inline const std::any Rlt_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
};

static_assert(RbaseSymbolsSig<RbaseSymbolsImpl>);
__attribute__((pure)) RbaseSymbolsImpl::R Rminus(const RbaseSymbolsImpl::R r1,
                                                 const RbaseSymbolsImpl::R r2);
__attribute__((pure)) RbaseSymbolsImpl::R
IPR_2(const std::shared_ptr<Positive> &p);
__attribute__((pure)) RbaseSymbolsImpl::R
IPR(const std::shared_ptr<Positive> &p);
__attribute__((pure)) RbaseSymbolsImpl::R IZR(const std::shared_ptr<Z> &z);
std::shared_ptr<Sumor<bool>> total_order_T(const RbaseSymbolsImpl::R r1,
                                           const RbaseSymbolsImpl::R r2);

struct RIneq {
  __attribute__((pure)) static bool Req_dec_T(const RbaseSymbolsImpl::R r1,
                                              const RbaseSymbolsImpl::R r2);
};

struct QArith_base {
  static std::shared_ptr<Q> Qplus(std::shared_ptr<Q> x, std::shared_ptr<Q> y);
  static std::shared_ptr<Q> Qmult(std::shared_ptr<Q> x, std::shared_ptr<Q> y);
  static std::shared_ptr<Q> Qopp(std::shared_ptr<Q> x);
  static std::shared_ptr<Q> Qminus(const std::shared_ptr<Q> &x,
                                   const std::shared_ptr<Q> &y);
  static std::shared_ptr<Q> Qinv(std::shared_ptr<Q> x);
  __attribute__((pure)) static bool Qlt_le_dec(std::shared_ptr<Q> x,
                                               std::shared_ptr<Q> y);
  static std::shared_ptr<Sig<std::shared_ptr<Positive>>>
  Qarchimedean(const std::shared_ptr<Q> &q);
  static std::shared_ptr<Q>
  Qpower_positive(const std::shared_ptr<Q> &_x0,
                  const std::shared_ptr<Positive> &_x1);
  static std::shared_ptr<Q> Qpower(const std::shared_ptr<Q> &q,
                                   const std::shared_ptr<Z> &z);
};

struct ClassicalDedekindReals {
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>
  sig_forall_dec(F0 &&_x0);
  template <MapsTo<bool, std::shared_ptr<Q>> F0>
  static std::shared_ptr<Sig<std::shared_ptr<Q>>> lowerCutBelow(F0 &&f);
  template <MapsTo<bool, std::shared_ptr<Q>> F0>
  static std::shared_ptr<Sig<std::shared_ptr<Q>>> lowerCutAbove(F0 &&f);
  template <MapsTo<bool, std::shared_ptr<Q>> F0>
  static std::shared_ptr<Sig<std::shared_ptr<Q>>>
  DRealQlim_rec(F0 &&f, const unsigned int n, const unsigned int p);
  __attribute__((pure)) static DReal DRealAbstr(std::shared_ptr<CReal> x);
  static std::shared_ptr<Sig<std::shared_ptr<Q>>> DRealQlim(
      const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
      const unsigned int n);
  static std::shared_ptr<Sig<std::shared_ptr<Q>>> DRealQlimExp2(
      const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
      const unsigned int n);
  static std::shared_ptr<Q> CReal_of_DReal_seq(
      const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x,
      const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> CReal_of_DReal_scale(
      const std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> &x);
  static std::shared_ptr<CReal>
  DRealRepr(std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>> x);
};

struct ConstructiveCauchyReals {
  template <MapsTo<std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>,
                   std::function<bool(unsigned int)>>
                F2>
  static std::shared_ptr<Sum<CRealLt, std::any>>
  CRealLt_lpo_dec(std::shared_ptr<CReal> x, std::shared_ptr<CReal> y, F2 &&lpo);
  static std::shared_ptr<CReal> inject_Q(std::shared_ptr<Q> q);
  static std::shared_ptr<Q> CReal_plus_seq(const std::shared_ptr<CReal> &x,
                                           const std::shared_ptr<CReal> &y,
                                           const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> CReal_plus_scale(const std::shared_ptr<CReal> &x,
                                             const std::shared_ptr<CReal> &y);
  static std::shared_ptr<CReal> CReal_plus(std::shared_ptr<CReal> x,
                                           std::shared_ptr<CReal> y);
  static std::shared_ptr<Q> CReal_opp_seq(const std::shared_ptr<CReal> &x,
                                          const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> CReal_opp_scale(const std::shared_ptr<CReal> &x);
  static std::shared_ptr<CReal> CReal_opp(std::shared_ptr<CReal> x);
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
};

struct FoldSequenceStateTraceCase {
  using Point = std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>;

  struct Line {
    RbaseSymbolsImpl::R A;
    RbaseSymbolsImpl::R B;
    RbaseSymbolsImpl::R C;
  };

  struct Fold {
    // TYPES
    struct Fold_line_ctor {
      std::shared_ptr<Line> d_a0;
    };

    using variant_t = std::variant<Fold_line_ctor>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit Fold(Fold_line_ctor _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<Fold>
    fold_line_ctor(const std::shared_ptr<Line> &a0) {
      return std::make_shared<Fold>(Fold_line_ctor{a0});
    }

    static std::shared_ptr<Fold> fold_line_ctor(std::shared_ptr<Line> &&a0) {
      return std::make_shared<Fold>(Fold_line_ctor{std::move(a0)});
    }

    static std::unique_ptr<Fold>
    fold_line_ctor_uptr(const std::shared_ptr<Line> &a0) {
      return std::make_unique<Fold>(Fold_line_ctor{a0});
    }

    static std::unique_ptr<Fold>
    fold_line_ctor_uptr(std::shared_ptr<Line> &&a0) {
      return std::make_unique<Fold>(Fold_line_ctor{std::move(a0)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<Line> fold_line() const {
      return std::visit(
          Overloaded{[](const typename Fold::Fold_line_ctor _args)
                         -> std::shared_ptr<Line> { return _args.d_a0; }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<Line>> F0>
    T1 Fold_rec(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename Fold::Fold_line_ctor _args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }

    template <typename T1, MapsTo<T1, std::shared_ptr<Line>> F0>
    T1 Fold_rect(F0 &&f) const {
      return std::visit(
          Overloaded{[&](const typename Fold::Fold_line_ctor _args) -> T1 {
            return f(_args.d_a0);
          }},
          this->v());
    }
  };

  static inline const std::shared_ptr<Line> line_xaxis = std::make_shared<Line>(
      Line{IZR(Z::z0()), IZR(Z::zpos(Positive::xh())), IZR(Z::z0())});
  static inline const std::shared_ptr<Line> line_yaxis = std::make_shared<Line>(
      Line{IZR(Z::zpos(Positive::xh())), IZR(Z::z0()), IZR(Z::z0())});
  static inline const Point point_O =
      std::make_pair(IZR(Z::z0()), IZR(Z::z0()));
  static inline const Point point_X =
      std::make_pair(IZR(Z::zpos(Positive::xh())), IZR(Z::z0()));
  static inline const Point point_diag = std::make_pair(
      IZR(Z::zpos(Positive::xh())), IZR(Z::zpos(Positive::xh())));
  static std::shared_ptr<Line>
  line_through(const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
               const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2);
  static std::shared_ptr<Line>
  perp_bisector(const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
                const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2);
  static std::shared_ptr<Line>
  perp_through(const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p,
               std::shared_ptr<Line> l);
  static std::shared_ptr<Fold>
  fold_O1(const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
          const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2);
  static std::shared_ptr<Fold>
  fold_O2(const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p1,
          const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p2);
  static std::shared_ptr<Fold>
  fold_O4(const std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> p,
          std::shared_ptr<Line> l);

  struct FoldStep {
    // TYPES
    struct FS_O1 {
      Point d_a0;
      Point d_a1;
    };

    struct FS_O2 {
      Point d_a0;
      Point d_a1;
    };

    struct FS_O4 {
      Point d_a0;
      std::shared_ptr<Line> d_a1;
    };

    using variant_t = std::variant<FS_O1, FS_O2, FS_O4>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    explicit FoldStep(FS_O1 _v) : d_v_(std::move(_v)) {}

    explicit FoldStep(FS_O2 _v) : d_v_(std::move(_v)) {}

    explicit FoldStep(FS_O4 _v) : d_v_(std::move(_v)) {}

    static std::shared_ptr<FoldStep> fs_o1(Point a0, Point a1) {
      return std::make_shared<FoldStep>(FS_O1{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<FoldStep> fs_o2(Point a0, Point a1) {
      return std::make_shared<FoldStep>(FS_O2{std::move(a0), std::move(a1)});
    }

    static std::shared_ptr<FoldStep> fs_o4(Point a0,
                                           const std::shared_ptr<Line> &a1) {
      return std::make_shared<FoldStep>(FS_O4{std::move(a0), a1});
    }

    static std::shared_ptr<FoldStep> fs_o4(Point a0,
                                           std::shared_ptr<Line> &&a1) {
      return std::make_shared<FoldStep>(FS_O4{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<FoldStep> fs_o1_uptr(Point a0, Point a1) {
      return std::make_unique<FoldStep>(FS_O1{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<FoldStep> fs_o2_uptr(Point a0, Point a1) {
      return std::make_unique<FoldStep>(FS_O2{std::move(a0), std::move(a1)});
    }

    static std::unique_ptr<FoldStep>
    fs_o4_uptr(Point a0, const std::shared_ptr<Line> &a1) {
      return std::make_unique<FoldStep>(FS_O4{std::move(a0), a1});
    }

    static std::unique_ptr<FoldStep> fs_o4_uptr(Point a0,
                                                std::shared_ptr<Line> &&a1) {
      return std::make_unique<FoldStep>(FS_O4{std::move(a0), std::move(a1)});
    }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }

    std::shared_ptr<Line> execute_fold_step() const {
      return std::visit(
          Overloaded{[](const typename FoldStep::FS_O1 _args)
                         -> std::shared_ptr<Line> {
                       return fold_O1(_args.d_a0, _args.d_a1)->fold_line();
                     },
                     [](const typename FoldStep::FS_O2 _args)
                         -> std::shared_ptr<Line> {
                       return fold_O2(_args.d_a0, _args.d_a1)->fold_line();
                     },
                     [](const typename FoldStep::FS_O4 _args)
                         -> std::shared_ptr<Line> {
                       return fold_O4(_args.d_a0, _args.d_a1)->fold_line();
                     }},
          this->v());
    }
  };

  template <typename T1,
            MapsTo<T1, std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>,
                   std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>>
                F0,
            MapsTo<T1, std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>,
                   std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>>
                F1,
            MapsTo<T1, std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>,
                   std::shared_ptr<Line>>
                F2>
  static T1 FoldStep_rect(F0 &&f, F1 &&f0, F2 &&f1,
                          const std::shared_ptr<FoldStep> &f2) {
    return std::visit(
        Overloaded{[&](const typename FoldStep::FS_O1 _args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O2 _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O4 _args) -> T1 {
                     return f1(_args.d_a0, _args.d_a1);
                   }},
        f2->v());
  }

  template <typename T1,
            MapsTo<T1, std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>,
                   std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>>
                F0,
            MapsTo<T1, std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>,
                   std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>>
                F1,
            MapsTo<T1, std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>,
                   std::shared_ptr<Line>>
                F2>
  static T1 FoldStep_rec(F0 &&f, F1 &&f0, F2 &&f1,
                         const std::shared_ptr<FoldStep> &f2) {
    return std::visit(
        Overloaded{[&](const typename FoldStep::FS_O1 _args) -> T1 {
                     return f(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O2 _args) -> T1 {
                     return f0(_args.d_a0, _args.d_a1);
                   },
                   [&](const typename FoldStep::FS_O4 _args) -> T1 {
                     return f1(_args.d_a0, _args.d_a1);
                   }},
        f2->v());
  }

  using FoldSequence = std::shared_ptr<List<std::shared_ptr<FoldStep>>>;

  struct ConstructionState {
    std::shared_ptr<List<Point>> state_points;
    std::shared_ptr<List<std::shared_ptr<Line>>> state_lines;
  };

  static inline const std::shared_ptr<ConstructionState> initial_state =
      std::make_shared<ConstructionState>(ConstructionState{
          List<std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>>::cons(
              point_O,
              List<std::pair<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R>>::cons(
                  point_X, List<std::pair<RbaseSymbolsImpl::R,
                                          RbaseSymbolsImpl::R>>::nil())),
          List<std::shared_ptr<Line>>::cons(
              line_xaxis,
              List<std::shared_ptr<Line>>::cons(
                  line_yaxis, List<std::shared_ptr<Line>>::nil()))});
  static std::shared_ptr<ConstructionState>
  add_fold_to_state(std::shared_ptr<ConstructionState> st,
                    const std::shared_ptr<FoldStep> &step);
  static std::shared_ptr<ConstructionState> execute_sequence(
      std::shared_ptr<ConstructionState> st,
      const std::shared_ptr<List<std::shared_ptr<FoldStep>>> &seq0);
  static inline const FoldSequence sample_sequence =
      List<std::shared_ptr<FoldStep>>::cons(
          FoldStep::fs_o1(point_O, point_diag),
          List<std::shared_ptr<FoldStep>>::cons(
              FoldStep::fs_o2(point_O, point_X),
              List<std::shared_ptr<FoldStep>>::cons(
                  FoldStep::fs_o4(point_diag, line_xaxis),
                  List<std::shared_ptr<FoldStep>>::nil())));
  static inline const std::shared_ptr<ConstructionState> sample_final_state =
      execute_sequence(initial_state, sample_sequence);
  __attribute__((pure)) static unsigned int line_count_after_sample_sequence(
      const std::shared_ptr<ConstructionState> &st);
  static inline const unsigned int sample_sequence_length =
      sample_sequence->length();
  static inline const unsigned int sample_line_count =
      line_count_after_sample_sequence(initial_state);
  static inline const unsigned int sample_point_count =
      sample_final_state->state_points->length();
  static inline const bool sample_lines_nonempty =
      !(PeanoNat::eqb(sample_line_count, 0u));
  static inline const bool sample_has_expected_lines =
      PeanoNat::eqb(sample_line_count, 5u);
};

template <typename T1, MapsTo<T1, T1, T1> F0>
T1 Ring_theory::pow_pos(F0 &&rmul, const T1 x,
                        const std::shared_ptr<Positive> &i) {
  return std::visit(
      Overloaded{[&](const typename Positive::XI _args) -> T1 {
                   T1 p =
                       Ring_theory::template pow_pos<T1>(rmul, x, _args.d_a0);
                   return rmul(x, rmul(p, p));
                 },
                 [&](const typename Positive::XO _args) -> T1 {
                   T1 p =
                       Ring_theory::template pow_pos<T1>(rmul, x, _args.d_a0);
                   return rmul(p, p);
                 },
                 [&](const typename Positive::XH _args) -> T1 { return x; }},
      i->v());
}

template <MapsTo<std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>,
                 std::function<bool(unsigned int)>>
              F2>
std::shared_ptr<Sum<ConstructiveCauchyReals::CRealLt, std::any>>
ConstructiveCauchyReals::CRealLt_lpo_dec(std::shared_ptr<CReal> x,
                                         std::shared_ptr<CReal> y, F2 &&lpo) {
  std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>> s =
      lpo([=](unsigned int n) mutable {
        bool s = QArith_base::Qlt_le_dec(
            QArith_base::Qmult(
                std::make_shared<Q>(
                    Q{Z::zpos(Positive::xo(Positive::xh())), Positive::xh()}),
                QArith_base::Qpower(
                    std::make_shared<Q>(Q{Z::zpos(Positive::xo(Positive::xh())),
                                          Positive::xh()}),
                    ConstructiveExtra::Z_inj_nat_rev(n))),
            QArith_base::Qminus(y->seq(ConstructiveExtra::Z_inj_nat_rev(n)),
                                x->seq(ConstructiveExtra::Z_inj_nat_rev(n))));
        if (s) {
          return false;
        } else {
          return true;
        }
      });
  return std::visit(
      Overloaded{
          [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inleft
                 _args)
              -> std::shared_ptr<
                  Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>> {
            return Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>::inl(
                std::visit(
                    Overloaded{
                        [](const typename Sig<unsigned int>::Exist _args0)
                            -> std::shared_ptr<Sig<std::shared_ptr<Z>>> {
                          return Sig<std::shared_ptr<Z>>::exist(
                              ConstructiveExtra::Z_inj_nat_rev(_args0.d_a0));
                        }},
                    _args.d_a0->v()));
          },
          [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inright
                 _args)
              -> std::shared_ptr<
                  Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>> {
            return Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>, std::any>::inr(
                std::any{});
          }},
      std::move(s)->v());
}

template <MapsTo<bool, unsigned int> F0>
std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>
ClassicalDedekindReals::sig_forall_dec(F0 &&_x0) {
  throw std::logic_error(
      "unrealized axiom: Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec");
}

template <MapsTo<bool, std::shared_ptr<Q>> F0>
std::shared_ptr<Sig<std::shared_ptr<Q>>>
ClassicalDedekindReals::lowerCutBelow(F0 &&f) {
  std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>> s =
      ClassicalDedekindReals::sig_forall_dec([=](unsigned int n) mutable {
        bool b = f(QArith_base::Qopp(
            std::make_shared<Q>(Q{BinInt::of_nat(n), Positive::xh()})));
        if (b) {
          return false;
        } else {
          return true;
        }
      });
  return std::visit(
      Overloaded{
          [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inleft
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
            return std::visit(
                Overloaded{[](const typename Sig<unsigned int>::Exist _args0)
                               -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                  return Sig<std::shared_ptr<Q>>::exist(
                      QArith_base::Qopp(std::make_shared<Q>(
                          Q{BinInt::of_nat(_args0.d_a0), Positive::xh()})));
                }},
                _args.d_a0->v());
          },
          [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inright
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
            throw std::logic_error("absurd case");
          }},
      std::move(s)->v());
}

template <MapsTo<bool, std::shared_ptr<Q>> F0>
std::shared_ptr<Sig<std::shared_ptr<Q>>>
ClassicalDedekindReals::lowerCutAbove(F0 &&f) {
  std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>> s =
      ClassicalDedekindReals::sig_forall_dec([=](unsigned int n) mutable {
        bool b = f(std::make_shared<Q>(Q{BinInt::of_nat(n), Positive::xh()}));
        if (b) {
          return true;
        } else {
          return false;
        }
      });
  return std::visit(
      Overloaded{
          [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inleft
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
            return std::visit(
                Overloaded{[](const typename Sig<unsigned int>::Exist _args0)
                               -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                  return Sig<std::shared_ptr<Q>>::exist(std::make_shared<Q>(
                      Q{BinInt::of_nat(_args0.d_a0), Positive::xh()}));
                }},
                _args.d_a0->v());
          },
          [](const typename Sumor<std::shared_ptr<Sig<unsigned int>>>::Inright
                 _args) -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
            throw std::logic_error("absurd case");
          }},
      std::move(s)->v());
}

template <MapsTo<bool, std::shared_ptr<Q>> F0>
std::shared_ptr<Sig<std::shared_ptr<Q>>>
ClassicalDedekindReals::DRealQlim_rec(F0 &&f, const unsigned int n,
                                      const unsigned int p) {
  if (p <= 0) {
    throw std::logic_error("absurd case");
  } else {
    unsigned int n0 = p - 1;
    bool b = f(QArith_base::Qplus(
        std::visit(Overloaded{[](const typename Sig<std::shared_ptr<Q>>::Exist
                                     _args) -> auto { return _args.d_a0; }},
                   ClassicalDedekindReals::lowerCutBelow(f)->v()),
        std::make_shared<Q>(Q{BinInt::of_nat(n0), Coq_Pos::of_nat((n + 1))})));
    if (std::move(b)) {
      return Sig<std::shared_ptr<Q>>::exist(QArith_base::Qplus(
          std::visit(Overloaded{[](const typename Sig<std::shared_ptr<Q>>::Exist
                                       _args0) -> auto { return _args0.d_a0; }},
                     ClassicalDedekindReals::lowerCutBelow(f)->v()),
          std::make_shared<Q>(
              Q{BinInt::of_nat(n0), Coq_Pos::of_nat((n + 1))})));
    } else {
      std::shared_ptr<Sig<std::shared_ptr<Q>>> s =
          ClassicalDedekindReals::DRealQlim_rec(f, n, n0);
      return [&](void) {
        if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
          auto &_rf = std::get<0>(std::move(s)->v_mut());
          std::shared_ptr<Q> x = std::move(_rf.d_a0);
          _rf.d_a0 = std::move(x);
          return std::move(s);
        } else {
          return std::visit(
              Overloaded{
                  [](const typename Sig<std::shared_ptr<Q>>::Exist _args1)
                      -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                    return Sig<std::shared_ptr<Q>>::exist(_args1.d_a0);
                  }},
              std::move(s)->v());
        }
      }();
    }
  }
}

#endif // INCLUDED_FOLD_SEQUENCE_STATE_TRACE
