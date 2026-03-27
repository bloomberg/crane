#ifndef INCLUDED_DENSITY_POTENTIAL_TRACE
#define INCLUDED_DENSITY_POTENTIAL_TRACE

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

enum class Unit { e_TT };

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

template <typename t_A, typename t_P> struct SigT {
  // TYPES
  struct ExistT {
    t_A d_a0;
    t_P d_a1;
  };

  using variant_t = std::variant<ExistT>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit SigT(ExistT _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<SigT<t_A, t_P>> existt(t_A a0, t_P a1) {
    return std::make_shared<SigT<t_A, t_P>>(
        ExistT{std::move(a0), std::move(a1)});
  }

  static std::unique_ptr<SigT<t_A, t_P>> existt_uptr(t_A a0, t_P a1) {
    return std::make_unique<SigT<t_A, t_P>>(
        ExistT{std::move(a0), std::move(a1)});
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

  template <typename T1, MapsTo<T1, T1> F0>
  static T1 iter(F0 &&f, const T1 x, const std::shared_ptr<Positive> &n) {
    return std::visit(
        Overloaded{
            [&](const typename Positive::XI _args) -> T1 {
              return f(iter<T1>(f, iter<T1>(f, x, _args.d_a0), _args.d_a0));
            },
            [&](const typename Positive::XO _args) -> T1 {
              return iter<T1>(f, iter<T1>(f, x, _args.d_a0), _args.d_a0);
            },
            [&](const typename Positive::XH _args) -> T1 { return f(x); }},
        n->v());
  }

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
  static std::shared_ptr<Positive> pow(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &_x0);
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
  __attribute__((pure)) static bool leb(const std::shared_ptr<Z> &x,
                                        const std::shared_ptr<Z> &y);
  __attribute__((pure)) static bool ltb(const std::shared_ptr<Z> &x,
                                        const std::shared_ptr<Z> &y);
  static std::shared_ptr<Z> max(std::shared_ptr<Z> n, std::shared_ptr<Z> m);
  static std::shared_ptr<Z> min(std::shared_ptr<Z> n, std::shared_ptr<Z> m);
  __attribute__((pure)) static unsigned int to_nat(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> of_nat(const unsigned int n);
  static std::shared_ptr<Positive> to_pos(const std::shared_ptr<Z> &z);
  __attribute__((pure)) static std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
  pos_div_eucl(const std::shared_ptr<Positive> &a, std::shared_ptr<Z> b);
  __attribute__((pure)) static std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>
  div_eucl(std::shared_ptr<Z> a, std::shared_ptr<Z> b);
  static std::shared_ptr<Z> div(const std::shared_ptr<Z> &a,
                                const std::shared_ptr<Z> &b);
  static std::shared_ptr<Z> sgn(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> abs(const std::shared_ptr<Z> &z);
  __attribute__((pure)) static std::pair<
      std::shared_ptr<Z>, std::pair<std::shared_ptr<Z>, std::shared_ptr<Z>>>
  ggcd(std::shared_ptr<Z> a, std::shared_ptr<Z> b);
};

struct Ranalysis1 {
  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  opp_fct(F0 &&f, const RbaseSymbolsImpl::R x);
};

template <typename a, typename b> using arrow = std::function<b(a)>;
template <typename a, typename b>
using iffT = std::pair<std::function<b(a)>, std::function<a(b)>>;
template <typename a, typename r, typename x>
using subrelation = std::function<x(a, a, r)>;
template <typename a> using Unconvertible = Unit;

struct ConstructiveEpsilon {
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<Sig<unsigned int>>
  linear_search_conform(F0 &&p_dec, const unsigned int start);
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<Sig<unsigned int>>
  linear_search_from_0_conform(F0 &&p_dec);
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<Sig<unsigned int>>
  constructive_indefinite_ground_description_nat(F0 &&p_dec);
template <typename T1, typename F0, typename F1>
__attribute__((pure)) static bool P'_decidable(F0&& g, F1&& p_decidable,
const unsigned int n);
template <typename T1, MapsTo<unsigned int, T1> F0, MapsTo<T1, unsigned int> F1,
          MapsTo<bool, T1> F2>
static std::shared_ptr<Sig<T1>>
constructive_indefinite_ground_description(F0 &&_x, F1 &&g, F2 &&p_decidable);
};

struct Ring_theory {
  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 pow_pos(F0 &&rmul, const T1 x, const std::shared_ptr<Positive> &i);
};

template <typename a, typename r> using Proper = r;
template <typename a, typename r> using ProperProxy = r;
template <typename a, typename b, typename r, typename x>
using respectful = std::function<x(a, a, r)>;

struct ConstructiveExtra {
  __attribute__((pure)) static unsigned int
  Z_inj_nat(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> Z_inj_nat_rev(const unsigned int n);
  template <MapsTo<bool, std::shared_ptr<Z>> F0>
  static std::shared_ptr<Sig<std::shared_ptr<Z>>>
  constructive_indefinite_ground_description_Z(F0 &&x);
};

struct Q {
  std::shared_ptr<Z> Qnum;
  std::shared_ptr<Positive> Qden;
};

template <typename x, typename xlt>
using isLinearOrder =
    std::pair<std::pair<std::any, std::function<xlt(x, x, x, xlt, xlt)>>,
              std::function<std::shared_ptr<Sum<xlt, xlt>>(x, x, x, xlt)>>;
template <typename I>
concept ConstructiveReals = requires(typename I::CRcarrier a0,
                                     typename I::CRcarrier a1, std::any a2,
                                     typename I::CRcarrier a3, std::any a4) {
  typename I::CRcarrier;
  {
    I::CRltLinear()
  } -> std::convertible_to<isLinearOrder<typename I::CRcarrier, std::any>>;
  { I::CRltEpsilon(a0, a1, a2) } -> std::convertible_to<std::any>;
  {
    I::CRltDisjunctEpsilon(a0, a1, a2, a3, a4)
  } -> std::convertible_to<std::shared_ptr<Sum<std::any, std::any>>>;
  { I::CR_of_Q(a0) } -> std::convertible_to<typename I::CRcarrier>;
  { I::CR_of_Q_lt(a0, a1, a2) } -> std::convertible_to<std::any>;
  { I::CRplus(a0, a1) } -> std::convertible_to<typename I::CRcarrier>;
  { I::CRopp(a0) } -> std::convertible_to<typename I::CRcarrier>;
  { I::CRmult(a0, a1) } -> std::convertible_to<typename I::CRcarrier>;
  { I::CRzero_lt_one() } -> std::convertible_to<std::any>;
  { I::CRplus_lt_compat_l(a0, a1, a2, a3) } -> std::convertible_to<std::any>;
  { I::CRplus_lt_reg_l(a0, a1, a2, a3) } -> std::convertible_to<std::any>;
  { I::CRmult_lt_0_compat(a0, a1, a2, a3) } -> std::convertible_to<std::any>;
  { I::CRinv(a0, a1) } -> std::convertible_to<typename I::CRcarrier>;
  { I::CRinv_0_lt_compat(a0, a1, a2) } -> std::convertible_to<std::any>;
  {
    I::CR_Q_dense(a0, a1, a2)
  } -> std::convertible_to<
      std::shared_ptr<SigT<std::shared_ptr<Q>, std::pair<std::any, std::any>>>>;
  {
    I::CR_archimedean(a0)
  } -> std::convertible_to<
      std::shared_ptr<SigT<std::shared_ptr<Positive>, std::any>>>;
  { I::CRabs(a0) } -> std::convertible_to<typename I::CRcarrier>;
  {
    I::CR_complete(a0, a1)
  } -> std::convertible_to<std::shared_ptr<SigT<
      typename I::CRcarrier, std::function<std::shared_ptr<Sig<unsigned int>>(
                                 std::shared_ptr<Positive>)>>>>;
};
using CRcarrier = std::any;

struct QExtra {
  static std::shared_ptr<Positive>
  Pos_log2floor_plus1(const std::shared_ptr<Positive> &p);
};

using sig_forall_dec_T =
    std::function<std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>(
        std::function<bool(unsigned int)>)>;
using sig_not_dec_T = bool;

struct DedekindDecCut {
  std::shared_ptr<Q> DDlow;
  std::shared_ptr<Q> DDhigh;
  std::function<bool(std::shared_ptr<Q>)> DDdec;
};

struct CReal {
  std::function<std::shared_ptr<Q>(std::shared_ptr<Z>)> seq;
  std::shared_ptr<Z> scale;
};

using CRealLt = std::shared_ptr<Sig<std::shared_ptr<Z>>>;
using CReal_appart = std::shared_ptr<Sum<CRealLt, CRealLt>>;

struct ConstructiveCauchyAbs {
  static std::shared_ptr<Q> CReal_abs_seq(const std::shared_ptr<CReal> &x,
                                          const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> CReal_abs_scale(const std::shared_ptr<CReal> &x);
  static std::shared_ptr<CReal> CReal_abs(std::shared_ptr<CReal> x);
};

using DReal = std::shared_ptr<Sig<std::function<bool(std::shared_ptr<Q>)>>>;

struct ConstructiveCauchyRealsMult {
  static std::shared_ptr<Q> CReal_mult_seq(const std::shared_ptr<CReal> &x,
                                           const std::shared_ptr<CReal> &y,
                                           const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z> CReal_mult_scale(const std::shared_ptr<CReal> &x,
                                             const std::shared_ptr<CReal> &y);
  static std::shared_ptr<CReal> CReal_mult(std::shared_ptr<CReal> x,
                                           std::shared_ptr<CReal> y);
  __attribute__((pure)) static CRealLt
  CReal_mult_lt_0_compat(const std::shared_ptr<CReal> &_x,
                         const std::shared_ptr<CReal> &_x0,
                         std::shared_ptr<Sig<std::shared_ptr<Z>>> hx,
                         std::shared_ptr<Sig<std::shared_ptr<Z>>> hy);
  static std::shared_ptr<SigT<std::shared_ptr<Z>, std::pair<CRealLt, CRealLt>>>
  CRealArchimedean(const std::shared_ptr<CReal> &x);
  static std::shared_ptr<Z>
  CRealLowerBound(const std::shared_ptr<CReal> &_x,
                  const std::shared_ptr<Sig<std::shared_ptr<Z>>> &xPos);
  static std::shared_ptr<Z>
  CReal_inv_pos_cm(const std::shared_ptr<CReal> &x,
                   const std::shared_ptr<Sig<std::shared_ptr<Z>>> &xPos,
                   const std::shared_ptr<Z> &n);
  static std::shared_ptr<Q>
  CReal_inv_pos_seq(const std::shared_ptr<CReal> &x,
                    const std::shared_ptr<Sig<std::shared_ptr<Z>>> &xPos,
                    const std::shared_ptr<Z> &n);
  static std::shared_ptr<Z>
  CReal_inv_pos_scale(const std::shared_ptr<CReal> &x,
                      const std::shared_ptr<Sig<std::shared_ptr<Z>>> &xPos);
  static std::shared_ptr<CReal>
  CReal_inv_pos(std::shared_ptr<CReal> x,
                std::shared_ptr<Sig<std::shared_ptr<Z>>> hxpos);
  __attribute__((pure)) static CRealLt
  CReal_neg_lt_pos(const std::shared_ptr<CReal> &_x,
                   const std::shared_ptr<Sig<std::shared_ptr<Z>>> &h);
  static std::shared_ptr<CReal>
  CReal_inv(const std::shared_ptr<CReal> &x,
            const std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                      std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
                &xnz);
  __attribute__((pure)) static CRealLt CReal_inv_0_lt_compat(
      std::shared_ptr<CReal> r,
      const std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
          &hrnz,
      const std::shared_ptr<Sig<std::shared_ptr<Z>>> &_x);
  static std::shared_ptr<SigT<std::shared_ptr<Q>, std::pair<CRealLt, CRealLt>>>
  CRealQ_dense(std::shared_ptr<CReal> a, std::shared_ptr<CReal> b,
               const std::shared_ptr<Sig<std::shared_ptr<Z>>> &h);
};

using seq_cv = std::function<std::shared_ptr<Sig<unsigned int>>(
    std::shared_ptr<Positive>)>;
using Un_cauchy_mod = std::function<std::shared_ptr<Sig<unsigned int>>(
    std::shared_ptr<Positive>)>;
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
__attribute__((pure)) bool Req_appart_dec(const RbaseSymbolsImpl::R x,
                                          const RbaseSymbolsImpl::R y);
__attribute__((pure)) CReal_appart Rrepr_appart_0(const RbaseSymbolsImpl::R x);
template <typename M>
concept RinvSig = requires {
  {
    M::Rinv(std::declval<typename M::RbaseSymbolsImpl::R>())
  } -> std::same_as<typename M::RbaseSymbolsImpl::R>;
};

struct RinvImpl {
  __attribute__((pure)) static RbaseSymbolsImpl::R
  Rinv(const RbaseSymbolsImpl::R x);
  static inline const std::any Rinv_def =
      ([]() -> const std::any { throw std::logic_error("unreachable"); })();
};

static_assert(RinvSig<RinvImpl>);
__attribute__((pure)) RbaseSymbolsImpl::R Rdiv(const RbaseSymbolsImpl::R r1,
                                               const RbaseSymbolsImpl::R r2);

struct Raxioms {
  __attribute__((pure)) static RbaseSymbolsImpl::R INR(const unsigned int n);
  static inline const std::shared_ptr<Sig<RbaseSymbolsImpl::R>> completeness =
      [](void) {
        std::shared_ptr<Sig<std::any>> s =
            ConstructiveLUB::template CR_sig_lub<CRealConstructive>(
                [](auto &&d_a0) -> decltype(auto) {
                  return sig_forall_dec(std::forward<decltype(d_a0)>(d_a0));
                },
                []() -> decltype(auto) { return sig_not_dec(); });
        return std::visit(
            Overloaded{[](const typename Sig<std::any>::Exist _args)
                           -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
              return Sig<RbaseSymbolsImpl::R>::exist(
                  RbaseSymbolsImpl::Rabst(_args.d_a0));
            }},
            std::move(s)->v());
      }();
};

struct nonnegreal {
  RbaseSymbolsImpl::R nonneg;
};

struct Rpow_def {
  __attribute__((pure)) static RbaseSymbolsImpl::R
  pow0(const RbaseSymbolsImpl::R r, const unsigned int n);
};

struct SeqProp {
  template <MapsTo<RbaseSymbolsImpl::R, unsigned int> F0>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  opp_seq(F0 &&un, const unsigned int n);
  template <MapsTo<RbaseSymbolsImpl::R, unsigned int> F0>
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>> growing_cv(F0 &&_x);
  template <MapsTo<RbaseSymbolsImpl::R, unsigned int> F0>
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>> decreasing_cv(F0 &&un);
};

struct Rbasic_fun {
  __attribute__((pure)) static bool Rcase_abs(const RbaseSymbolsImpl::R r);
};

struct Rsqrt_def {
  template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  Dichotomy_lb(const RbaseSymbolsImpl::R x, const RbaseSymbolsImpl::R y, F2 &&p,
               const unsigned int n);
  template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  Dichotomy_ub(const RbaseSymbolsImpl::R x, const RbaseSymbolsImpl::R y, F2 &&p,
               const unsigned int n);
  template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  dicho_lb(const RbaseSymbolsImpl::R _x0, const RbaseSymbolsImpl::R _x1,
           F2 &&_x2, const unsigned int _x3);
  template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  dicho_up(const RbaseSymbolsImpl::R _x0, const RbaseSymbolsImpl::R _x1,
           F2 &&_x2, const unsigned int _x3);
  template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
  dicho_lb_cv(const RbaseSymbolsImpl::R x, const RbaseSymbolsImpl::R y, F2 &&p);
  template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
  dicho_up_cv(const RbaseSymbolsImpl::R x, const RbaseSymbolsImpl::R y, F2 &&p);
  __attribute__((pure)) static bool
  cond_positivity(const RbaseSymbolsImpl::R x);
  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
  IVT(F0 &&f, const RbaseSymbolsImpl::R x, const RbaseSymbolsImpl::R y);
  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
  IVT_cor(F0 &&f, const RbaseSymbolsImpl::R x, const RbaseSymbolsImpl::R y);
  static std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
  Rsqrt_exists(const RbaseSymbolsImpl::R y);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  Rsqrt(const std::shared_ptr<nonnegreal> &y);
};

struct R_sqrt {
  __attribute__((pure)) static RbaseSymbolsImpl::R
  sqrt(const RbaseSymbolsImpl::R x);
};

struct ConstructiveRcomplete {
  static std::shared_ptr<Positive>
  CReal_from_cauchy_cm(const std::shared_ptr<Z> &n);
  template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
  static std::shared_ptr<Q> CReal_from_cauchy_seq(F0 &&xn,
                                                  const Un_cauchy_mod xcau,
                                                  const std::shared_ptr<Z> &n);
  static std::shared_ptr<SigT<std::shared_ptr<Positive>, CRealLt>>
  Rup_pos(std::shared_ptr<CReal> x);
  template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
  static std::shared_ptr<Z> CReal_from_cauchy_scale(F0 &&xn,
                                                    const Un_cauchy_mod xcau);
  template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
  static std::shared_ptr<CReal> CReal_from_cauchy(F0 &&xn,
                                                  const Un_cauchy_mod xcau);
  template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
  static std::shared_ptr<SigT<std::shared_ptr<CReal>, seq_cv>>
  Rcauchy_complete(F0 &&xn, const Un_cauchy_mod cau);
  static inline const isLinearOrder<std::shared_ptr<CReal>, CRealLt>
      CRealLtIsLinear = []() {
        return std::make_pair(
            std::make_pair(std::any{}, this->CReal_lt_trans()),
            [](std::shared_ptr<CReal> x, std::shared_ptr<CReal> y,
               std::shared_ptr<CReal> z,
               std::shared_ptr<Sig<std::shared_ptr<Z>>> x0) {
              std::shared_ptr<Sum<std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                  std::shared_ptr<Sig<std::shared_ptr<Z>>>>>
                  s = x->CRealLt_dec(z, y, x0);
              return [&](void) {
                if (std::move(s).use_count() == 1 &&
                    std::move(s)->v().index() == 0) {
                  auto &_rf = std::get<0>(std::move(s)->v_mut());
                  std::shared_ptr<Sig<std::shared_ptr<Z>>> c =
                      std::move(_rf.d_a0);
                  _rf.d_a0 = std::move(c);
                  return std::move(s);
                } else {
                  return std::visit(
                      Overloaded{
                          [](const typename Sum<
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inl
                                 _args)
                              -> std::shared_ptr<Sum<
                                  std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                  std::shared_ptr<Sig<std::shared_ptr<Z>>>>> {
                            return Sum<
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                                inl(_args.d_a0);
                          },
                          [](const typename Sum<
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                              std::shared_ptr<Sig<std::shared_ptr<Z>>>>::Inr
                                 _args)
                              -> std::shared_ptr<Sum<
                                  std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                  std::shared_ptr<Sig<std::shared_ptr<Z>>>>> {
                            return Sum<
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>,
                                std::shared_ptr<Sig<std::shared_ptr<Z>>>>::
                                inr(_args.d_a0);
                          }},
                      std::move(s)->v());
                }
              }();
            });
      }();
  template <
      MapsTo<std::shared_ptr<CReal>, unsigned int> F0,
      MapsTo<std::shared_ptr<Sig<unsigned int>>, std::shared_ptr<Positive>> F1>
  static std::shared_ptr<SigT<std::shared_ptr<CReal>,
                              std::function<std::shared_ptr<Sig<unsigned int>>(
                                  std::shared_ptr<Positive>)>>>
  CRealComplete(F0 &&xn, F1 &&x);
  static std::shared_ptr<Sum<CRealLt, CRealLt>>
  CRealLtDisjunctEpsilon(std::shared_ptr<CReal> a, std::shared_ptr<CReal> b,
                         std::shared_ptr<CReal> c, std::shared_ptr<CReal> d);
};

struct ConstructiveLUB {
  template <ConstructiveReals _tcI0>
  __attribute__((pure)) static bool
  is_upper_bound_dec(const typename _tcI0::CRcarrier _x,
                     const sig_forall_dec_T _x0,
                     const sig_not_dec_T sig_not_dec0);
  template <ConstructiveReals _tcI0>
  static std::shared_ptr<Sig<unsigned int>>
  is_upper_bound_epsilon(const sig_forall_dec_T lpo,
                         const sig_not_dec_T sig_not_dec0);
  template <ConstructiveReals _tcI0>
  static std::shared_ptr<Sig<unsigned int>>
  is_upper_bound_not_epsilon(const sig_forall_dec_T lpo,
                             const sig_not_dec_T sig_not_dec0);
  template <ConstructiveReals _tcI0>
  static std::shared_ptr<Sig<typename _tcI0::CRcarrier>>
  is_upper_bound_glb(const sig_not_dec_T sig_not_dec0,
                     const sig_forall_dec_T lpo);
  template <ConstructiveReals _tcI0>
  static std::shared_ptr<Sig<typename _tcI0::CRcarrier>>
  sig_lub(const sig_forall_dec_T sig_forall_dec0,
          const sig_not_dec_T sig_not_dec0);
  template <ConstructiveReals _tcI0>
  static std::shared_ptr<Sig<typename _tcI0::CRcarrier>>
  CR_sig_lub(const sig_forall_dec_T _x1, const sig_not_dec_T _x2);
};

struct RIneq {
  __attribute__((pure)) static bool Rlt_dec(const RbaseSymbolsImpl::R r1,
                                            const RbaseSymbolsImpl::R r2);
  __attribute__((pure)) static bool Rle_dec(const RbaseSymbolsImpl::R r1,
                                            const RbaseSymbolsImpl::R r2);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  Rsqr(const RbaseSymbolsImpl::R r);
};

struct ClassicalDedekindReals {
  template <MapsTo<bool, unsigned int> F0>
  static std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>
  sig_forall_dec(F0 &&_x0);
  static bool sig_not_dec();
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
  static std::shared_ptr<CReal> inject_Q(std::shared_ptr<Q> q);
  static inline const CRealLt CRealLt_0_1 =
      Sig<std::shared_ptr<Z>>::exist(Z::zneg(Positive::xo(Positive::xh())));
  __attribute__((pure)) static CRealLt inject_Q_lt(const std::shared_ptr<Q> &q,
                                                   const std::shared_ptr<Q> &r);
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
};

struct CMorphisms {
  template <typename T1, typename T2, typename T3, typename T4, typename T5,
            typename T6>
  __attribute__((pure)) static subrelation<std::function<T4(T1)>,
                                           respectful<T1, T4, T3, T5>,
                                           respectful<T1, T4, T2, T6>>
  subrelation_respectful(const subrelation<T1, T2, T3> subl,
                         const subrelation<T4, T5, T6> subr);
  template <typename T1, typename T2, typename T3>
  __attribute__((pure)) static Proper<T1, T3>
  subrelation_proper(const T1 m, const T2 mor, const Unit _x,
                     const subrelation<T1, T2, T3> sub0);
  __attribute__((pure)) static arrow<std::any, std::any>
  iffT_arrow_subrelation(const std::pair<std::function<std::any(std::any)>,
                                         std::function<std::any(std::any)>>
                             x);
  __attribute__((pure)) static arrow<std::any, std::any>
  iffT_flip_arrow_subrelation(const std::pair<std::function<std::any(std::any)>,
                                              std::function<std::any(std::any)>>
                                  x);
  template <typename T1, typename T2, typename T3, typename T4,
            MapsTo<T2, T1> F0>
  __attribute__((pure)) static Proper<T2, T4> Reflexive_partial_app_morphism(
      F0 &&_x,
      const Proper<std::function<T2(T1)>, respectful<T1, T2, T3, T4>> h,
      const T1 x, const T3 h0);
};

struct DensityPotentialTraceCase {
  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0,
            MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F1>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  lapse(F0 &&f, F1 &&mu, const RbaseSymbolsImpl::R x) {
    return f(mu(x));
  }

  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0,
            MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F1>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  proper_time_static(F0 &&f, F1 &&mu, const RbaseSymbolsImpl::R x,
                     const RbaseSymbolsImpl::R t) {
    return RbaseSymbolsImpl::Rmult(lapse(f, mu, x), t);
  }

  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0,
            MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F1,
            MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F2,
            MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F3>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  proper_time_density_path(F0 &&f, F1 &&mu, F2 &&gamma, F3 &&v,
                           const RbaseSymbolsImpl::R t) {
    return R_sqrt::sqrt(Rminus(Rpow_def::pow0(lapse(f, mu, gamma(t)), 2u),
                               Rpow_def::pow0(v(t), 2u)));
  }

  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  V_eff(F0 &&n, const RbaseSymbolsImpl::R x) {
    return RinvImpl::Rinv(RbaseSymbolsImpl::Rmult(n(x), n(x)));
  }

  template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
  __attribute__((pure)) static RbaseSymbolsImpl::R
  V_eff_massive(F0 &&n, const RbaseSymbolsImpl::R m,
                const RbaseSymbolsImpl::R x) {
    return RbaseSymbolsImpl::Rmult(Rpow_def::pow0(m, 2u), V_eff(n, x));
  }

  __attribute__((pure)) static RbaseSymbolsImpl::R
  sample_activation(const RbaseSymbolsImpl::R z);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  sample_mu(const RbaseSymbolsImpl::R x);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  sample_gamma(const RbaseSymbolsImpl::R t);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  sample_v(const RbaseSymbolsImpl::R _x);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  sample_N(const RbaseSymbolsImpl::R x);
  static inline const RbaseSymbolsImpl::R sample_mass =
      IZR(Z::zpos(Positive::xi(Positive::xh())));
  static inline const RbaseSymbolsImpl::R sample_time =
      IZR(Z::zpos(Positive::xo(Positive::xh())));
  __attribute__((pure)) static RbaseSymbolsImpl::R
  density_radicand_at(const unsigned int n);
  __attribute__((pure)) static bool
  static_time_nonnegative_at(const unsigned int n);
  __attribute__((pure)) static bool
  density_radicand_nonnegative_at(const unsigned int n);
  __attribute__((pure)) static RbaseSymbolsImpl::R
  density_value_at(const unsigned int n);
  __attribute__((pure)) static bool
  density_value_nonnegative_at(const unsigned int n);
  __attribute__((pure)) static bool
  massive_potential_nonnegative_at(const unsigned int n);
  static inline const bool sample_static_nonneg =
      static_time_nonnegative_at(1u);
  static inline const bool sample_density_radicand_nonneg =
      density_radicand_nonnegative_at(1u);
  static inline const bool sample_density_value_nonneg =
      density_value_nonnegative_at(1u);
  static inline const bool sample_massive_nonneg =
      massive_potential_nonnegative_at(2u);
};

template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
__attribute__((pure)) RbaseSymbolsImpl::R
Ranalysis1::opp_fct(F0 &&f, const RbaseSymbolsImpl::R x) {
  return RbaseSymbolsImpl::Ropp(f(x));
}

template <MapsTo<bool, unsigned int> F0>
std::shared_ptr<Sig<unsigned int>>
ConstructiveEpsilon::linear_search_conform(F0 &&p_dec,
                                           const unsigned int start) {
  if (p_dec(start)) {
    return Sig<unsigned int>::exist(std::move(start));
  } else {
    return std::visit(
        Overloaded{[](const typename Sig<unsigned int>::Exist _args)
                       -> std::shared_ptr<Sig<unsigned int>> {
          return Sig<unsigned int>::exist(_args.d_a0);
        }},
        ConstructiveEpsilon::linear_search_conform(p_dec,
                                                   (std::move(start) + 1))
            ->v());
  }
}

template <MapsTo<bool, unsigned int> F0>
std::shared_ptr<Sig<unsigned int>>
ConstructiveEpsilon::linear_search_from_0_conform(F0 &&p_dec) {
  return ConstructiveEpsilon::linear_search_conform(p_dec, 0u);
}

template <MapsTo<bool, unsigned int> F0>
std::shared_ptr<Sig<unsigned int>>
ConstructiveEpsilon::constructive_indefinite_ground_description_nat(
    F0 &&p_dec) {
  std::shared_ptr<Sig<unsigned int>> s =
      ConstructiveEpsilon::linear_search_from_0_conform(p_dec);
  return [&](void) {
    if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
      auto &_rf = std::get<0>(std::move(s)->v_mut());
      unsigned int x = std::move(_rf.d_a0);
      _rf.d_a0 = std::move(x);
      return std::move(s);
    } else {
      return std::visit(
          Overloaded{[](const typename Sig<unsigned int>::Exist _args)
                         -> std::shared_ptr<Sig<unsigned int>> {
            return Sig<unsigned int>::exist(_args.d_a0);
          }},
          std::move(s)->v());
    }
  }();
}

     template <typename T1, typename F0, typename
F1>
__attribute__((pure)) bool ConstructiveEpsilon::P'_decidable(F0&& g,
F1&& p_decidable,
const unsigned int n){
       bool s = p_decidable(g(n));
       if (std::move(s)) {
         return p_decidable(g(n));
       } else {
         return p_decidable(g(n));
       }
     }

     template <typename T1, MapsTo<unsigned int, T1> F0,
               MapsTo<T1, unsigned int> F1, MapsTo<bool, T1> F2>
     std::shared_ptr<Sig<T1>>
     ConstructiveEpsilon::constructive_indefinite_ground_description(
         F0 &&_x, F1 &&g, F2 &&p_decidable) {
       std::shared_ptr<Sig<unsigned int>> h1 =
           ConstructiveEpsilon::constructive_indefinite_ground_description_nat(
               [&](unsigned int _x0) -> bool {
return ConstructiveEpsilon::P'_decidable(g, p_decidable,
_x0);
               });
       return std::visit(
           Overloaded{[&](const typename Sig<unsigned int>::Exist _args)
                          -> std::shared_ptr<Sig<T1>> {
             return Sig<T1>::exist(g(_args.d_a0));
           }},
           std::move(h1)->v());
     }

     template <typename T1, MapsTo<T1, T1, T1> F0>
     T1 Ring_theory::pow_pos(F0 &&rmul, const T1 x,
                             const std::shared_ptr<Positive> &i) {
       return std::visit(
           Overloaded{
               [&](const typename Positive::XI _args) -> T1 {
                 T1 p = Ring_theory::template pow_pos<T1>(rmul, x, _args.d_a0);
                 return rmul(x, rmul(p, p));
               },
               [&](const typename Positive::XO _args) -> T1 {
                 T1 p = Ring_theory::template pow_pos<T1>(rmul, x, _args.d_a0);
                 return rmul(p, p);
               },
               [&](const typename Positive::XH _args) -> T1 { return x; }},
           i->v());
     }

     template <typename T1, typename T2, typename T3, typename T4, typename T5,
               typename T6>
     __attribute__((pure))
     subrelation<std::function<T4(T1)>, CMorphisms::respectful<T1, T4, T3, T5>,
                 CMorphisms::respectful<T1, T4, T2, T6>>
     CMorphisms::subrelation_respectful(const subrelation<T1, T2, T3> subl,
                                        const subrelation<T4, T5, T6> subr) {
       return
           [=](std::function<T4(T1)> x, std::function<T4(T1)> y,
               std::function<T5(T1, T1, T3)> x0, T1 x1, T1 y0, T2 x2) mutable {
             return subr(x(x1), y(y0), x0(x1, y0, subl(x1, y0, x2)));
           };
     }

     template <typename T1, typename T2, typename T3>
     __attribute__((pure)) CMorphisms::Proper<T1, T3>
     CMorphisms::subrelation_proper(const T1 m, const T2 mor, const Unit _x,
                                    const subrelation<T1, T2, T3> sub0) {
       return sub0(m, m, mor);
     }

     template <typename T1, typename T2, typename T3, typename T4,
               MapsTo<T2, T1> F0>
     __attribute__((pure)) CMorphisms::Proper<T2, T4>
     CMorphisms::Reflexive_partial_app_morphism(
         F0 &&_x,
         const CMorphisms::Proper<std::function<T2(T1)>,
                                  CMorphisms::respectful<T1, T2, T3, T4>>
             h,
         const T1 x, const T3 h0) {
       return h(x, x, h0);
     }

     template <MapsTo<bool, std::shared_ptr<Z>> F0>
     std::shared_ptr<Sig<std::shared_ptr<Z>>>
     ConstructiveExtra::constructive_indefinite_ground_description_Z(F0 &&x) {
       return ConstructiveEpsilon::constructive_indefinite_ground_description(
           ConstructiveExtra::Z_inj_nat, ConstructiveExtra::Z_inj_nat_rev, x);
     }

     template <ConstructiveReals _tcI0>
     __attribute__((pure)) bool ConstructiveLUB::is_upper_bound_dec(
         const typename _tcI0::CRcarrier _x,
         const ConstructiveLUB::sig_forall_dec_T _x0,
         const ConstructiveLUB::sig_not_dec_T sig_not_dec0) {
       bool s = sig_not_dec0();
       if (std::move(s)) {
         return true;
       } else {
         return false;
       }
     }

     template <ConstructiveReals _tcI0>
     std::shared_ptr<Sig<unsigned int>> ConstructiveLUB::is_upper_bound_epsilon(
         const ConstructiveLUB::sig_forall_dec_T lpo,
         const ConstructiveLUB::sig_not_dec_T sig_not_dec0) {
       return ConstructiveEpsilon::
           constructive_indefinite_ground_description_nat(
               [=](unsigned int n) mutable {
                 return ConstructiveLUB::template is_upper_bound_dec<_tcI0>(
                     _tcI0::CR_of_Q(std::make_shared<Q>(
                         Q{BinInt::of_nat(n), Positive::xh()})),
                     lpo, sig_not_dec0);
               });
     }

     template <ConstructiveReals _tcI0>
     std::shared_ptr<Sig<unsigned int>>
     ConstructiveLUB::is_upper_bound_not_epsilon(
         const ConstructiveLUB::sig_forall_dec_T lpo,
         const ConstructiveLUB::sig_not_dec_T sig_not_dec0) {
       return ConstructiveEpsilon::
           constructive_indefinite_ground_description_nat(
               [=](unsigned int n) mutable {
                 bool s = ConstructiveLUB::template is_upper_bound_dec<_tcI0>(
                     _tcI0::CRopp(_tcI0::CR_of_Q(std::make_shared<Q>(
                         Q{BinInt::of_nat(n), Positive::xh()}))),
                     lpo, sig_not_dec0);
                 if (std::move(s)) {
                   return false;
                 } else {
                   return true;
                 }
               });
     }

     template <ConstructiveReals _tcI0>
     std::shared_ptr<Sig<typename _tcI0::CRcarrier>>
     ConstructiveLUB::is_upper_bound_glb(
         const ConstructiveLUB::sig_not_dec_T sig_not_dec0,
         const ConstructiveLUB::sig_forall_dec_T lpo) {
       std::shared_ptr<Sig<unsigned int>> s =
           ConstructiveLUB::template is_upper_bound_epsilon<_tcI0>(
               lpo, sig_not_dec0);
       return std::visit(
           Overloaded{[&](const typename Sig<unsigned int>::Exist _args)
                          -> std::shared_ptr<Sig<typename _tcI0::CRcarrier>> {
             std::shared_ptr<Sig<unsigned int>> s0 =
                 ConstructiveLUB::template is_upper_bound_not_epsilon<_tcI0>(
                     lpo, sig_not_dec0);
             return std::visit(
                 Overloaded{[&](const typename Sig<unsigned int>::Exist _args0)
                                -> std::shared_ptr<
                                    Sig<typename _tcI0::CRcarrier>> {
                   std::function<bool(std::shared_ptr<Q>)> h =
                       [=](std::shared_ptr<Q> q) mutable {
                         return ConstructiveLUB::template is_upper_bound_dec<
                             _tcI0>(_tcI0::CR_of_Q(q), lpo, sig_not_dec0);
                       };
                   std::shared_ptr<Sig<typename _tcI0::CRcarrier>> s1 =
                       [](const auto &_x) { return _x->glb_dec_Q(); }();
                   return [&](void) {
                     if (std::move(s1).use_count() == 1 &&
                         std::move(s1)->v().index() == 0) {
                       auto &_rf = std::get<0>(std::move(s1)->v_mut());
                       typename _tcI0::CRcarrier x1 = std::move(_rf.d_a0);
                       _rf.d_a0 = std::move(x1);
                       return std::move(s1);
                     } else {
                       return std::visit(
                           Overloaded{
                               [](const typename Sig<
                                   typename _tcI0::CRcarrier>::Exist _args1)
                                   -> std::shared_ptr<
                                       Sig<typename _tcI0::CRcarrier>> {
                                 return Sig<typename _tcI0::CRcarrier>::exist(
                                     _args1.d_a0);
                               }},
                           std::move(s1)->v());
                     }
                   }();
                 }},
                 std::move(s0)->v());
           }},
           std::move(s)->v());
     }

     template <ConstructiveReals _tcI0>
     std::shared_ptr<Sig<typename _tcI0::CRcarrier>> ConstructiveLUB::sig_lub(
         const ConstructiveLUB::sig_forall_dec_T sig_forall_dec0,
         const ConstructiveLUB::sig_not_dec_T sig_not_dec0) {
       std::shared_ptr<Sig<typename _tcI0::CRcarrier>> s =
           ConstructiveLUB::template is_upper_bound_glb<_tcI0>(sig_not_dec0,
                                                               sig_forall_dec0);
       return [&](void) {
         if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
           auto &_rf = std::get<0>(std::move(s)->v_mut());
           typename _tcI0::CRcarrier x = std::move(_rf.d_a0);
           _rf.d_a0 = std::move(x);
           return std::move(s);
         } else {
           return std::visit(
               Overloaded{
                   [](const typename Sig<typename _tcI0::CRcarrier>::Exist
                          _args)
                       -> std::shared_ptr<Sig<typename _tcI0::CRcarrier>> {
                     return Sig<typename _tcI0::CRcarrier>::exist(_args.d_a0);
                   }},
               std::move(s)->v());
         }
       }();
     }

     template <ConstructiveReals _tcI0>
     std::shared_ptr<Sig<typename _tcI0::CRcarrier>>
     ConstructiveLUB::CR_sig_lub(const ConstructiveLUB::sig_forall_dec_T _x1,
                                 const ConstructiveLUB::sig_not_dec_T _x2) {
       return ConstructiveLUB::template sig_lub<_tcI0>(_x1, _x2);
     }

     template <MapsTo<bool, unsigned int> F0>
     std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>>
     ClassicalDedekindReals::sig_forall_dec(F0 &&_x0) {
       throw std::logic_error(
           "unrealized axiom: "
           "Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec");
     }

     template <MapsTo<bool, std::shared_ptr<Q>> F0>
     std::shared_ptr<Sig<std::shared_ptr<Q>>>
     ClassicalDedekindReals::lowerCutBelow(F0 &&f) {
       std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>> s =
           ClassicalDedekindReals::sig_forall_dec([=](unsigned int n) mutable {
             bool b =
                 f(std::make_shared<Q>(Q{BinInt::of_nat(n), Positive::xh()})
                       ->Qopp());
             if (b) {
               return false;
             } else {
               return true;
             }
           });
       return std::visit(
           Overloaded{
               [](const typename Sumor<
                   std::shared_ptr<Sig<unsigned int>>>::Inleft _args)
                   -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                 return std::visit(
                     Overloaded{
                         [](const typename Sig<unsigned int>::Exist _args0)
                             -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                           return Sig<std::shared_ptr<Q>>::exist(
                               std::make_shared<Q>(
                                   Q{BinInt::of_nat(_args0.d_a0),
                                     Positive::xh()})
                                   ->Qopp());
                         }},
                     _args.d_a0->v());
               },
               [](const typename Sumor<
                   std::shared_ptr<Sig<unsigned int>>>::Inright _args)
                   -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                 throw std::logic_error("absurd case");
               }},
           std::move(s)->v());
     }

     template <MapsTo<bool, std::shared_ptr<Q>> F0>
     std::shared_ptr<Sig<std::shared_ptr<Q>>>
     ClassicalDedekindReals::lowerCutAbove(F0 &&f) {
       std::shared_ptr<Sumor<std::shared_ptr<Sig<unsigned int>>>> s =
           ClassicalDedekindReals::sig_forall_dec([=](unsigned int n) mutable {
             bool b =
                 f(std::make_shared<Q>(Q{BinInt::of_nat(n), Positive::xh()}));
             if (b) {
               return true;
             } else {
               return false;
             }
           });
       return std::visit(
           Overloaded{
               [](const typename Sumor<
                   std::shared_ptr<Sig<unsigned int>>>::Inleft _args)
                   -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                 return std::visit(
                     Overloaded{
                         [](const typename Sig<unsigned int>::Exist _args0)
                             -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
                           return Sig<std::shared_ptr<Q>>::exist(
                               std::make_shared<Q>(
                                   Q{BinInt::of_nat(_args0.d_a0),
                                     Positive::xh()}));
                         }},
                     _args.d_a0->v());
               },
               [](const typename Sumor<
                   std::shared_ptr<Sig<unsigned int>>>::Inright _args)
                   -> std::shared_ptr<Sig<std::shared_ptr<Q>>> {
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
         bool b =
             f(std::visit(
                   Overloaded{[](const typename Sig<std::shared_ptr<Q>>::Exist
                                     _args) -> auto { return _args.d_a0; }},
                   ClassicalDedekindReals::lowerCutBelow(f)->v())
                   ->Qplus(std::make_shared<Q>(
                       Q{BinInt::of_nat(n0), Coq_Pos::of_nat((n + 1))})));
         if (std::move(b)) {
           return Sig<std::shared_ptr<Q>>::exist(
               std::visit(
                   Overloaded{[](const typename Sig<std::shared_ptr<Q>>::Exist
                                     _args0) -> auto { return _args0.d_a0; }},
                   ClassicalDedekindReals::lowerCutBelow(f)->v())
                   ->Qplus(std::make_shared<Q>(
                       Q{BinInt::of_nat(n0), Coq_Pos::of_nat((n + 1))})));
         } else {
           std::shared_ptr<Sig<std::shared_ptr<Q>>> s =
               ClassicalDedekindReals::DRealQlim_rec(f, n, n0);
           return [&](void) {
             if (std::move(s).use_count() == 1 &&
                 std::move(s)->v().index() == 0) {
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

     template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
     std::shared_ptr<Q> ConstructiveRcomplete::CReal_from_cauchy_seq(
         F0 &&xn, const ConstructiveRcomplete::Un_cauchy_mod xcau,
         const std::shared_ptr<Z> &n) {
       std::shared_ptr<Positive> p =
           ConstructiveRcomplete::CReal_from_cauchy_cm(n);
       return std::visit(
           Overloaded{[&](const typename Sig<unsigned int>::Exist _args)
                          -> std::shared_ptr<Q> {
             return xn(_args.d_a0)
                 ->seq(BinInt::sub(Z::zneg(p),
                                   Z::zpos(Positive::xo(Positive::xh()))));
           }},
           xcau(Coq_Pos::mul(Positive::xo(Positive::xo(Positive::xh())),
                             Coq_Pos::pow(Positive::xo(Positive::xh()), p)))
               ->v());
     }

     template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
     std::shared_ptr<Z> ConstructiveRcomplete::CReal_from_cauchy_scale(
         F0 &&xn, const ConstructiveRcomplete::Un_cauchy_mod xcau) {
       return ConstructiveRcomplete::CReal_from_cauchy_seq(
                  xn, xcau, Z::zneg(Positive::xh()))
           ->Qabs()
           ->Qplus(std::make_shared<Q>(
               Q{Z::zpos(Positive::xo(Positive::xh())), Positive::xh()}))
           ->Qbound_lt_ZExp2();
     }

     template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
     std::shared_ptr<CReal> ConstructiveRcomplete::CReal_from_cauchy(
         F0 &&xn, const ConstructiveRcomplete::Un_cauchy_mod xcau) {
       return std::make_shared<CReal>(CReal{
           [&](const std::shared_ptr<Z> &_x0) -> std::shared_ptr<Q> {
             return ConstructiveRcomplete::CReal_from_cauchy_seq(xn, xcau, _x0);
           },
           ConstructiveRcomplete::CReal_from_cauchy_scale(xn, xcau)});
     }

     template <MapsTo<std::shared_ptr<CReal>, unsigned int> F0>
     std::shared_ptr<
         SigT<std::shared_ptr<CReal>, ConstructiveRcomplete::seq_cv>>
     ConstructiveRcomplete::Rcauchy_complete(
         F0 &&xn, const ConstructiveRcomplete::Un_cauchy_mod cau) {
       return SigT<std::shared_ptr<CReal>,
                   std::function<std::shared_ptr<Sig<unsigned int>>(
                       std::shared_ptr<Positive>)>>::
           existt(
               ConstructiveRcomplete::CReal_from_cauchy(xn, cau),
               [=](std::shared_ptr<Positive> p) mutable {
                 std::shared_ptr<Sig<unsigned int>> h0 =
                     cau(Coq_Pos::mul(Positive::xo(Positive::xh()), p));
                 return std::visit(
                     Overloaded{[&](const typename Sig<unsigned int>::Exist
                                        _args)
                                    -> std::shared_ptr<Sig<unsigned int>> {
                       std::shared_ptr<Positive> i_ =
                           ConstructiveRcomplete::CReal_from_cauchy_cm(
                               BinInt::sub(Z::zneg(p),
                                           Z::zpos(Positive::xh())));
                       std::shared_ptr<Sig<unsigned int>> s = cau(Coq_Pos::mul(
                           Positive::xo(Positive::xo(Positive::xh())),
                           Coq_Pos::pow(Positive::xo(Positive::xh()),
                                        std::move(i_))));
                       return [&](void) {
                         if (std::move(s).use_count() == 1 &&
                             std::move(s)->v().index() == 0) {
                           auto &_rf = std::get<0>(std::move(s)->v_mut());
                           unsigned int x0 = std::move(_rf.d_a0);
                           _rf.d_a0 = std::max(_args.d_a0, std::move(x0));
                           return std::move(s);
                         } else {
                           return std::visit(
                               Overloaded{
                                   [&](const typename Sig<unsigned int>::Exist
                                           _args0)
                                       -> std::shared_ptr<Sig<unsigned int>> {
                                     return Sig<unsigned int>::exist(
                                         std::max(_args.d_a0, _args0.d_a0));
                                   }},
                               std::move(s)->v());
                         }
                       }();
                     }},
                     std::move(h0)->v());
               });
     }

     template <
         MapsTo<std::shared_ptr<CReal>, unsigned int> F0,
         MapsTo<std::shared_ptr<Sig<unsigned int>>, std::shared_ptr<Positive>>
             F1>
     std::shared_ptr<SigT<std::shared_ptr<CReal>,
                          std::function<std::shared_ptr<Sig<unsigned int>>(
                              std::shared_ptr<Positive>)>>>
     ConstructiveRcomplete::CRealComplete(F0 &&xn, F1 &&x) {
       std::shared_ptr<SigT<std::shared_ptr<CReal>,
                            std::function<std::shared_ptr<Sig<unsigned int>>(
                                std::shared_ptr<Positive>)>>>
           s = ConstructiveRcomplete::Rcauchy_complete(
               xn, [=](std::shared_ptr<Positive> p) mutable {
                 std::shared_ptr<Sig<unsigned int>> s = x(p);
                 return [&](void) {
                   if (s.use_count() == 1 && s->v().index() == 0) {
                     auto &_rf = std::get<0>(s->v_mut());
                     unsigned int x0 = std::move(_rf.d_a0);
                     _rf.d_a0 = x0;
                     return s;
                   } else {
                     return std::visit(
                         Overloaded{
                             [](const typename Sig<unsigned int>::Exist _args)
                                 -> std::shared_ptr<Sig<unsigned int>> {
                               return Sig<unsigned int>::exist(_args.d_a0);
                             }},
                         s->v());
                   }
                 }();
               });
       return [&](void) {
         if (std::move(s).use_count() == 1 && std::move(s)->v().index() == 0) {
           auto &_rf = std::get<0>(std::move(s)->v_mut());
           std::shared_ptr<CReal> x0 = std::move(_rf.d_a0);
           std::function<std::shared_ptr<Sig<unsigned int>>(
               std::shared_ptr<Positive>)>
               s0 = std::move(_rf.d_a1);
           _rf.d_a0 = x0;
           _rf.d_a1 = [=](std::shared_ptr<Positive> p) mutable {
             std::shared_ptr<Sig<unsigned int>> s1 = s0(p);
             return [&](void) {
               if (std::move(s1).use_count() == 1 &&
                   std::move(s1)->v().index() == 0) {
                 auto &_rf = std::get<0>(std::move(s1)->v_mut());
                 unsigned int x1 = std::move(_rf.d_a0);
                 _rf.d_a0 = std::move(x1);
                 return std::move(s1);
               } else {
                 return std::visit(
                     Overloaded{
                         [](const typename Sig<unsigned int>::Exist _args)
                             -> std::shared_ptr<Sig<unsigned int>> {
                           return Sig<unsigned int>::exist(_args.d_a0);
                         }},
                     std::move(s1)->v());
               }
             }();
           };
           return std::move(s);
         } else {
           return std::visit(
               Overloaded{[](const typename SigT<
                              std::shared_ptr<CReal>,
                              std::function<std::shared_ptr<Sig<unsigned int>>(
                                  std::shared_ptr<Positive>)>>::ExistT _args)
                              -> std::shared_ptr<
                                  SigT<std::shared_ptr<CReal>,
                                       std::function<
                                           std::shared_ptr<Sig<unsigned int>>(
                                               std::shared_ptr<Positive>)>>> {
                 return SigT<std::shared_ptr<CReal>,
                             std::function<std::shared_ptr<Sig<unsigned int>>(
                                 std::shared_ptr<Positive>)>>::
                     existt(_args.d_a0, [=](std::shared_ptr<Positive>
                                                p) mutable {
                       std::shared_ptr<Sig<unsigned int>> s1 = _args.d_a1(p);
                       return [&](void) {
                         if (std::move(s1).use_count() == 1 &&
                             std::move(s1)->v().index() == 0) {
                           auto &_rf = std::get<0>(std::move(s1)->v_mut());
                           unsigned int x1 = std::move(_rf.d_a0);
                           _rf.d_a0 = std::move(x1);
                           return std::move(s1);
                         } else {
                           return std::visit(
                               Overloaded{
                                   [](const typename Sig<unsigned int>::Exist
                                          _args)
                                       -> std::shared_ptr<Sig<unsigned int>> {
                                     return Sig<unsigned int>::exist(
                                         _args.d_a0);
                                   }},
                               std::move(s1)->v());
                         }
                       }();
                     });
               }},
               std::move(s)->v());
         }
       }();
     }

     template <MapsTo<RbaseSymbolsImpl::R, unsigned int> F0>
     __attribute__((pure)) RbaseSymbolsImpl::R
     SeqProp::opp_seq(F0 &&un, const unsigned int n) {
       return RbaseSymbolsImpl::Ropp(un(n));
     }

     template <MapsTo<RbaseSymbolsImpl::R, unsigned int> F0>
     std::shared_ptr<Sig<RbaseSymbolsImpl::R>> SeqProp::growing_cv(F0 &&_x) {
       return Sig<RbaseSymbolsImpl::R>::exist(std::visit(
           Overloaded{[](const typename Sig<RbaseSymbolsImpl::R>::Exist _args)
                          -> auto { return _args.d_a0; }},
           Raxioms::completeness()->v()));
     }

     template <MapsTo<RbaseSymbolsImpl::R, unsigned int> F0>
     std::shared_ptr<Sig<RbaseSymbolsImpl::R>> SeqProp::decreasing_cv(F0 &&un) {
       std::shared_ptr<Sig<RbaseSymbolsImpl::R>> h1 =
           SeqProp::growing_cv([&](unsigned int _x0) -> RbaseSymbolsImpl::R {
             return SeqProp::opp_seq(un, _x0);
           });
       return std::visit(
           Overloaded{[](const typename Sig<RbaseSymbolsImpl::R>::Exist _args)
                          -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
             return Sig<RbaseSymbolsImpl::R>::exist(
                 RbaseSymbolsImpl::Ropp(_args.d_a0));
           }},
           std::move(h1)->v());
     }

     template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
     __attribute__((pure)) RbaseSymbolsImpl::R
     Rsqrt_def::Dichotomy_lb(const RbaseSymbolsImpl::R x,
                             const RbaseSymbolsImpl::R y, F2 &&p,
                             const unsigned int n) {
       if (n <= 0) {
         return x;
       } else {
         unsigned int n0 = n - 1;
         RbaseSymbolsImpl::R down = Rsqrt_def::Dichotomy_lb(x, y, p, n0);
         RbaseSymbolsImpl::R up = Rsqrt_def::Dichotomy_ub(x, y, p, n0);
         RbaseSymbolsImpl::R z =
             ::Rdiv(RbaseSymbolsImpl::Rplus(down, up),
                    ::IZR(Z::zpos(Positive::xo(Positive::xh()))));
         if (p(z)) {
           return down;
         } else {
           return z;
         }
       }
     }

     template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
     __attribute__((pure)) RbaseSymbolsImpl::R
     Rsqrt_def::Dichotomy_ub(const RbaseSymbolsImpl::R x,
                             const RbaseSymbolsImpl::R y, F2 &&p,
                             const unsigned int n) {
       if (n <= 0) {
         return y;
       } else {
         unsigned int n0 = n - 1;
         RbaseSymbolsImpl::R down = Rsqrt_def::Dichotomy_lb(x, y, p, n0);
         RbaseSymbolsImpl::R up = Rsqrt_def::Dichotomy_ub(x, y, p, n0);
         RbaseSymbolsImpl::R z =
             ::Rdiv(RbaseSymbolsImpl::Rplus(down, up),
                    ::IZR(Z::zpos(Positive::xo(Positive::xh()))));
         if (p(z)) {
           return z;
         } else {
           return up;
         }
       }
     }

     template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
     __attribute__((pure)) RbaseSymbolsImpl::R
     Rsqrt_def::dicho_lb(const RbaseSymbolsImpl::R _x0,
                         const RbaseSymbolsImpl::R _x1, F2 &&_x2,
                         const unsigned int _x3) {
       return Rsqrt_def::Dichotomy_lb(_x0, _x1, _x2, _x3);
     }

     template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
     __attribute__((pure)) RbaseSymbolsImpl::R
     Rsqrt_def::dicho_up(const RbaseSymbolsImpl::R _x0,
                         const RbaseSymbolsImpl::R _x1, F2 &&_x2,
                         const unsigned int _x3) {
       return Rsqrt_def::Dichotomy_ub(_x0, _x1, _x2, _x3);
     }

     template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
     std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
     Rsqrt_def::dicho_lb_cv(const RbaseSymbolsImpl::R x,
                            const RbaseSymbolsImpl::R y, F2 &&p) {
       return SeqProp::growing_cv([&](unsigned int _x0) -> RbaseSymbolsImpl::R {
         return Rsqrt_def::dicho_lb(x, y, p, _x0);
       });
     }

     template <MapsTo<bool, RbaseSymbolsImpl::R> F2>
     std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
     Rsqrt_def::dicho_up_cv(const RbaseSymbolsImpl::R x,
                            const RbaseSymbolsImpl::R y, F2 &&p) {
       return SeqProp::decreasing_cv(
           [&](unsigned int _x0) -> RbaseSymbolsImpl::R {
             return Rsqrt_def::dicho_up(x, y, p, _x0);
           });
     }

     template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
     std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
     Rsqrt_def::IVT(F0 &&f, const RbaseSymbolsImpl::R x,
                    const RbaseSymbolsImpl::R y) {
       std::shared_ptr<Sig<RbaseSymbolsImpl::R>> s =
           Rsqrt_def::dicho_lb_cv(x, y, [=](RbaseSymbolsImpl::R z) mutable {
             return Rsqrt_def::cond_positivity(f(z));
           });
       return std::visit(
           Overloaded{[&](const typename Sig<RbaseSymbolsImpl::R>::Exist _args)
                          -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
             std::shared_ptr<Sig<RbaseSymbolsImpl::R>> s0 =
                 Rsqrt_def::dicho_up_cv(
                     x, y, [=](RbaseSymbolsImpl::R z) mutable {
                       return Rsqrt_def::cond_positivity(f(z));
                     });
             return [&](void) {
               if (std::move(s0).use_count() == 1 &&
                   std::move(s0)->v().index() == 0) {
                 auto &_rf = std::get<0>(std::move(s0)->v_mut());
                 RbaseSymbolsImpl::R x0 = std::move(_rf.d_a0);
                 _rf.d_a0 = std::move(x0);
                 return std::move(s0);
               } else {
                 return std::visit(
                     Overloaded{
                         [](const typename Sig<RbaseSymbolsImpl::R>::Exist
                                _args0)
                             -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                           return Sig<RbaseSymbolsImpl::R>::exist(_args0.d_a0);
                         }},
                     std::move(s0)->v());
               }
             }();
           }},
           std::move(s)->v());
     }

     template <MapsTo<RbaseSymbolsImpl::R, RbaseSymbolsImpl::R> F0>
     std::shared_ptr<Sig<RbaseSymbolsImpl::R>>
     Rsqrt_def::IVT_cor(F0 &&f, const RbaseSymbolsImpl::R x,
                        const RbaseSymbolsImpl::R y) {
       std::shared_ptr<Sumor<bool>> s = ::total_order_T(::IZR(Z::z0()), f(x));
       return std::visit(
           Overloaded{
               [&](const typename Sumor<bool>::Inleft _args)
                   -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                 if (_args.d_a0) {
                   std::shared_ptr<Sumor<bool>> s1 =
                       ::total_order_T(::IZR(Z::z0()), f(y));
                   return std::visit(
                       Overloaded{
                           [&](const typename Sumor<bool>::Inleft _args0)
                               -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                             if (_args0.d_a0) {
                               throw std::logic_error("absurd case");
                             } else {
                               return Sig<RbaseSymbolsImpl::R>::exist(y);
                             }
                           },
                           [&](const typename Sumor<bool>::Inright _args0)
                               -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                             std::shared_ptr<Sig<RbaseSymbolsImpl::R>> h3 =
                                 [=](void) mutable {
                                   return Rsqrt_def::IVT(
                                       [&](RbaseSymbolsImpl::R _x0)
                                           -> RbaseSymbolsImpl::R {
                                         return Ranalysis1::opp_fct(f, _x0);
                                       },
                                       x, y);
                                 }();
                             std::shared_ptr<Sig<RbaseSymbolsImpl::R>> s2 =
                                 h3();
                             return [&](void) {
                               if (std::move(s2).use_count() == 1 &&
                                   std::move(s2)->v().index() == 0) {
                                 auto &_rf =
                                     std::get<0>(std::move(s2)->v_mut());
                                 RbaseSymbolsImpl::R x0 = std::move(_rf.d_a0);
                                 _rf.d_a0 = std::move(x0);
                                 return std::move(s2);
                               } else {
                                 return std::visit(
                                     Overloaded{[](const typename Sig<
                                                    RbaseSymbolsImpl::R>::Exist
                                                       _args1)
                                                    -> std::shared_ptr<Sig<
                                                        RbaseSymbolsImpl::R>> {
                                       return Sig<RbaseSymbolsImpl::R>::exist(
                                           _args1.d_a0);
                                     }},
                                     std::move(s2)->v());
                               }
                             }();
                           }},
                       std::move(s1)->v());
                 } else {
                   return Sig<RbaseSymbolsImpl::R>::exist(x);
                 }
               },
               [&](const typename Sumor<bool>::Inright _args)
                   -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                 std::shared_ptr<Sumor<bool>> s0 =
                     ::total_order_T(::IZR(Z::z0()), f(y));
                 return std::visit(
                     Overloaded{
                         [&](const typename Sumor<bool>::Inleft _args0)
                             -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                           if (_args0.d_a0) {
                             return Rsqrt_def::IVT(f, x, y);
                           } else {
                             return Sig<RbaseSymbolsImpl::R>::exist(y);
                           }
                         },
                         [](const typename Sumor<bool>::Inright _args0)
                             -> std::shared_ptr<Sig<RbaseSymbolsImpl::R>> {
                           throw std::logic_error("absurd case");
                         }},
                     std::move(s0)->v());
               }},
           std::move(s)->v());
     }

#endif // INCLUDED_DENSITY_POTENTIAL_TRACE
