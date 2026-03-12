#ifndef INCLUDED_BINARY_NUMS
#define INCLUDED_BINARY_NUMS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class comparison { Eq, Lt, Gt };

struct Positive {
  // TYPES
  struct xI {
    std::shared_ptr<Positive> _a0;
  };

  struct xO {
    std::shared_ptr<Positive> _a0;
  };

  struct xH {};

  using variant_t = std::variant<xI, xO, xH>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Positive(xI _v) : v_(std::move(_v)) {}

  explicit Positive(xO _v) : v_(std::move(_v)) {}

  explicit Positive(xH _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Positive> xI_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Positive>(new Positive(xI{a0}));
    }

    static std::shared_ptr<Positive> xO_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Positive>(new Positive(xO{a0}));
    }

    static std::shared_ptr<Positive> xH_() {
      return std::shared_ptr<Positive>(new Positive(xH{}));
    }

    static std::unique_ptr<Positive>
    xI_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Positive>(new Positive(xI{a0}));
    }

    static std::unique_ptr<Positive>
    xO_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Positive>(new Positive(xO{a0}));
    }

    static std::unique_ptr<Positive> xH_uptr() {
      return std::unique_ptr<Positive>(new Positive(xH{}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    std::shared_ptr<Positive> _a0;
  };

  using variant_t = std::variant<N0, Npos>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit N(N0 _v) : v_(std::move(_v)) {}

  explicit N(Npos _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<N> N0_() { return std::shared_ptr<N>(new N(N0{})); }

    static std::shared_ptr<N> Npos_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<N>(new N(Npos{a0}));
    }

    static std::unique_ptr<N> N0_uptr() {
      return std::unique_ptr<N>(new N(N0{}));
    }

    static std::unique_ptr<N> Npos_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<N>(new N(Npos{a0}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    std::shared_ptr<Positive> _a0;
  };

  struct Zneg {
    std::shared_ptr<Positive> _a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t v_;

  // CREATORS
  explicit Z(Z0 _v) : v_(std::move(_v)) {}

  explicit Z(Zpos _v) : v_(std::move(_v)) {}

  explicit Z(Zneg _v) : v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Z> Z0_() { return std::shared_ptr<Z>(new Z(Z0{})); }

    static std::shared_ptr<Z> Zpos_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Z>(new Z(Zpos{a0}));
    }

    static std::shared_ptr<Z> Zneg_(const std::shared_ptr<Positive> &a0) {
      return std::shared_ptr<Z>(new Z(Zneg{a0}));
    }

    static std::unique_ptr<Z> Z0_uptr() {
      return std::unique_ptr<Z>(new Z(Z0{}));
    }

    static std::unique_ptr<Z> Zpos_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Z>(new Z(Zpos{a0}));
    }

    static std::unique_ptr<Z> Zneg_uptr(const std::shared_ptr<Positive> &a0) {
      return std::unique_ptr<Z>(new Z(Zneg{a0}));
    }
  };

  // MANIPULATORS
  variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
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
  static std::shared_ptr<N> pred_N(const std::shared_ptr<Positive> &x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      std::shared_ptr<Positive> _a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t v_;

    // CREATORS
    explicit mask(IsNul _v) : v_(std::move(_v)) {}

    explicit mask(IsPos _v) : v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : v_(std::move(_v)) {}

  public:
    // TYPES
    struct ctor {
      ctor() = delete;

      static std::shared_ptr<mask> IsNul_() {
        return std::shared_ptr<mask>(new mask(IsNul{}));
      }

      static std::shared_ptr<mask> IsPos_(const std::shared_ptr<Positive> &a0) {
        return std::shared_ptr<mask>(new mask(IsPos{a0}));
      }

      static std::shared_ptr<mask> IsNeg_() {
        return std::shared_ptr<mask>(new mask(IsNeg{}));
      }

      static std::unique_ptr<mask> IsNul_uptr() {
        return std::unique_ptr<mask>(new mask(IsNul{}));
      }

      static std::unique_ptr<mask>
      IsPos_uptr(const std::shared_ptr<Positive> &a0) {
        return std::unique_ptr<mask>(new mask(IsPos{a0}));
      }

      static std::unique_ptr<mask> IsNeg_uptr() {
        return std::unique_ptr<mask>(new mask(IsNeg{}));
      }
    };

    // MANIPULATORS
    variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
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
  static std::shared_ptr<Positive> mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y);
  static comparison compare_cont(const comparison r,
                                 const std::shared_ptr<Positive> &x,
                                 const std::shared_ptr<Positive> &y);
  static comparison compare(const std::shared_ptr<Positive> &_x0,
                            const std::shared_ptr<Positive> &_x1);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive> &p, const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::xI _args) -> T1 {
                     std::shared_ptr<Positive> p0 = _args._a0;
                     return op(a, iter_op<T1>(op, std::move(p0), op(a, a)));
                   },
                   [&](const typename Positive::xO _args) -> T1 {
                     std::shared_ptr<Positive> p0 = _args._a0;
                     return iter_op<T1>(op, std::move(p0), op(a, a));
                   },
                   [&](const typename Positive::xH _args) -> T1 { return a; }},
        p->v());
  }

  static unsigned int to_nat(const std::shared_ptr<Positive> &x);
};

struct Coq_Pos {
  static std::shared_ptr<Positive> succ(const std::shared_ptr<Positive> &x);
  static std::shared_ptr<Positive> add(const std::shared_ptr<Positive> &x,
                                       const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive>
  add_carry(const std::shared_ptr<Positive> &x,
            const std::shared_ptr<Positive> &y);
  static std::shared_ptr<Positive> mul(const std::shared_ptr<Positive> &x,
                                       std::shared_ptr<Positive> y);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const std::shared_ptr<Positive> &p, const T1 a) {
    return std::visit(
        Overloaded{[&](const typename Positive::xI _args) -> T1 {
                     std::shared_ptr<Positive> p0 = _args._a0;
                     return op(a, iter_op<T1>(op, std::move(p0), op(a, a)));
                   },
                   [&](const typename Positive::xO _args) -> T1 {
                     std::shared_ptr<Positive> p0 = _args._a0;
                     return iter_op<T1>(op, std::move(p0), op(a, a));
                   },
                   [&](const typename Positive::xH _args) -> T1 { return a; }},
        p->v());
  }

  static unsigned int to_nat(const std::shared_ptr<Positive> &x);
};

struct BinNat {
  static std::shared_ptr<N> sub(std::shared_ptr<N> n,
                                const std::shared_ptr<N> &m);
  static comparison compare(const std::shared_ptr<N> &n,
                            const std::shared_ptr<N> &m);
  static std::shared_ptr<N> pred(const std::shared_ptr<N> &n);
  static std::shared_ptr<N> add(std::shared_ptr<N> n, std::shared_ptr<N> m);
  static std::shared_ptr<N> mul(const std::shared_ptr<N> &n,
                                const std::shared_ptr<N> &m);
  static unsigned int to_nat(const std::shared_ptr<N> &a);
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
  static comparison compare(const std::shared_ptr<Z> &x,
                            const std::shared_ptr<Z> &y);
  static unsigned int to_nat(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> abs(const std::shared_ptr<Z> &z);
};

struct Datatypes {
  static comparison CompOpp(const comparison r);
};

struct BinaryNums {
  static inline const std::shared_ptr<Positive> pos_one = Positive::ctor::xH_();
  static inline const std::shared_ptr<Positive> pos_five =
      Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()));
  static inline const std::shared_ptr<Positive> pos_add_result = Coq_Pos::add(
      Positive::ctor::xI_(Positive::ctor::xH_()),
      Positive::ctor::xI_(Positive::ctor::xI_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<Positive> pos_mul_result = Coq_Pos::mul(
      Positive::ctor::xO_(Positive::ctor::xO_(Positive::ctor::xH_())),
      Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<Positive> pos_succ_result =
      Coq_Pos::succ(Positive::ctor::xI_(
          Positive::ctor::xO_(Positive::ctor::xO_(Positive::ctor::xH_()))));
  static inline const std::shared_ptr<N> n_zero = N::ctor::N0_();
  static inline const std::shared_ptr<N> n_five = N::ctor::Npos_(
      Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<N> n_add_result = BinNat::add(
      N::ctor::Npos_(Positive::ctor::xO_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_())))),
      N::ctor::Npos_(Positive::ctor::xO_(Positive::ctor::xO_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))))));
  static inline const std::shared_ptr<N> n_mul_result = BinNat::mul(
      N::ctor::Npos_(
          Positive::ctor::xO_(Positive::ctor::xI_(Positive::ctor::xH_()))),
      N::ctor::Npos_(
          Positive::ctor::xI_(Positive::ctor::xI_(Positive::ctor::xH_()))));
  static inline const std::shared_ptr<N> n_sub_result =
      BinNat::sub(N::ctor::Npos_(Positive::ctor::xO_(Positive::ctor::xI_(
                      Positive::ctor::xO_(Positive::ctor::xH_())))),
                  N::ctor::Npos_(Positive::ctor::xI_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<N> n_pred_result =
      BinNat::pred(N::ctor::Npos_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))));
  static inline const comparison n_compare_result = BinNat::compare(
      N::ctor::Npos_(Positive::ctor::xI_(Positive::ctor::xH_())),
      N::ctor::Npos_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))));
  static inline const std::shared_ptr<Z> z_zero = Z::ctor::Z0_();
  static inline const std::shared_ptr<Z> z_pos = Z::ctor::Zpos_(
      Positive::ctor::xO_(Positive::ctor::xI_(Positive::ctor::xO_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))))));
  static inline const std::shared_ptr<Z> z_neg = Z::ctor::Zneg_(
      Positive::ctor::xI_(Positive::ctor::xI_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<Z> z_add_result =
      BinInt::add(Z::ctor::Zpos_(Positive::ctor::xO_(Positive::ctor::xI_(
                      Positive::ctor::xO_(Positive::ctor::xH_())))),
                  Z::ctor::Zneg_(Positive::ctor::xI_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<Z> z_mul_result = BinInt::mul(
      Z::ctor::Zneg_(
          Positive::ctor::xO_(Positive::ctor::xO_(Positive::ctor::xH_()))),
      Z::ctor::Zpos_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))));
  static inline const std::shared_ptr<Z> z_sub_result =
      BinInt::sub(Z::ctor::Zpos_(Positive::ctor::xI_(Positive::ctor::xH_())),
                  Z::ctor::Zpos_(Positive::ctor::xO_(Positive::ctor::xI_(
                      Positive::ctor::xO_(Positive::ctor::xH_())))));
  static inline const std::shared_ptr<Z> z_abs_result =
      BinInt::abs(Z::ctor::Zneg_(Positive::ctor::xO_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xI_(
              Positive::ctor::xO_(Positive::ctor::xH_())))))));
  static inline const comparison z_compare_result = BinInt::compare(
      Z::ctor::Zneg_(Positive::ctor::xI_(Positive::ctor::xH_())),
      Z::ctor::Zpos_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))));
  static inline const unsigned int pos_to_nat = Coq_Pos::to_nat(
      Positive::ctor::xI_(Positive::ctor::xI_(Positive::ctor::xH_())));
  static inline const unsigned int n_to_nat =
      BinNat::to_nat(N::ctor::Npos_(Positive::ctor::xI_(
          Positive::ctor::xI_(Positive::ctor::xI_(Positive::ctor::xH_())))));
  static inline const unsigned int z_to_nat =
      BinInt::to_nat(Z::ctor::Zpos_(Positive::ctor::xO_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_())))));
  static std::shared_ptr<N> n_max(std::shared_ptr<N> a, std::shared_ptr<N> b);
  static std::shared_ptr<Z> z_sign(const std::shared_ptr<Z> &z);
  static inline const std::shared_ptr<N> test_n_max =
      n_max(N::ctor::Npos_(Positive::ctor::xI_(Positive::ctor::xH_())),
            N::ctor::Npos_(Positive::ctor::xI_(
                Positive::ctor::xI_(Positive::ctor::xH_()))));
  static inline const std::shared_ptr<Z> test_z_sign_pos =
      z_sign(Z::ctor::Zpos_(
          Positive::ctor::xI_(Positive::ctor::xO_(Positive::ctor::xH_()))));
  static inline const std::shared_ptr<Z> test_z_sign_neg =
      z_sign(Z::ctor::Zneg_(Positive::ctor::xI_(Positive::ctor::xH_())));
  static inline const std::shared_ptr<Z> test_z_sign_zero =
      z_sign(Z::ctor::Z0_());
};

#endif // INCLUDED_BINARY_NUMS
