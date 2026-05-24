#ifndef INCLUDED_BINARY_NUMS
#define INCLUDED_BINARY_NUMS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

enum class Comparison { EQ, LT, GT };

struct Positive {
  // TYPES
  struct XI {
    std::shared_ptr<Positive> a0;
  };

  struct XO {
    std::shared_ptr<Positive> a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : v_(std::move(_v)) {}

  explicit Positive(XO _v) : v_(std::move(_v)) {}

  explicit Positive(XH _v) : v_(_v) {}

  static Positive xi(Positive a0) {
    return Positive(XI{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xo(Positive a0) {
    return Positive(XO{std::make_shared<Positive>(std::move(a0))});
  }

  static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    Positive a0;
  };

  using variant_t = std::variant<N0, Npos>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  N() {}

  explicit N(N0 _v) : v_(_v) {}

  explicit N(Npos _v) : v_(std::move(_v)) {}

  static N n0() { return N(N0{}); }

  static N npos(Positive a0) { return N(Npos{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    Positive a0;
  };

  struct Zneg {
    Positive a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Z() {}

  explicit Z(Z0 _v) : v_(_v) {}

  explicit Z(Zpos _v) : v_(std::move(_v)) {}

  explicit Z(Zneg _v) : v_(std::move(_v)) {}

  static Z z0() { return Z(Z0{}); }

  static Z zpos(Positive a0) { return Z(Zpos{std::move(a0)}); }

  static Z zneg(Positive a0) { return Z(Zneg{std::move(a0)}); }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive pred_double(const Positive &x);
  static N pred_N(const Positive &x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      Positive a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mask() {}

    explicit mask(IsNul _v) : v_(_v) {}

    explicit mask(IsPos _v) : v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : v_(_v) {}

    static mask isnul() { return mask(IsNul{}); }

    static mask ispos(Positive a0) { return mask(IsPos{std::move(a0)}); }

    static mask isneg() { return mask(IsNeg{}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static mask succ_double_mask(const mask &x);
  static mask double_mask(const mask &x);
  static mask double_pred_mask(const Positive &x);
  static mask sub_mask(const Positive &x, const Positive &y);
  static mask sub_mask_carry(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &_x0, const Positive &_x1);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *a0, op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *a0, op(a, a));
    } else {
      return a;
    }
  }

  static uint64_t to_nat(const Positive &x);
};

struct Coq_Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, T1 &>
  static T1 iter_op(F0 &&op, const Positive &p, T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *a0, op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *a0, op(a, a));
    } else {
      return a;
    }
  }

  static uint64_t to_nat(const Positive &x);
};

struct BinNat {
  static N sub(N n, const N &m);
  static Comparison compare(const N &n, const N &m);
  static N pred(const N &n);
  static N add(N n, N m);
  static N mul(const N &n, const N &m);
  static uint64_t to_nat(const N &a);
};

struct BinInt {
  static Z double_(const Z &x);
  static Z succ_double(const Z &x);
  static Z pred_double(const Z &x);
  static Z pos_sub(const Positive &x, const Positive &y);
  static Z add(Z x, Z y);
  static Z opp(const Z &x);
  static Z sub(const Z &m, const Z &n);
  static Z mul(const Z &x, const Z &y);
  static Comparison compare(const Z &x, const Z &y);
  static uint64_t to_nat(const Z &z);
  static Z abs(const Z &z);
};

struct Datatypes {
  static Comparison CompOpp(Comparison r);
};

struct BinaryNums {
  static inline const Positive pos_one = Positive::xh();
  static inline const Positive pos_five =
      Positive::xi(Positive::xo(Positive::xh()));
  static inline const Positive pos_add_result = Coq_Pos::add(
      Positive::xi(Positive::xh()), Positive::xi(Positive::xi(Positive::xh())));
  static inline const Positive pos_mul_result =
      Coq_Pos::mul(Positive::xo(Positive::xo(Positive::xh())),
                   Positive::xi(Positive::xo(Positive::xh())));
  static inline const Positive pos_succ_result =
      Coq_Pos::succ(Positive::xi(Positive::xo(Positive::xo(Positive::xh()))));
  static inline const N n_zero = N::n0();
  static inline const N n_five =
      N::npos(Positive::xi(Positive::xo(Positive::xh())));
  static inline const N n_add_result = BinNat::add(
      N::npos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      N::npos(Positive::xo(
          Positive::xo(Positive::xi(Positive::xo(Positive::xh()))))));
  static inline const N n_mul_result =
      BinNat::mul(N::npos(Positive::xo(Positive::xi(Positive::xh()))),
                  N::npos(Positive::xi(Positive::xi(Positive::xh()))));
  static inline const N n_sub_result = BinNat::sub(
      N::npos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      N::npos(Positive::xi(Positive::xh())));
  static inline const N n_pred_result =
      BinNat::pred(N::npos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const Comparison n_compare_result =
      BinNat::compare(N::npos(Positive::xi(Positive::xh())),
                      N::npos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const Z z_zero = Z::z0();
  static inline const Z z_pos = Z::zpos(Positive::xo(
      Positive::xi(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))))));
  static inline const Z z_neg =
      Z::zneg(Positive::xi(Positive::xi(Positive::xh())));
  static inline const Z z_add_result = BinInt::add(
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      Z::zneg(Positive::xi(Positive::xh())));
  static inline const Z z_mul_result =
      BinInt::mul(Z::zneg(Positive::xo(Positive::xo(Positive::xh()))),
                  Z::zpos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const Z z_sub_result = BinInt::sub(
      Z::zpos(Positive::xi(Positive::xh())),
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  static inline const Z z_abs_result = BinInt::abs(Z::zneg(Positive::xo(
      Positive::xi(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))))));
  static inline const Comparison z_compare_result =
      BinInt::compare(Z::zneg(Positive::xi(Positive::xh())),
                      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const uint64_t pos_to_nat =
      Coq_Pos::to_nat(Positive::xi(Positive::xi(Positive::xh())));
  static inline const uint64_t n_to_nat = BinNat::to_nat(
      N::npos(Positive::xi(Positive::xi(Positive::xi(Positive::xh())))));
  static inline const uint64_t z_to_nat = BinInt::to_nat(
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  static N n_max(N a, N b);
  static Z z_sign(const Z &z);
  static inline const N test_n_max =
      n_max(N::npos(Positive::xi(Positive::xh())),
            N::npos(Positive::xi(Positive::xi(Positive::xh()))));
  static inline const Z test_z_sign_pos =
      z_sign(Z::zpos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const Z test_z_sign_neg =
      z_sign(Z::zneg(Positive::xi(Positive::xh())));
  static inline const Z test_z_sign_zero = z_sign(Z::z0());
};

#endif // INCLUDED_BINARY_NUMS
