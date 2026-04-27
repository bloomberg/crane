#ifndef INCLUDED_BINARY_NUMS
#define INCLUDED_BINARY_NUMS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct Positive {
  // TYPES
  struct XI {
    std::unique_ptr<Positive> d_a0;
  };

  struct XO {
    std::unique_ptr<Positive> d_a0;
  };

  struct XH {};

  using variant_t = std::variant<XI, XO, XH>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Positive() {}

  explicit Positive(XI _v) : d_v_(std::move(_v)) {}

  explicit Positive(XO _v) : d_v_(std::move(_v)) {}

  explicit Positive(XH _v) : d_v_(_v) {}

  Positive(const Positive &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Positive(Positive &&_other) : d_v_(std::move(_other.d_v_)) {}

  Positive &operator=(const Positive &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Positive &operator=(Positive &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Positive clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<XI>(_sv.v())) {
      const auto &[d_a0] = std::get<XI>(_sv.v());
      return Positive(
          XI{d_a0 ? std::make_unique<Positive>(d_a0->clone()) : nullptr});
    } else if (std::holds_alternative<XO>(_sv.v())) {
      const auto &[d_a0] = std::get<XO>(_sv.v());
      return Positive(
          XO{d_a0 ? std::make_unique<Positive>(d_a0->clone()) : nullptr});
    } else {
      return Positive(XH{});
    }
  }

  // CREATORS
  __attribute__((pure)) static Positive xi(const Positive &a0) {
    return Positive(XI{std::make_unique<Positive>(a0)});
  }

  __attribute__((pure)) static Positive xo(const Positive &a0) {
    return Positive(XO{std::make_unique<Positive>(a0)});
  }

  __attribute__((pure)) static Positive xh() { return Positive(XH{}); }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Positive *operator->() { return this; }

  __attribute__((pure)) const Positive *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Positive(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    Positive d_a0;
  };

  using variant_t = std::variant<N0, Npos>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  N() {}

  explicit N(N0 _v) : d_v_(_v) {}

  explicit N(Npos _v) : d_v_(std::move(_v)) {}

  N(const N &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  N(N &&_other) : d_v_(std::move(_other.d_v_)) {}

  N &operator=(const N &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  N &operator=(N &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) N clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<N0>(_sv.v())) {
      return N(N0{});
    } else {
      const auto &[d_a0] = std::get<Npos>(_sv.v());
      return N(Npos{d_a0.clone()});
    }
  }

  // CREATORS
  constexpr static N n0() { return N(N0{}); }

  __attribute__((pure)) static N npos(Positive a0) {
    return N(Npos{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) N *operator->() { return this; }

  __attribute__((pure)) const N *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = N(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Z {
  // TYPES
  struct Z0 {};

  struct Zpos {
    Positive d_a0;
  };

  struct Zneg {
    Positive d_a0;
  };

  using variant_t = std::variant<Z0, Zpos, Zneg>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Z() {}

  explicit Z(Z0 _v) : d_v_(_v) {}

  explicit Z(Zpos _v) : d_v_(std::move(_v)) {}

  explicit Z(Zneg _v) : d_v_(std::move(_v)) {}

  Z(const Z &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Z(Z &&_other) : d_v_(std::move(_other.d_v_)) {}

  Z &operator=(const Z &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  Z &operator=(Z &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Z clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Z0>(_sv.v())) {
      return Z(Z0{});
    } else if (std::holds_alternative<Zpos>(_sv.v())) {
      const auto &[d_a0] = std::get<Zpos>(_sv.v());
      return Z(Zpos{d_a0.clone()});
    } else {
      const auto &[d_a0] = std::get<Zneg>(_sv.v());
      return Z(Zneg{d_a0.clone()});
    }
  }

  // CREATORS
  constexpr static Z z0() { return Z(Z0{}); }

  __attribute__((pure)) static Z zpos(Positive a0) {
    return Z(Zpos{std::move(a0)});
  }

  __attribute__((pure)) static Z zneg(Positive a0) {
    return Z(Zneg{std::move(a0)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Z *operator->() { return this; }

  __attribute__((pure)) const Z *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Z(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct Pos {
  __attribute__((pure)) static Positive succ(const Positive &x);
  __attribute__((pure)) static Positive add(const Positive &x,
                                            const Positive &y);
  __attribute__((pure)) static Positive add_carry(const Positive &x,
                                                  const Positive &y);
  __attribute__((pure)) static Positive pred_double(const Positive &x);
  __attribute__((pure)) static N pred_N(const Positive &x);

  struct mask {
    // TYPES
    struct IsNul {};

    struct IsPos {
      Positive d_a0;
    };

    struct IsNeg {};

    using variant_t = std::variant<IsNul, IsPos, IsNeg>;

  private:
    // DATA
    variant_t d_v_;

  public:
    // CREATORS
    mask() {}

    explicit mask(IsNul _v) : d_v_(_v) {}

    explicit mask(IsPos _v) : d_v_(std::move(_v)) {}

    explicit mask(IsNeg _v) : d_v_(_v) {}

    mask(const mask &_other) : d_v_(std::move(_other.clone().d_v_)) {}

    mask(mask &&_other) : d_v_(std::move(_other.d_v_)) {}

    mask &operator=(const mask &_other) {
      d_v_ = std::move(_other.clone().d_v_);
      return *this;
    }

    mask &operator=(mask &&_other) {
      d_v_ = std::move(_other.d_v_);
      return *this;
    }

    // ACCESSORS
    __attribute__((pure)) mask clone() const {
      auto &&_sv = *(this);
      if (std::holds_alternative<IsNul>(_sv.v())) {
        return mask(IsNul{});
      } else if (std::holds_alternative<IsPos>(_sv.v())) {
        const auto &[d_a0] = std::get<IsPos>(_sv.v());
        return mask(IsPos{d_a0.clone()});
      } else {
        return mask(IsNeg{});
      }
    }

    // CREATORS
    constexpr static mask isnul() { return mask(IsNul{}); }

    __attribute__((pure)) static mask ispos(Positive a0) {
      return mask(IsPos{std::move(a0)});
    }

    constexpr static mask isneg() { return mask(IsNeg{}); }

    // MANIPULATORS
    __attribute__((pure)) variant_t &v_mut() { return d_v_; }

    // ACCESSORS
    __attribute__((pure)) mask *operator->() { return this; }

    __attribute__((pure)) const mask *operator->() const { return this; }

    __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

    __attribute__((pure)) bool operator==(std::nullptr_t) const {
      return false;
    }

    // MANIPULATORS
    void reset() { *this = mask(); }

    // ACCESSORS
    __attribute__((pure)) const variant_t &v() const { return d_v_; }
  };

  __attribute__((pure)) static mask succ_double_mask(const mask &x);
  __attribute__((pure)) static mask double_mask(const mask &x);
  __attribute__((pure)) static mask double_pred_mask(const Positive &x);
  __attribute__((pure)) static mask sub_mask(const Positive &x,
                                             const Positive &y);
  __attribute__((pure)) static mask sub_mask_carry(const Positive &x,
                                                   const Positive &y);
  __attribute__((pure)) static Positive mul(const Positive &x, Positive y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const Positive &x, const Positive &y);
  __attribute__((pure)) static Comparison compare(const Positive &_x0,
                                                  const Positive &_x1);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const Positive &p, const T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[d_a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *(d_a0), op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[d_a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *(d_a0), op(a, a));
    } else {
      return a;
    }
  }

  __attribute__((pure)) static unsigned int to_nat(const Positive &x);
};

struct Coq_Pos {
  __attribute__((pure)) static Positive succ(const Positive &x);
  __attribute__((pure)) static Positive add(const Positive &x,
                                            const Positive &y);
  __attribute__((pure)) static Positive add_carry(const Positive &x,
                                                  const Positive &y);
  __attribute__((pure)) static Positive mul(const Positive &x, Positive y);

  template <typename T1, MapsTo<T1, T1, T1> F0>
  static T1 iter_op(F0 &&op, const Positive &p, const T1 a) {
    if (std::holds_alternative<typename Positive::XI>(p.v())) {
      const auto &[d_a0] = std::get<typename Positive::XI>(p.v());
      return op(a, iter_op<T1>(op, *(d_a0), op(a, a)));
    } else if (std::holds_alternative<typename Positive::XO>(p.v())) {
      const auto &[d_a0] = std::get<typename Positive::XO>(p.v());
      return iter_op<T1>(op, *(d_a0), op(a, a));
    } else {
      return a;
    }
  }

  __attribute__((pure)) static unsigned int to_nat(const Positive &x);
};

struct BinNat {
  __attribute__((pure)) static N sub(N n, const N &m);
  __attribute__((pure)) static Comparison compare(const N &n, const N &m);
  __attribute__((pure)) static N pred(const N &n);
  __attribute__((pure)) static N add(N n, N m);
  __attribute__((pure)) static N mul(const N &n, const N &m);
  __attribute__((pure)) static unsigned int to_nat(const N &a);
};

struct BinInt {
  __attribute__((pure)) static Z double_(const Z &x);
  __attribute__((pure)) static Z succ_double(const Z &x);
  __attribute__((pure)) static Z pred_double(const Z &x);
  __attribute__((pure)) static Z pos_sub(const Positive &x, const Positive &y);
  __attribute__((pure)) static Z add(Z x, Z y);
  __attribute__((pure)) static Z opp(const Z &x);
  __attribute__((pure)) static Z sub(const Z &m, const Z &n);
  __attribute__((pure)) static Z mul(const Z &x, const Z &y);
  __attribute__((pure)) static Comparison compare(const Z &x, const Z &y);
  __attribute__((pure)) static unsigned int to_nat(const Z &z);
  __attribute__((pure)) static Z abs(const Z &z);
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
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
  static inline const unsigned int pos_to_nat =
      Coq_Pos::to_nat(Positive::xi(Positive::xi(Positive::xh())));
  static inline const unsigned int n_to_nat = BinNat::to_nat(
      N::npos(Positive::xi(Positive::xi(Positive::xi(Positive::xh())))));
  static inline const unsigned int z_to_nat = BinInt::to_nat(
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  __attribute__((pure)) static N n_max(N a, N b);
  __attribute__((pure)) static Z z_sign(const Z &z);
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
