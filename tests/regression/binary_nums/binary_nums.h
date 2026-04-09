#ifndef INCLUDED_BINARY_NUMS
#define INCLUDED_BINARY_NUMS

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Comparison { e_EQ, e_LT, e_GT };

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

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct N {
  // TYPES
  struct N0 {};

  struct Npos {
    std::shared_ptr<Positive> d_a0;
  };

  using variant_t = std::variant<N0, Npos>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit N(N0 _v) : d_v_(std::move(_v)) {}

  explicit N(Npos _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<N> n0() { return std::make_shared<N>(N0{}); }

  static std::shared_ptr<N> npos(const std::shared_ptr<Positive> &a0) {
    return std::make_shared<N>(Npos{a0});
  }

  static std::shared_ptr<N> npos(std::shared_ptr<Positive> &&a0) {
    return std::make_shared<N>(Npos{std::move(a0)});
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

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
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
};

struct BinNat {
  static std::shared_ptr<N> sub(std::shared_ptr<N> n,
                                const std::shared_ptr<N> &m);
  __attribute__((pure)) static Comparison compare(const std::shared_ptr<N> &n,
                                                  const std::shared_ptr<N> &m);
  static std::shared_ptr<N> pred(const std::shared_ptr<N> &n);
  static std::shared_ptr<N> add(std::shared_ptr<N> n, std::shared_ptr<N> m);
  static std::shared_ptr<N> mul(const std::shared_ptr<N> &n,
                                const std::shared_ptr<N> &m);
  __attribute__((pure)) static unsigned int to_nat(const std::shared_ptr<N> &a);
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
  __attribute__((pure)) static unsigned int to_nat(const std::shared_ptr<Z> &z);
  static std::shared_ptr<Z> abs(const std::shared_ptr<Z> &z);
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
};

struct BinaryNums {
  static inline const std::shared_ptr<Positive> pos_one = Positive::xh();
  static inline const std::shared_ptr<Positive> pos_five =
      Positive::xi(Positive::xo(Positive::xh()));
  static inline const std::shared_ptr<Positive> pos_add_result = Coq_Pos::add(
      Positive::xi(Positive::xh()), Positive::xi(Positive::xi(Positive::xh())));
  static inline const std::shared_ptr<Positive> pos_mul_result =
      Coq_Pos::mul(Positive::xo(Positive::xo(Positive::xh())),
                   Positive::xi(Positive::xo(Positive::xh())));
  static inline const std::shared_ptr<Positive> pos_succ_result =
      Coq_Pos::succ(Positive::xi(Positive::xo(Positive::xo(Positive::xh()))));
  static inline const std::shared_ptr<N> n_zero = N::n0();
  static inline const std::shared_ptr<N> n_five =
      N::npos(Positive::xi(Positive::xo(Positive::xh())));
  static inline const std::shared_ptr<N> n_add_result = BinNat::add(
      N::npos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      N::npos(Positive::xo(
          Positive::xo(Positive::xi(Positive::xo(Positive::xh()))))));
  static inline const std::shared_ptr<N> n_mul_result =
      BinNat::mul(N::npos(Positive::xo(Positive::xi(Positive::xh()))),
                  N::npos(Positive::xi(Positive::xi(Positive::xh()))));
  static inline const std::shared_ptr<N> n_sub_result = BinNat::sub(
      N::npos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      N::npos(Positive::xi(Positive::xh())));
  static inline const std::shared_ptr<N> n_pred_result =
      BinNat::pred(N::npos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const Comparison n_compare_result =
      BinNat::compare(N::npos(Positive::xi(Positive::xh())),
                      N::npos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const std::shared_ptr<Z> z_zero = Z::z0();
  static inline const std::shared_ptr<Z> z_pos = Z::zpos(Positive::xo(
      Positive::xi(Positive::xo(Positive::xi(Positive::xo(Positive::xh()))))));
  static inline const std::shared_ptr<Z> z_neg =
      Z::zneg(Positive::xi(Positive::xi(Positive::xh())));
  static inline const std::shared_ptr<Z> z_add_result = BinInt::add(
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))),
      Z::zneg(Positive::xi(Positive::xh())));
  static inline const std::shared_ptr<Z> z_mul_result =
      BinInt::mul(Z::zneg(Positive::xo(Positive::xo(Positive::xh()))),
                  Z::zpos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const std::shared_ptr<Z> z_sub_result = BinInt::sub(
      Z::zpos(Positive::xi(Positive::xh())),
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  static inline const std::shared_ptr<Z> z_abs_result =
      BinInt::abs(Z::zneg(Positive::xo(Positive::xi(
          Positive::xo(Positive::xi(Positive::xo(Positive::xh())))))));
  static inline const Comparison z_compare_result =
      BinInt::compare(Z::zneg(Positive::xi(Positive::xh())),
                      Z::zpos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const unsigned int pos_to_nat =
      Coq_Pos::to_nat(Positive::xi(Positive::xi(Positive::xh())));
  static inline const unsigned int n_to_nat = BinNat::to_nat(
      N::npos(Positive::xi(Positive::xi(Positive::xi(Positive::xh())))));
  static inline const unsigned int z_to_nat = BinInt::to_nat(
      Z::zpos(Positive::xo(Positive::xi(Positive::xo(Positive::xh())))));
  static std::shared_ptr<N> n_max(std::shared_ptr<N> a, std::shared_ptr<N> b);
  static std::shared_ptr<Z> z_sign(const std::shared_ptr<Z> &z);
  static inline const std::shared_ptr<N> test_n_max =
      n_max(N::npos(Positive::xi(Positive::xh())),
            N::npos(Positive::xi(Positive::xi(Positive::xh()))));
  static inline const std::shared_ptr<Z> test_z_sign_pos =
      z_sign(Z::zpos(Positive::xi(Positive::xo(Positive::xh()))));
  static inline const std::shared_ptr<Z> test_z_sign_neg =
      z_sign(Z::zneg(Positive::xi(Positive::xh())));
  static inline const std::shared_ptr<Z> test_z_sign_zero = z_sign(Z::z0());
};

#endif // INCLUDED_BINARY_NUMS
