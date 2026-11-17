#ifndef INCLUDED_CUSTOM_MATCH_LAMBDA_SCRUTINEE
#define INCLUDED_CUSTOM_MATCH_LAMBDA_SCRUTINEE

#include <atomic>
#include <memory>
#include <utility>
#include <variant>

struct Positive;

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
  ~Positive() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Positive> {
      if (auto *_alt = std::get_if<XI>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      if (auto *_alt = std::get_if<XO>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Positive> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Positive(const Positive &) = default;
  Positive &operator=(const Positive &) = default;
  Positive(Positive &&) = default;
  Positive &operator=(Positive &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CustomMatchLambdaScrutinee {
  enum class Fpv { FP_HALF, FP_FLOAT, FP_DOUBLE };

  struct dtyp_base {
    // TYPES
    struct DTYPE_I {
      Positive sz;
    };

    struct DTYPE_Iptr {};

    struct DTYPE_FP {
      Fpv fp;
    };

    struct DTYPE_B {
      Positive sz;
    };

    using variant_t = std::variant<DTYPE_I, DTYPE_Iptr, DTYPE_FP, DTYPE_B>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    dtyp_base() {}

    explicit dtyp_base(DTYPE_I _v) : v_(std::move(_v)) {}

    explicit dtyp_base(DTYPE_Iptr _v) : v_(_v) {}

    explicit dtyp_base(DTYPE_FP _v) : v_(std::move(_v)) {}

    explicit dtyp_base(DTYPE_B _v) : v_(std::move(_v)) {}

    static dtyp_base dtype_i(Positive sz) {
      return dtyp_base(DTYPE_I{std::move(sz)});
    }

    static dtyp_base dtype_iptr() { return dtyp_base(DTYPE_Iptr{}); }

    static dtyp_base dtype_fp(Fpv fp) { return dtyp_base(DTYPE_FP{fp}); }

    static dtyp_base dtype_b(Positive sz) {
      return dtyp_base(DTYPE_B{std::move(sz)});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  static bool dtyp_base_eq_dec(const dtyp_base &t1, const dtyp_base &t2);
  static bool dtyp_base_eqb(const dtyp_base &a, const dtyp_base &b);
  static inline const bool same_i =
      dtyp_base_eqb(dtyp_base::dtype_i(Positive::xo(Positive::xo(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
                    dtyp_base::dtype_i(Positive::xo(Positive::xo(Positive::xo(
                        Positive::xo(Positive::xo(Positive::xh())))))));
  static inline const bool diff_i = dtyp_base_eqb(
      dtyp_base::dtype_i(Positive::xo(Positive::xo(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))))),
      dtyp_base::dtype_i(Positive::xo(Positive::xo(Positive::xo(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh()))))))));
  static inline const bool diff_ctor =
      dtyp_base_eqb(dtyp_base::dtype_i(
          Positive::xo(Positive::xo(Positive::xo(Positive::xh())))),
                    dtyp_base::dtype_b(Positive::xo(
                        Positive::xo(Positive::xo(Positive::xh())))));
  static inline const bool same_fp = dtyp_base_eqb(
      dtyp_base::dtype_fp(Fpv::FP_FLOAT), dtyp_base::dtype_fp(Fpv::FP_FLOAT));
  static inline const bool diff_fp = dtyp_base_eqb(
      dtyp_base::dtype_fp(Fpv::FP_FLOAT), dtyp_base::dtype_fp(Fpv::FP_DOUBLE));
};

#endif // INCLUDED_CUSTOM_MATCH_LAMBDA_SCRUTINEE
