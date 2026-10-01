#ifndef INCLUDED_CONCEPT_AFTER_USE
#define INCLUDED_CONCEPT_AFTER_USE

#include <atomic>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

enum class Comparison;
struct Positive;
struct N;

struct Coq_Pos {
  static Positive succ(const Positive &x);
  static Positive add(const Positive &x, const Positive &y);
  static Positive add_carry(const Positive &x, const Positive &y);
  static Positive mul(const Positive &x, Positive y);
};
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
  ~Positive() {
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
  Positive(Positive &&) noexcept = default;
  Positive &operator=(Positive &&) noexcept = default;

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

struct Pos {
  static Positive pred_double(const Positive &x);

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
  static Comparison compare_cont(Comparison r, const Positive &x,
                                 const Positive &y);
  static Comparison compare(const Positive &x0_, const Positive &x1_);
  static bool eqb(const Positive &p, const Positive &q);
};

struct BinNat {
  static N succ_double(const N &x);
  static N double_(const N &n);
  static N sub(N n, const N &m);
  static Comparison compare(const N &n, const N &m);
  static bool leb(const N &x, const N &y);
  static std::pair<N, N> pos_div_eucl(const Positive &a, const N &b);
  static N mul(const N &n, const N &m);
  static bool eqb(const N &n, const N &m);
  static std::pair<N, N> div_eucl(const N &a, const N &b);
  static N div(const N &a, const N &b);
};

/// A class and a function generic over it, in one module.  Crane emits the
/// class as a C++ concept Size, and walk as a member template
/// template <Size _tcI0> of the module's struct -- but the concept is
/// printed after that struct, so the template names a concept that is not
/// declared yet: "unknown type name 'Size'", and every call to walk fails
/// with it.  Moving Size into a module of its own, as Vellvm's classes are,
/// orders the output correctly.
///
/// Found while reducing borrowed_field_moved_into_method.
struct ConceptAfterUse {
  struct ty {
    // TYPES
    struct TB {
      Positive n;
    };

    struct TA {
      N sz;
      std::shared_ptr<ty> t;
    };

    using variant_t = std::variant<TB, TA>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ty() {}

    explicit ty(TB _v) : v_(std::move(_v)) {}

    explicit ty(TA _v) : v_(std::move(_v)) {}

    static ty tb(Positive n) { return ty(TB{std::move(n)}); }

    static ty ta(N sz, ty t) {
      return ty(TA{std::move(sz), std::make_shared<ty>(std::move(t))});
    }

    // MANIPULATORS
    ~ty() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<ty> {
        if (auto *_alt = std::get_if<TA>(&_v)) {
          if (_alt->t && _alt->t.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->t);
          }
        }
        return nullptr;
      };
      std::shared_ptr<ty> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    ty(const ty &) = default;
    ty &operator=(const ty &) = default;
    ty(ty &&) noexcept = default;
    ty &operator=(ty &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, Positive &> &&
             std::is_invocable_r_v<T1, F1 &, N &, ty &, T1 &>
  static T1 ty_rect(F0 &&f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TB>(t.v())) {
      const auto &[n0] = std::get<typename ty::TB>(t.v());
      return f(n0);
    } else {
      const auto &[sz1, t1] = std::get<typename ty::TA>(t.v());
      return f0(sz1, *t1, ty_rect<T1>(f, f0, *t1));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, Positive &> &&
             std::is_invocable_r_v<T1, F1 &, N &, ty &, T1 &>
  static T1 ty_rec(F0 &&f, F1 &&f0, const ty &t) {
    if (std::holds_alternative<typename ty::TB>(t.v())) {
      const auto &[n0] = std::get<typename ty::TB>(t.v());
      return f(n0);
    } else {
      const auto &[sz1, t1] = std::get<typename ty::TA>(t.v());
      return f0(sz1, *t1, ty_rec<T1>(f, f0, *t1));
    }
  }

  template <typename _tcI0> static N walk(const ty &t) {
    if (std::holds_alternative<typename ty::TB>(t.v())) {
      return N::n0();
    } else {
      const auto &[sz0, t0] = std::get<typename ty::TA>(t.v());
      return _tcI0::size_of(*t0);
    }
  }

  static N sz(const ty &t);

  struct SizeI {
    static N size_of(ty a0) { return sz(std::move(a0)); }
  };

  static bool check(std::monostate _x);
};

template <typename I>
concept Size = requires {
  { I::size_of(std::declval<ConceptAfterUse::ty>()) } -> std::convertible_to<N>;
};

static_assert(Size<ConceptAfterUse::SizeI>);

#endif // INCLUDED_CONCEPT_AFTER_USE
