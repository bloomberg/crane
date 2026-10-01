#ifndef INCLUDED_MISSING_INDUCTIVE_POS_MASK
#define INCLUDED_MISSING_INDUCTIVE_POS_MASK

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

struct Pos {
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
};

struct Coq_Pos {
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
};

struct MissingInductivePosMask {
  static Coq_Pos::mask f(const Positive &x0_, const Positive &x1_);
};

#endif // INCLUDED_MISSING_INDUCTIVE_POS_MASK
