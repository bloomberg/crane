#ifndef INCLUDED_LIFTED_HELPER_IN_MEMBER_INIT
#define INCLUDED_LIFTED_HELPER_IN_MEMBER_INIT

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

/// A helper lifted out of a module member's initialiser is defined after the
/// struct it came out of, so its call site -- the initialiser, which is not a
/// complete-class context -- names it before it is declared: "use of
/// undeclared identifier '_shifted_F'".
///
/// The declaration belongs at the top of the file, above every definition.
/// Two members so that the pair exercises the claim table that decides which
/// emission path owns a lifted helper; one alone does not distinguish them.
struct LiftedHelperInMemberInit {
  static inline const std::pair<bool, Positive> shifted = []() {
    return std::make_pair(false, []() {
      auto f_impl = [](auto &_self_f, uint64_t n) -> Positive {
        if (n <= 0) {
          return Positive::xh();
        } else {
          uint64_t n0 = n - 1;
          return Positive::xo(_self_f(_self_f, n0));
        }
      };
      auto f = [&](uint64_t n) -> Positive { return f_impl(f_impl, n); };
      return f(UINT64_C(4));
    }());
  }();
  static inline const std::pair<bool, Positive> doubled = []() {
    return std::make_pair(true, []() {
      auto f_impl = [](auto &_self_f, uint64_t n) -> Positive {
        if (n <= 0) {
          return Positive::xh();
        } else {
          uint64_t n0 = n - 1;
          return Positive::xi(_self_f(_self_f, n0));
        }
      };
      auto f = [&](uint64_t n) -> Positive { return f_impl(f_impl, n); };
      return f(UINT64_C(3));
    }());
  }();
};

#endif // INCLUDED_LIFTED_HELPER_IN_MEMBER_INIT
