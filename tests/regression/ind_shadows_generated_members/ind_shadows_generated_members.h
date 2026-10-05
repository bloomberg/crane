#ifndef INCLUDED_IND_SHADOWS_GENERATED_MEMBERS
#define INCLUDED_IND_SHADOWS_GENERATED_MEMBERS

#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Every generated inductive carries a variant_t alias and v / v_mut
/// accessors.  An inductive that is itself named variant_t, with
/// constructors named v_mut and v_, redeclares them, and the pattern match
/// then calls std::get_if against the constructor rather than the alias.
struct IndShadowsGeneratedMembers {
  struct variant_t0 {
    // TYPES
    struct V_mut {
      uint64_t a0;
    };

    struct V_ {
      std::shared_ptr<variant_t0> a0;
    };

    using variant_t = std::variant<V_mut, V_>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    variant_t0() {}

    explicit variant_t0(V_mut _v) : v_(std::move(_v)) {}

    explicit variant_t0(V_ _v) : v_(std::move(_v)) {}

    static variant_t0 V_mut_(uint64_t a0) { return variant_t0(V_mut{a0}); }

    static variant_t0 V_p(variant_t0 a0) {
      return variant_t0(V_{std::make_shared<variant_t0>(std::move(a0))});
    }

    // MANIPULATORS
    ~variant_t0() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<variant_t0> {
        if (auto *_alt = std::get_if<V_>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<variant_t0> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    variant_t0(const variant_t0 &) = default;
    variant_t0 &operator=(const variant_t0 &) = default;
    variant_t0(variant_t0 &&) = default;
    variant_t0 &operator=(variant_t0 &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 variant_t_rect(F0 &&f, F1 &&f0, const variant_t0 &v) {
    if (std::holds_alternative<typename variant_t0::V_mut>(v.v())) {
      const auto &[a0] = std::get<typename variant_t0::V_mut>(v.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename variant_t0::V_>(v.v());
      return f0(*a0, variant_t_rect<T1>(f, f0, *a0));
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 variant_t_rec(F0 &&f, F1 &&f0, const variant_t0 &v) {
    return variant_t_rect<T1>(f, f0, v);
  }

  static uint64_t depth(const variant_t0 &x);
  static constexpr uint64_t run = UINT64_C(4);
};

#endif // INCLUDED_IND_SHADOWS_GENERATED_MEMBERS
