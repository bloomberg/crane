#ifndef INCLUDED_IND_SHADOWS_GENERATED_MEMBERS
#define INCLUDED_IND_SHADOWS_GENERATED_MEMBERS

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// Every generated inductive carries a variant_t alias and v / v_mut
/// accessors.  An inductive that is itself named variant_t, with
/// constructors named v_mut and v_, redeclares them, and the pattern match
/// then calls std::get_if against the constructor rather than the alias.
struct IndShadowsGeneratedMembers {
  struct variant_t {
    // TYPES
    struct V_mut {
      uint64_t a0;
    };

    struct V_ {
      std::shared_ptr<variant_t> a0;
    };

    using variant_t_ = std::variant<V_mut, V_>;

  private:
    // DATA
    variant_t_ v_;

  public:
    // CREATORS
    variant_t() {}

    explicit variant_t(V_mut _v) : v_(std::move(_v)) {}

    explicit variant_t(V_ _v) : v_(std::move(_v)) {}

    static variant_t V_mut_(uint64_t a0) { return variant_t(V_mut{a0}); }

    static variant_t V__(variant_t a0) {
      return variant_t(V_{std::make_shared<variant_t>(std::move(a0))});
    }

    // MANIPULATORS
    ~variant_t() {
      crane::small_vector<std::shared_ptr<variant_t>> _stack = {};
      auto _drain = [&](variant_t_ &_v) {
        if (auto *_alt = std::get_if<V_>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
        }
      };
      _drain(v_mut());
      while (!_stack.empty()) {
        auto _cur = std::move(_stack.back());
        _stack.pop_back();
        if (_cur.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          _drain(_cur->v_mut());
        }
      }
    }

    variant_t(const variant_t &) = default;
    variant_t &operator=(const variant_t &) = default;
    variant_t(variant_t &&) noexcept = default;
    variant_t &operator=(variant_t &&) noexcept = default;

    inline variant_t_ &v_mut() { return v_; }

    // ACCESSORS
    const variant_t_ &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, variant_t &, T1 &>
  static T1 variant_t_rect(F0 &&f, F1 &&f0, const variant_t &v) {
    if (std::holds_alternative<typename variant_t::V_mut>(v.v())) {
      const auto &[a0] = std::get<typename variant_t::V_mut>(v.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename variant_t::V_>(v.v());
      return f0(*a0, variant_t_rect<T1>(f, f0, *a0));
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, variant_t &, T1 &>
  static T1 variant_t_rec(F0 &&f, F1 &&f0, const variant_t &v) {
    if (std::holds_alternative<typename variant_t::V_mut>(v.v())) {
      const auto &[a0] = std::get<typename variant_t::V_mut>(v.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename variant_t::V_>(v.v());
      return f0(*a0, variant_t_rec<T1>(f, f0, *a0));
    }
  }

  static uint64_t depth(const variant_t &x);
  static inline const uint64_t run =
      depth(variant_t::V__(variant_t::V__(variant_t::V_mut_(UINT64_C(2)))));
};

#endif // INCLUDED_IND_SHADOWS_GENERATED_MEMBERS
