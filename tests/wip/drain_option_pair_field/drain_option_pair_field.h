#ifndef INCLUDED_DRAIN_OPTION_PAIR_FIELD
#define INCLUDED_DRAIN_OPTION_PAIR_FIELD

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

/// The iterative destructor walks a recursive field to avoid deep recursion.
/// For a field of type option (t * nat) the walk reads the pair component as
/// a0->first, applying operator-> to the std::optional rather than
/// opening it first.  A bare option t and a bare t * t both work, so it is
/// the nesting the drain path does not handle.
struct DrainOptionPairField {
  struct t {
    // TYPES
    struct C {
      std::shared_ptr<std::optional<std::pair<t, uint64_t>>> a0;
    };

    using variant_t = std::variant<C>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(C _v) : v_(std::move(_v)) {}

    static t c(std::optional<std::pair<t, uint64_t>> a0) {
      return t(C{std::make_shared<std::optional<std::pair<t, uint64_t>>>(
          std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<C>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if ((*_alt->a0).has_value()) {
              _stack.push_back(
                  std::make_shared<t>(std::move(*_alt->a0->first)));
            }
            _alt->a0.reset();
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

    t(const t &) = default;
    t &operator=(const t &) = default;
    t(t &&) noexcept = default;
    t &operator=(t &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &,
                                   std::optional<std::pair<t, uint64_t>> &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0] = std::get<typename t::C>(t0.v());
    return f(*a0);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &,
                                   std::optional<std::pair<t, uint64_t>> &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0] = std::get<typename t::C>(t0.v());
    return f(*a0);
  }

  static uint64_t depth(const t &x);
  static inline const uint64_t test =
      depth(t::c(std::make_optional<std::pair<t, uint64_t>>(std::make_pair(
          t::c(std::optional<std::pair<t, uint64_t>>()), UINT64_C(1)))));
};

#endif // INCLUDED_DRAIN_OPTION_PAIR_FIELD
