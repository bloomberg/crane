#ifndef INCLUDED_PAIR_BOTH_RECURSIVE
#define INCLUDED_PAIR_BOTH_RECURSIVE

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct PairBothRecursive {
  struct t {
    // TYPES
    struct Leaf {
      uint64_t a0;
    };

    struct Br {
      std::shared_ptr<std::pair<t, t>> a0;
    };

    using variant_t = std::variant<Leaf, Br>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Leaf _v) : v_(std::move(_v)) {}

    explicit t(Br _v) : v_(std::move(_v)) {}

    static t leaf(uint64_t a0) { return t(Leaf{a0}); }

    static t br(std::pair<t, t> a0) {
      return t(Br{std::make_shared<std::pair<t, t>>(std::move(a0))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Br>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(
                std::make_shared<t>(std::move(((*(_alt->a0))).first)));
            _stack.push_back(
                std::make_shared<t>(std::move(((*(_alt->a0))).second)));
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

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, std::pair<t, t> &>
  static T1 t_rect(F0 &&f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename t::Leaf>(t0.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename t::Br>(t0.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, std::pair<t, t> &>
  static T1 t_rec(F0 &&f, F1 &&f0, const t &t0) {
    if (std::holds_alternative<typename t::Leaf>(t0.v())) {
      const auto &[a0] = std::get<typename t::Leaf>(t0.v());
      return f(a0);
    } else {
      const auto &[a0] = std::get<typename t::Br>(t0.v());
      return f0(*a0);
    }
  }

  static t wrap(t acc);
  static inline const t empty = t::leaf(UINT64_C(1));
  static uint64_t size(const t &x);
};

#endif // INCLUDED_PAIR_BOTH_RECURSIVE
