#ifndef INCLUDED_DOUBLE_OPTION_NEST
#define INCLUDED_DOUBLE_OPTION_NEST

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct DoubleOptionNest {
  struct t {
    // TYPES
    struct Node {
      uint64_t a0;
      std::shared_ptr<std::optional<std::optional<t>>> a1;
    };

    using variant_t = std::variant<Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    t() {}

    explicit t(Node _v) : v_(std::move(_v)) {}

    static t node(uint64_t a0, std::optional<std::optional<t>> a1) {
      return t(Node{a0, std::make_shared<std::optional<std::optional<t>>>(
                            std::move(a1))});
    }

    // MANIPULATORS
    ~t() {
      crane::small_vector<std::shared_ptr<t>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if ((*_alt->a1).has_value()) {
              if ((*(*_alt->a1)).has_value()) {
                _stack.push_back(
                    std::make_shared<t>(std::move(*(*(*_alt->a1)))));
              }
            }
            _alt->a1.reset();
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
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &,
                                   std::optional<std::optional<t>> &>
  static T1 t_rect(F0 &&f, const t &t0) {
    const auto &[a0, a1] = std::get<typename t::Node>(t0.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &,
                                   std::optional<std::optional<t>> &>
  static T1 t_rec(F0 &&f, const t &t0) {
    const auto &[a0, a1] = std::get<typename t::Node>(t0.v());
    return f(a0, *a1);
  }

  static t wrap(uint64_t k, t acc);
  static inline const t empty =
      t::node(UINT64_C(0), std::optional<std::optional<t>>());

  static uint64_t peek(const t &x);
};

#endif // INCLUDED_DOUBLE_OPTION_NEST
