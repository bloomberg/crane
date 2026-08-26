#ifndef INCLUDED_PAIR_SELF_DEEP_COPY
#define INCLUDED_PAIR_SELF_DEEP_COPY

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct PairSelfDeepCopy {
  /// Like the option case, but the recursive occurrence is hidden under
  /// prod.  The generated C++ currently represents the field as an owned
  /// std::pair containing an owned recursive value.  Clone generation then
  /// emits invalid C++ that calls .clone() on the std::pair object itself, so
  /// this test fails at C++ compile time.
  struct chain {
    // TYPES
    struct Stop {};

    struct Link {
      std::shared_ptr<std::pair<chain, bool>> a0;
    };

    using variant_t = std::variant<Stop, Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Stop _v) : v_(_v) {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain stop() { return chain(Stop{}); }

    static chain link(std::pair<chain, bool> a0) {
      return chain(
          Link{std::make_shared<std::pair<chain, bool>>(std::move(a0))});
    }

    // MANIPULATORS
    ~chain() {
      crane::small_vector<std::shared_ptr<chain>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Link>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            _stack.push_back(
                std::make_shared<chain>(std::move(((*(_alt->a0))).first)));
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

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) noexcept = default;
    chain &operator=(chain &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<chain, bool> &>
  static T1 chain_rect(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::Link>(c.v());
      return f0(*a0);
    }
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, std::pair<chain, bool> &>
  static T1 chain_rec(T1 f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::Stop>(c.v())) {
      return f;
    } else {
      const auto &[a0] = std::get<typename chain::Link>(c.v());
      return f0(*a0);
    }
  }

  static std::pair<chain, chain> dup_chain(chain c);
};

#endif // INCLUDED_PAIR_SELF_DEEP_COPY
