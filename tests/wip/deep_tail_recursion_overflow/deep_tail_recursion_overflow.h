#ifndef INCLUDED_DEEP_TAIL_RECURSION_OVERFLOW
#define INCLUDED_DEEP_TAIL_RECURSION_OVERFLOW

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct DeepTailRecursionOverflow {
  /// A plainly tail-recursive builder over a deep value-type inductive still
  /// recurses in the generated C++ (and so does the resulting move-constructor
  /// chain) unless Set Crane Loopify is in effect.
  struct chain {
    // TYPES
    struct End_ {
      uint64_t a0;
    };

    struct Link {
      std::shared_ptr<chain> a0;
      uint64_t a1;
    };

    using variant_t = std::variant<End_, Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(End_ _v) : v_(std::move(_v)) {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain end_(uint64_t a0) { return chain(End_{a0}); }

    static chain link(chain a0, uint64_t a1) {
      return chain(Link{std::make_shared<chain>(std::move(a0)), a1});
    }

    // MANIPULATORS
    ~chain() {
      crane::small_vector<std::shared_ptr<chain>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Link>(&_v)) {
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

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) noexcept = default;
    chain &operator=(chain &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, chain &, T1 &, uint64_t &>
  static T1 chain_rect(F0 &&f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::End_>(c.v())) {
      const auto &[a0] = std::get<typename chain::End_>(c.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
      return f0(*a0, chain_rect<T1>(f, f0, *a0), a1);
    }
  }

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
             std::is_invocable_r_v<T1, F1 &, chain &, T1 &, uint64_t &>
  static T1 chain_rec(F0 &&f, F1 &&f0, const chain &c) {
    if (std::holds_alternative<typename chain::End_>(c.v())) {
      const auto &[a0] = std::get<typename chain::End_>(c.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
      return f0(*a0, chain_rec<T1>(f, f0, *a0), a1);
    }
  }

  static chain build(uint64_t n, chain acc);
  static uint64_t total_of(const chain &c);
  static inline const uint64_t deep =
      total_of(build(UINT64_C(3000000), chain::end_(UINT64_C(0))));
};

#endif // INCLUDED_DEEP_TAIL_RECURSION_OVERFLOW
