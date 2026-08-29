#ifndef INCLUDED_OPTION_NESTED_RECURSION_BAD_CPP
#define INCLUDED_OPTION_NESTED_RECURSION_BAD_CPP

#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

struct OptionNestedRecursionBadCpp {
  struct chain {
    // TYPES
    struct Link {
      uint64_t a0;
      std::shared_ptr<std::optional<chain>> a1;
    };

    using variant_t = std::variant<Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain link(uint64_t a0, std::optional<chain> a1) {
      return chain(
          Link{a0, std::make_shared<std::optional<chain>>(std::move(a1))});
    }

    // MANIPULATORS
    ~chain() {
      crane::small_vector<std::shared_ptr<chain>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Link>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            if (((*(_alt->a1))).has_value()) {
              _stack.push_back(
                  std::make_shared<chain>(std::move((*((*(_alt->a1)))))));
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

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) noexcept = default;
    chain &operator=(chain &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<chain> &>
  static T1 chain_rect(F0 &&f, const chain &c) {
    const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
    return f(a0, *a1);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, uint64_t &, std::optional<chain> &>
  static T1 chain_rec(F0 &&f, const chain &c) {
    const auto &[a0, a1] = std::get<typename chain::Link>(c.v());
    return f(a0, *a1);
  }

  static chain build(uint64_t n);
  static uint64_t depth(const chain &c);
  static uint64_t run(uint64_t n);
};

#endif // INCLUDED_OPTION_NESTED_RECURSION_BAD_CPP
