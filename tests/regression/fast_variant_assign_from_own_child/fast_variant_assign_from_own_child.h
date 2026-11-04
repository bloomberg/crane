#ifndef INCLUDED_FAST_VARIANT_ASSIGN_FROM_OWN_CHILD
#define INCLUDED_FAST_VARIANT_ASSIGN_FROM_OWN_CHILD

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#define CRANE_NON_ATOMIC_RC 1
#include "crane_variant.h"
#include "rc.h"

struct FastVariantAssignFromOwnChild {
  struct chain {
    // TYPES
    struct Last {
      uint64_t a0;
    };

    struct Link {
      uint64_t a0;
      crane::rc<chain> a1;
    };

    using variant_t = crane::variant<Last, Link>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    chain() {}

    explicit chain(Last _v) : v_(std::move(_v)) {}

    explicit chain(Link _v) : v_(std::move(_v)) {}

    static chain last(uint64_t a0) { return chain(Last{a0}); }

    static chain link(uint64_t a0, crane::child_slot<chain> a1) {
      return chain(Link{a0, a1.take()});
    }

    // MANIPULATORS
    ~chain() {
      auto _next = [&](variant_t &_v) -> crane::rc<chain> {
        if (auto *_alt = crane::get_if<Link>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            return std::move(_alt->a1);
          }
        }
        return nullptr;
      };
      crane::rc<chain> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    chain(const chain &) = default;
    chain &operator=(const chain &) = default;
    chain(chain &&) = default;
    chain &operator=(chain &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
  static T1 chain_rect(F0 &&f, F1 &&f0, const chain &c) {
    if (crane::holds_alternative<typename chain::Last>(c.v())) {
      const auto &[a0] = crane::get<typename chain::Last>(c.v());
      return f(a0);
    } else {
      const auto &[a0, a1] = crane::get<typename chain::Link>(c.v());
      return f0(a0, *a1, chain_rect<T1>(f, f0, *a1));
    }
  }

  template <typename T1, typename F0, typename F1>
  static T1 chain_rec(F0 &&f, F1 &&f0, const chain &c) {
    return chain_rect<T1>(f, f0, c);
  }

  static uint64_t total(const chain &c);
};

#endif // INCLUDED_FAST_VARIANT_ASSIGN_FROM_OWN_CHILD
