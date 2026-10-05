#ifndef INCLUDED_NON_UNIFORM_PAIR_NEST
#define INCLUDED_NON_UNIFORM_PAIR_NEST

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct NonUniformPairNest {
  struct nest {
    // TYPES
    struct NZ {
      crane::obj a0;
    };

    struct NS {
      std::shared_ptr<nest> a0;
    };

    using variant_t = std::variant<NZ, NS>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    nest() {}

    explicit nest(NZ _v) : v_(std::move(_v)) {}

    explicit nest(NS _v) : v_(std::move(_v)) {}

    static nest nz(crane::obj a0) { return nest(NZ{std::move(a0)}); }

    static nest ns(nest a0) {
      return nest(NS{std::make_shared<nest>(std::move(a0))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const crane::obj &>
  static T1 nest_rect(F0 &&f, F1 &&f0, const nest &n) {
    if (std::holds_alternative<typename nest::NZ>(n.v())) {
      const auto &[a0] = std::get<typename nest::NZ>(n.v());
      return crane_any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename nest::NS>(n.v());
      return crane_any_cast<T1>(
          f0(*a0, nest_rect(crane_erase_fn<T1>(f), f0, *a0)));
    }
  }

  template <typename T1, typename T2 = void, typename F0, typename F1>
  static T1 nest_rec(F0 &&f, F1 &&f0, const nest &n) {
    return nest_rect<T1, crane::obj>(crane_erase_fn<T1>(f), f0, n);
  }

  template <typename T1 = void> static uint64_t size(const nest &n) {
    if (std::holds_alternative<typename nest::NZ>(n.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a0] = std::get<typename nest::NS>(n.v());
      return (UINT64_C(2) * size<crane::obj>(*a0));
    }
  }

  static constexpr uint64_t go = UINT64_C(2);
};

#endif // INCLUDED_NON_UNIFORM_PAIR_NEST
