#ifndef INCLUDED_NESTED_TREE_PAIR_LITERAL
#define INCLUDED_NESTED_TREE_PAIR_LITERAL

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

/// A non-uniform (nested) inductive
/// (tree A := Lf : A -> tree A | Nd : tree (A * A) -> tree A) has its type
/// parameter erased, so a literal value built at tree nat passes a
/// std::pair through the erased constructor.
struct NestedTreePairLiteral {
  struct tree {
    // TYPES
    struct Lf {
      crane::obj a0;
    };

    struct Nd {
      std::shared_ptr<tree> a0;
    };

    using variant_t = std::variant<Lf, Nd>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Lf _v) : v_(std::move(_v)) {}

    explicit tree(Nd _v) : v_(std::move(_v)) {}

    static tree lf(crane::obj a0) { return tree(Lf{std::move(a0)}); }

    static tree nd(tree a0) {
      return tree(Nd{std::make_shared<tree>(std::move(a0))});
    }

    // MANIPULATORS
    ~tree() {
      auto _next = [&](variant_t &_v) -> std::shared_ptr<tree> {
        if (auto *_alt = std::get_if<Nd>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            return std::move(_alt->a0);
          }
        }
        return nullptr;
      };
      std::shared_ptr<tree> _cur = _next(v_mut());
      while (_cur) {
        _cur = _next(_cur->v_mut());
      }
    }

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const crane::obj &>
  static T1 tree_rect(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Lf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Lf>(t.v());
      return crane_any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename tree::Nd>(t.v());
      return crane_any_cast<T1>(f0(*a0, tree_rect<T1>(f, f0, *a0)));
    }
  }

  template <typename T1, typename T2 = void, typename F0, typename F1>
    requires std::is_invocable_r_v<T1, F0 &, const crane::obj &>
  static T1 tree_rec(F0 &&f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Lf>(t.v())) {
      const auto &[a0] = std::get<typename tree::Lf>(t.v());
      return crane_any_cast<T1>(f(a0));
    } else {
      const auto &[a0] = std::get<typename tree::Nd>(t.v());
      return crane_any_cast<T1>(f0(*a0, tree_rec<T1>(f, f0, *a0)));
    }
  }

  template <typename T1 = void> static uint64_t size(const tree &t) {
    if (std::holds_alternative<typename tree::Lf>(t.v())) {
      return UINT64_C(1);
    } else {
      const auto &[a0] = std::get<typename tree::Nd>(t.v());
      return (UINT64_C(2) * size<crane::obj>(*a0));
    }
  }

  static inline const tree sample = tree::nd(tree::nd(
      tree::lf(std::make_pair(std::make_pair(UINT64_C(1), UINT64_C(2)),
                              std::make_pair(UINT64_C(3), UINT64_C(4))))));

  static inline const uint64_t go = size<uint64_t>(sample);
};

#endif // INCLUDED_NESTED_TREE_PAIR_LITERAL
