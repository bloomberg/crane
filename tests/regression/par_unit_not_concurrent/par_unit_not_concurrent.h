#ifndef INCLUDED_PAR_UNIT_NOT_CONCURRENT
#define INCLUDED_PAR_UNIT_NOT_CONCURRENT

#include "crane_fn.h"
#include "crane_variant.h"
#include "shared_block.h"
#include "shared_variant.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <future>
#include <optional>
#include <utility>
static_assert(crane::rc_is_atomic,
              "this unit spawns threads, but a header included before it chose "
              "CRANE_NON_ATOMIC_RC");

struct ParUnitNotConcurrent {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      crane::shared_box<tree> a2;
    };

    using variant_t = crane::shared_variant<Leaf, Node>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(Leaf _v) : v_(_v) {}

    explicit tree(Node _v) : v_(std::move(_v)) {}

    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{crane::shared_box<tree>::make(std::move(a0)), a1,
                       crane::shared_box<tree>::make(std::move(a2))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// CraneEnter: captures varying
                                       /// parameters for each recursive call.

    struct CraneEnter {
      const tree *t;
    };

    /// CraneCont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_Node {
      crane::shared_box<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    /// CraneCont_Node_1: saves [_tmp2, a0, a1, a2], resumes after recursive
    /// call, then processes rest.
    struct CraneCont_Node_1 {
      T1 _tmp2;
      crane::shared_box<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_Node, CraneCont_Node_1>;
    T1 _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{&t});
    /// Loopified tree_rect: CraneEnter -> CraneCont_Node -> CraneCont_Node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (crane::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(crane::get<CraneEnter>(_frame));
        const tree &t = *_f.t;
        if (crane::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = crane::get<typename tree::Node>(t.v());
          _stack.emplace_back(CraneCont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (crane::holds_alternative<CraneCont_Node>(_frame)) {
        auto _f = std::move(crane::get<CraneCont_Node>(_frame));
        crane::shared_box<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _stack.emplace_back(
            CraneCont_Node_1{std::move(_result), std::move(a0), a1, &a2});
        _stack.emplace_back(CraneEnter{&a2});
      } else {
        auto _f = std::move(crane::get<CraneCont_Node_1>(_frame));
        crane::shared_box<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
  static T1 tree_rec(T1 f, F1 &&f0, const tree &t) {
    return tree_rect<T1>(std::move(f), f0, t);
  }

  static uint64_t sum(const tree &t);
  static tree mk(uint64_t n);
  static tree mirror(const tree &t);
  static uint64_t churn(uint64_t k, const tree &t);
  static inline const tree shared = mk(UINT64_C(2000));
  static uint64_t work(uint64_t k);
  static uint64_t race(uint64_t k);
};

#endif // INCLUDED_PAR_UNIT_NOT_CONCURRENT
