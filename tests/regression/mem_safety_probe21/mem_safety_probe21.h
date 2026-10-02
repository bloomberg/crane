#ifndef INCLUDED_MEM_SAFETY_PROBE21
#define INCLUDED_MEM_SAFETY_PROBE21

#include "crane_fn.h"
#include "fn.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe21 {
  /// Probe 21: Loopified recursion with constructed-value arguments.
  ///
  /// Attack vectors:
  /// 1. Recursive calls where the tree argument is a CONSTRUCTOR CALL
  /// (not the same parameter). The loopifier stores raw pointers to
  /// tree parameters. If the recursive call creates a temporary tree,
  /// the pointer to the temporary may dangle after the temporary dies.
  /// 2. Non-tail recursive calls where both the original parameter AND
  /// a constructed tree are used, requiring frame saves and moves.
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<Leaf, Node>;

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
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2 && _alt->a2.use_count() == 1) {
            _stack.push_back(std::move(_alt->a2));
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

    tree(const tree &) = default;
    tree &operator=(const tree &) = default;
    tree(tree &&) noexcept = default;
    tree &operator=(tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rect(T1 f, F1 &&f0,
                      const tree &t) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    /// _Cont_Node_1: saves [a0, a1, a2, r_], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
      T1 r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        T1 r_ = std::move(_result);
        _stack.emplace_back(
            _Cont_Node_1{std::move(a0), a1, &a2, std::move(r_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        auto r_ = std::move(_f.r_);
        T1 r_0 = std::move(_result);
        _result = f0(*a0, std::move(r_), a1, a2, std::move(r_0));
      }
    }
    return _result;
  }

  template <typename T1, typename F1>
    requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                   T1 &>
  static T1 tree_rec(T1 f, F1 &&f0,
                     const tree &t) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      const tree *t;
    };

    /// _Cont_Node: saves [a0, a1, a2], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
    };

    /// _Cont_Node_1: saves [a0, a1, a2, r_], resumes after recursive call, then
    /// processes rest.
    struct _Cont_Node_1 {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      const tree *a2;
      T1 r_;
    };

    using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _Cont_Node -> _Cont_Node_1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = f;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_Cont_Node{a0, a1, crane_raw(a2)});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_Node>(_frame)) {
        auto _f = std::move(std::get<_Cont_Node>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        T1 r_ = std::move(_result);
        _stack.emplace_back(
            _Cont_Node_1{std::move(a0), a1, &a2, std::move(r_)});
        _stack.emplace_back(_Enter{&a2});
      } else {
        auto _f = std::move(std::get<_Cont_Node_1>(_frame));
        std::shared_ptr<tree> a0 = std::move(_f.a0);
        uint64_t a1 = _f.a1;
        const tree &a2 = *_f.a2;
        auto r_ = std::move(_f.r_);
        T1 r_0 = std::move(_result);
        _result = f0(*a0, std::move(r_), a1, a2, std::move(r_0));
      }
    }
    return _result;
  }

  static uint64_t tree_sum(const tree &t);
  /// TEST 1: Tail-recursive function where the recursive call takes
  /// a constructed tree. The loopifier must store the new tree
  /// somewhere that outlives the iteration.
  static uint64_t grow_and_sum(const tree &t, uint64_t n);
  static inline const uint64_t test_grow_and_sum =
      grow_and_sum(tree::leaf(), UINT64_C(3));
  /// TEST 2: Non-tail recursive with constructed tree argument.
  /// The recursive call creates a new tree AND uses the original.
  static uint64_t double_grow(const tree &t, uint64_t n);
  static inline const uint64_t test_double_grow = double_grow(
      tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(2));
  /// TEST 3: Two recursive calls, one with original tree, one with
  /// constructed tree.
  static uint64_t branch_grow(const tree &t, uint64_t n);
  static inline const uint64_t test_branch_grow = branch_grow(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(2));
  /// TEST 4: Recursive call where the tree argument is built from
  /// MULTIPLE constructor calls with the original tree embedded.
  static uint64_t embed_grow(const tree &t, uint64_t n);
  static inline const uint64_t test_embed_grow =
      embed_grow(tree::leaf(), UINT64_C(2));
  /// TEST 5: Accumulator pattern with tree building.
  static tree accum_tree(tree acc, uint64_t n);
  static inline const uint64_t test_accum_tree =
      tree_sum(accum_tree(tree::leaf(), UINT64_C(4)));

  /// TEST 6: CPS-like pattern where the continuation builds a tree.
  static uint64_t cps_sum(
      const tree &t,
      crane::fn<uint64_t(uint64_t)>
          k) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      crane::fn<uint64_t(uint64_t)> k;
      const tree *t;
    };

    using _Frame = std::variant<_Enter>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{std::move(k), &t});
    /// Loopified cps_sum: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      crane::fn<uint64_t(uint64_t)> k = std::move(_f.k);
      const tree &t = *_f.t;
      if (std::holds_alternative<typename tree::Leaf>(t.v())) {
        _result = k(UINT64_C(0));
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        _stack.emplace_back(_Enter{[=](uint64_t lsum) {
                                     return cps_sum(
                                         a2_value, [=](uint64_t rsum) {
                                           return k(((lsum + a1) + rsum));
                                         });
                                   },
                                   crane_raw(a0)});
      }
    }
    return _result;
  }

  static inline const uint64_t test_cps_sum =
      cps_sum(tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                         UINT64_C(2),
                         tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
              [](uint64_t n) { return n; });
  /// TEST 7: Mutually-referencing recursive call with tree
  /// construction at each level.
  static uint64_t weave(const tree &t1, const tree &t2, uint64_t n);
  static inline const uint64_t test_weave =
      weave(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
            tree::node(tree::leaf(), UINT64_C(2), tree::leaf()), UINT64_C(2));
  /// TEST 8: Deep nesting with tree_sum at each level before recursion.
  static uint64_t sum_and_grow(const tree &t, uint64_t n);
  static inline const uint64_t test_sum_and_grow = sum_and_grow(
      tree::node(tree::leaf(), UINT64_C(1), tree::leaf()), UINT64_C(3));
};

#endif // INCLUDED_MEM_SAFETY_PROBE21
