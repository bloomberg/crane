#ifndef INCLUDED_PARTIAL_APP_MOVE
#define INCLUDED_PARTIAL_APP_MOVE

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct PartialAppMove {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      uint64_t a1;
      std::unique_ptr<tree> a2;
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

    tree(const tree &_other) : v_(std::move(_other.clone().v_)) {}

    tree(tree &&_other) noexcept : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    tree clone() const {
      tree _out{};

      struct _CloneFrame {
        const tree *_src;
        tree *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const tree *_src = _frame._src;
        tree *_dst = _frame._dst;
        if (std::holds_alternative<Leaf>(_src->v())) {
          _dst->v_ = Leaf{};
        } else {
          const auto &_alt = std::get<Node>(_src->v());
          _dst->v_ = Node{_alt.a0 ? std::make_unique<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_unique<tree>() : nullptr};
          auto &_dst_alt = std::get<Node>(_dst->v_);
          if (_alt.a0) {
            _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
          }
          if (_alt.a2) {
            _stack.push_back({_alt.a2.get(), _dst_alt.a2.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    static tree leaf() { return tree(Leaf{}); }

    static tree node(tree a0, uint64_t a1, tree a2) {
      return tree(Node{std::make_unique<tree>(std::move(a0)), a1,
                       std::make_unique<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::unique_ptr<tree>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](tree &_node) {
        if (std::holds_alternative<Node>(_node.v_)) {
          auto &_alt = std::get<Node>(_node.v_);
          if (_alt.a0) {
            _stack.push_back(std::move(_alt.a0));
          }
          if (_alt.a2) {
            _stack.push_back(std::move(_alt.a2));
          }
        }
      };
      _drain(*this);
      while (!_stack.empty()) {
        auto _node = std::move(_stack.back());
        _stack.pop_back();
        if (_node) {
          _drain(*_node);
        }
      }
    }

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

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      T1 _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                          std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
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

    /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive call.
    struct _After_Node {
      const tree *a0_0;
      tree a2;
      uint64_t a1;
      tree a0_1;
    };

    /// _Combine_Node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_Node {
      T1 _result;
      tree a2;
      uint64_t a1;
      tree a0;
    };

    using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
    T1 _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{&t});
    /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree &t = *_f.t;
        if (std::holds_alternative<typename tree::Leaf>(t.v())) {
          _result = std::move(f);
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
          _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
          _stack.emplace_back(_Enter{a2.get()});
        }
      } else if (std::holds_alternative<_After_Node>(_frame)) {
        auto _f = std::move(std::get<_After_Node>(_frame));
        _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                          std::move(_f.a0_1)});
        _stack.emplace_back(_Enter{_f.a0_0});
      } else {
        auto _f = std::move(std::get<_Combine_Node>(_frame));
        _result =
            f0(_f.a0, std::move(_result), _f.a1, _f.a2, std::move(_f._result));
      }
    }
    return _result;
  }

  /// A function taking two args: tree -> nat -> nat.
  /// Partial application of this to a tree creates a
  /// closure nat -> nat in C++ via & lambda.
  static uint64_t sum_values(const tree &t, uint64_t x);
  /// Wrap a tree inside another Node.
  /// In C++, this calls tree::node() which has rvalue ref overloads.
  /// If escape analysis adds std::move(t) here, the move is REAL.
  static tree wrap(tree t);
  /// BUG TRIGGER: partial application creates a & lambda capturing t,
  /// then t is passed to a constructor (actually moved via rvalue ref),
  /// then the lambda accesses the moved-from t.
  static uint64_t trigger_bug(tree t);
  /// Build a tree and trigger the bug.
  static inline const uint64_t run_bug = trigger_bug(tree::node(
      tree::node(tree::leaf(), UINT64_C(10), tree::leaf()), UINT64_C(20),
      tree::node(tree::leaf(), UINT64_C(30), tree::leaf())));
  /// Inline version: t is a local variable, not a function parameter.
  /// This is where move optimization might actually move t.
  static inline const uint64_t inline_bug = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return sum_values(t, _x0); };
      tree w = tree::node(std::move(t), UINT64_C(42), tree::leaf());
      if (std::holds_alternative<typename tree::Leaf>(w.v_mut())) {
        return f(UINT64_C(0));
      } else {
        return f(UINT64_C(99));
      }
    }();
  }();
  /// Same but using wrap function.
  static inline const uint64_t inline_bug2 = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return sum_values(t, _x0); };
      tree w = wrap(std::move(t));
      if (std::holds_alternative<typename tree::Leaf>(w.v_mut())) {
        return f(UINT64_C(0));
      } else {
        return f(UINT64_C(99));
      }
    }();
  }();
};

#endif // INCLUDED_PARTIAL_APP_MOVE
