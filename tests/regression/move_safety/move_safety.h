#ifndef INCLUDED_MOVE_SAFETY
#define INCLUDED_MOVE_SAFETY

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MoveSafety {
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
          _dst->v_ = Node{_alt.a0 ? std::make_shared<tree>() : nullptr, _alt.a1,
                          _alt.a2 ? std::make_shared<tree>() : nullptr};
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
      return tree(Node{std::make_shared<tree>(std::move(a0)), a1,
                       std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      std::vector<std::shared_ptr<tree>> _stack{};
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

    /// TEST 4: Partial application followed by identity function
    /// that takes by value (returns its argument).
    tree tree_id() const { return std::move(*this); }

    /// A function that stores its tree argument inside a constructor.
    /// This causes the parameter to be passed by value (it "escapes").
    tree wrap_tree() const {
      return tree::node(std::move(*this), UINT64_C(0), tree::leaf());
    }

    uint64_t sum_values(uint64_t x) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return x;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return (a1 + x);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (a10 + x);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return (((a10 + a11) + a1) + x);
          }
        }
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rec(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        tree a2;
        uint64_t a1;
        tree a0;
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, std::move(_result), _f.a1, _f.a2,
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, uint64_t &, tree &,
                                     T1 &>
    T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a2, a1, a0], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        tree a2;
        uint64_t a1;
        tree a0;
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
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), *a2, a1, *a0});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, std::move(_result), _f.a1, _f.a2,
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };

  /// A wrapper for closures.
  struct fn_box {
    // DATA
    std::function<uint64_t(uint64_t)> a0;

    // ACCESSORS
    fn_box clone() const { return {a0}; }

    // CREATORS
    static fn_box box(std::function<uint64_t(uint64_t)> a0) {
      return {std::move(a0)};
    }

    uint64_t apply_box(uint64_t x) const {
      const auto &[a0] = *this;
      return a0(x);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 fn_box_rec(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &,
                                     std::function<uint64_t(uint64_t)> &>
    T1 fn_box_rect(F0 &&f) const {
      const auto &[a0] = *this;
      return f(a0);
    }
  };

  /// TEST 1: Partial application + function taking by value.
  /// The & lambda from partial application captures t by reference.
  /// Then wrap_tree takes t by value, so std::move(t) is generated.
  /// The lambda then holds a dangling reference.
  static inline const uint64_t bug_partial_then_wrap = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    return std::move(t).sum_values(UINT64_C(99));
  }();
  /// TEST 2: Store partial application in a Box.
  /// If the eta-expanded lambda uses & capture,
  /// the Box will hold a dangling reference after the
  /// function returns.
  static fn_box make_box(tree t);
  static inline const uint64_t bug_box_escape = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    fn_box b = make_box(std::move(t));
    return std::move(b).apply_box(UINT64_C(99));
  }();
  /// TEST 3: Two partial applications of same variable.
  /// Second one should not move t.
  static inline const uint64_t bug_double_partial = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); };
      std::function<uint64_t(uint64_t)> g = [&](uint64_t _x0) -> uint64_t {
        return std::move(t).sum_values(_x0);
      };
      return (f(UINT64_C(1)) + g(UINT64_C(2)));
    }();
  }();
  static inline const uint64_t bug_partial_then_id = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                          UINT64_C(20),
                          tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
      std::function<uint64_t(uint64_t)> f =
          [=](uint64_t _x0) mutable -> uint64_t { return t.sum_values(_x0); };
      tree t2 = std::move(t).tree_id();
      if (std::holds_alternative<typename tree::Leaf>(t2.v_mut())) {
        return f(UINT64_C(0));
      } else {
        auto &[a0, a1, a2] = std::get<typename tree::Node>(t2.v_mut());
        return f(std::move(a1));
      }
    }();
  }();
};

#endif // INCLUDED_MOVE_SAFETY
