#ifndef INCLUDED_MEM_SAFETY_PROBE14
#define INCLUDED_MEM_SAFETY_PROBE14

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe14 {
  /// Probe 14: Stress-test closure capture safety.
  ///
  /// Focus on patterns where:
  /// 1. A value type is simultaneously used in a closure AND
  /// consumed by another operation in the same expression
  /// 2. Closures that capture value types are stored in
  /// data structures and later invoked
  /// 3. Closures returned from helper functions that take
  /// value-type parameters by value (move semantics)
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::unique_ptr<tree> a0;
      unsigned int a1;
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

    static tree node(tree a0, unsigned int a1, tree a2) {
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

    /// TEST 7: Closure stored in PAIR, then extracted and called.
    /// Tests pair construction + closure capture interaction.
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
    fn_and_val() const {
      unsigned int s = (*this).tree_sum();
      return std::make_pair([=](unsigned int n) mutable { return (s + n); }, s);
    }

    /// TEST 4: Two closures capture same tree. Both should
    /// have independent copies.
    unsigned int two_closures() const {
      tree _self_val = *this;
      std::function<unsigned int(unsigned int)> f1 =
          [=](unsigned int n) mutable { return (_self_val.tree_sum() + n); };
      std::function<unsigned int(unsigned int)> f2 =
          [=](unsigned int n) mutable { return (_self_val.tree_sum() * n); };
      return (f1(3u) + f2(2u));
    }

    unsigned int closure_then_consume() const {
      tree _self_val = *this;
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int n) mutable { return (_self_val.tree_sum() + n); };
      unsigned int v = std::move(*this).consume_tree();
      return (f(0u) + v);
    }

    /// TEST 3: Tree used in closure, then tree passed to
    /// function that consumes it. The closure must not
    /// share state with the consumed tree.
    unsigned int consume_tree() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return 0u;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return a1;
      }
    }

    /// TEST 2: Tree used in closure AND in a let-binding.
    /// The let-binding forces evaluation before the closure call.
    /// Tests evaluation order safety.
    unsigned int use_tree_twice() const {
      tree _self_val = *this;
      unsigned int ts = (*this).tree_sum();
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int n) mutable { return (_self_val.tree_sum() + n); };
      return (ts + f(0u));
    }

    /// TEST 1: make_adder takes a tree by value (move).
    /// The closure captures tree_sum t. After the closure is created,
    /// t is dead in the caller, so Crane might move t.
    /// But the closure must hold a valid copy.
    unsigned int make_adder(unsigned int n) const {
      return ((*this).tree_sum() + n);
    }

    unsigned int tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        unsigned int _result;
        unsigned int a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_sum: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), a1});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{_result, _f.a1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((_result + _f.a1) + _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
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
        unsigned int a1;
        tree a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree a2;
        unsigned int a1;
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
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree &, T1 &, unsigned int &,
                                     tree &, T1 &>
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
        unsigned int a1;
        tree a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        T1 _result;
        tree a2;
        unsigned int a1;
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
          _stack.emplace_back(_Combine_Node{_result, std::move(_f.a2), _f.a1,
                                            std::move(_f.a0)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(_f.a0, _result, _f.a1, _f.a2, _f._result);
        }
      }
      return _result;
    }
  };

  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::unique_ptr<mylist<A>> a1;
    };

    using variant_t = std::variant<Mynil, Mycons>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    mylist() {}

    explicit mylist(Mynil _v) : v_(_v) {}

    explicit mylist(Mycons _v) : v_(std::move(_v)) {}

    mylist(const mylist<A> &_other) : v_(std::move(_other.clone().v_)) {}

    mylist(mylist<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

    mylist<A> &operator=(const mylist<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    mylist<A> &operator=(mylist<A> &&_other) noexcept {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    mylist<A> clone() const {
      mylist<A> _out{};

      struct _CloneFrame {
        const mylist<A> *_src;
        mylist<A> *_dst;
      };

      std::vector<_CloneFrame> _stack{};
      _stack.reserve(8);
      _stack.push_back({this, &_out});
      while (!_stack.empty()) {
        auto _frame = _stack.back();
        _stack.pop_back();
        const mylist<A> *_src = _frame._src;
        mylist<A> *_dst = _frame._dst;
        if (std::holds_alternative<Mynil>(_src->v())) {
          _dst->v_ = Mynil{};
        } else {
          const auto &_alt = std::get<Mycons>(_src->v());
          _dst->v_ = Mycons{_alt.a0,
                            _alt.a1 ? std::make_unique<mylist<A>>() : nullptr};
          auto &_dst_alt = std::get<Mycons>(_dst->v_);
          if (_alt.a1) {
            _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
          }
        }
      }
      return _out;
    }

    // CREATORS
    template <typename _U> explicit mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ =
            Mycons{A(a0), a1 ? std::make_unique<mylist<A>>(*a1) : nullptr};
      }
    }

    static mylist<A> mynil() { return mylist(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist(
          Mycons{std::move(a0), std::make_unique<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      std::vector<std::unique_ptr<mylist<A>>> _stack{};
      _stack.reserve(8);
      auto _drain = [&](mylist<A> &_node) {
        if (std::holds_alternative<Mycons>(_node.v_)) {
          auto &_alt = std::get<Mycons>(_node.v_);
          if (_alt.a1) {
            _stack.push_back(std::move(_alt.a1));
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

    /// TEST 6: List of closures created from tree traversal.
    /// Each closure captures a value from its level. Closures
    /// are evaluated after the full traversal completes.
    mylist<A> mylist_append(mylist<A> l2) const {
      std::unique_ptr<mylist<A>> _head{};
      std::unique_ptr<mylist<A>> *_write = &_head;
      const mylist *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          *_write = std::make_unique<mylist<A>>(std::move(_loop_l2));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = std::make_unique<mylist<A>>(
              typename mylist<A>::Mycons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename mylist<A>::Mycons>((*_write)->v_mut()).a1;
          _loop_self = a1.get();
          continue;
        }
      }
      return std::move(*_head);
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<A> a1;
        A a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [f0, a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        F1 f0;
        mylist<A> a1;
        A a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = std::move(f);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{f0, *a1, a0});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = _f.f0(_f.a0, _f.a1, _result);
        }
      }
      return _result;
    }
  };

  static unsigned int
  sum_fns(const mylist<std::function<unsigned int(unsigned int)>> &l);
  static inline const unsigned int use_make_adder = []() {
    tree t = tree::node(tree::node(tree::leaf(), 10u, tree::leaf()), 20u,
                        tree::node(tree::leaf(), 30u, tree::leaf()));
    return std::move(t).make_adder(5u);
  }();
  static inline const unsigned int test_use_twice =
      tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                 tree::node(tree::leaf(), 15u, tree::leaf()))
          .use_tree_twice();
  static inline const unsigned int test_closure_consume =
      tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                 tree::node(tree::leaf(), 15u, tree::leaf()))
          .closure_then_consume();
  static inline const unsigned int test_two_closures =
      tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                 tree::node(tree::leaf(), 15u, tree::leaf()))
          .two_closures();
  /// TEST 5: Closure captures tree, tree is pattern-matched
  /// AFTER closure creation. The match destructures the tree.
  /// The closure must still hold the original tree.
  static unsigned int capture_then_match(tree t);
  static inline const unsigned int test_capture_match = capture_then_match(
      tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                 tree::node(tree::leaf(), 15u, tree::leaf())));
  static mylist<std::function<unsigned int(unsigned int)>>
  tree_level_fns(const tree &t, unsigned int depth);
  static inline const unsigned int test_level_fns = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    return sum_fns(tree_level_fns(std::move(t), 0u));
  }();
  static inline const unsigned int test_fn_and_val = []() {
    tree t = tree::node(tree::node(tree::leaf(), 100u, tree::leaf()), 200u,
                        tree::node(tree::leaf(), 300u, tree::leaf()));
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        std::move(t).fn_and_val();
    return (p.first(5u) + p.second);
  }();
  /// TEST 8: Large tree stress test. Many closures, deep recursion.
  static tree make_balanced(unsigned int n);
  static mylist<std::function<unsigned int(unsigned int)>>
  collect_closures(const tree &t);

  static inline const unsigned int test_stress = []() {
    tree t = make_balanced(8u);
    return sum_fns(collect_closures(std::move(t)));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE14
