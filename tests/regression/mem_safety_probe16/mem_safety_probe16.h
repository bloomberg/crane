#ifndef INCLUDED_MEM_SAFETY_PROBE16
#define INCLUDED_MEM_SAFETY_PROBE16

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe16 {
  /// Probe 16: Focused on finding RUNTIME memory safety bugs.
  ///
  /// Attack vectors:
  /// 1. Higher-order functions that STORE closures in data structures
  /// then invoke them after the original scope ends
  /// 2. Partial application chains where each link captures a value
  /// that may have been moved
  /// 3. Functions that return closures from match branches where
  /// the closure captures match bindings from an OWNED match
  /// 4. fold/map patterns that build closure lists
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

    /// TEST 8: Higher-order map: apply a function to each element
    /// of a tree, building a new tree of closures.
    tree tree_map_val() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, _s1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        unsigned int _s1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree _result;
        unsigned int _s1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_map_val: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::leaf();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{a0.get(), (a1 + 1u)});
            _stack.emplace_back(_Enter{a2.get()});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f._s1});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = tree::node(_result, _f._s1, _f._result);
        }
      }
      return _result;
    }

    /// TEST 6: Non-recursive closure from a deeply nested match.
    unsigned int deep_nested_closure(unsigned int n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        auto &&_sv0 = *a0;
        if (std::holds_alternative<typename tree::Leaf>(_sv0.v())) {
          return ((a1 + (*a2).tree_sum()) + n);
        } else {
          const auto &[a00, a10, a20] = std::get<typename tree::Node>(_sv0.v());
          auto &&_sv1 = *a2;
          if (std::holds_alternative<typename tree::Leaf>(_sv1.v())) {
            return (((((*a00).tree_sum() + a10) + (*a20).tree_sum()) + a1) + n);
          } else {
            const auto &[a01, a11, a21] =
                std::get<typename tree::Node>(_sv1.v());
            return ((((((((*a00).tree_sum() + a10) + (*a20).tree_sum()) + a1) +
                       (*a01).tree_sum()) +
                      a11) +
                     (*a21).tree_sum()) +
                    n);
          }
        }
      }
    }

    /// TEST 5: A function that takes TWO trees and returns a closure
    /// capturing both. Tests double ownership.
    unsigned int pair_closure(const tree &t2, unsigned int n) const {
      return (((*this).tree_sum() + t2.tree_sum()) + n);
    }

    /// TEST 1: Store a closure derived from a tree in a list,
    /// then invoke it after the tree goes out of scope.
    /// The closure should capture by value.
    unsigned int make_summer(unsigned int n) const {
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

    unsigned int length() const {
      const mylist *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist *_self;
      };

      /// _Resume_Mycons: saves [_s0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        decltype(1u) _s0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      unsigned int _result{};
      std::vector<_Frame> _stack;
      _stack.reserve(8);
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = 0u;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{1u});
            _stack.emplace_back(_Enter{a1.get()});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = (_f._s0 + _result);
        }
      }
      return _result;
    }

    mylist<A> myapp(mylist<A> l2) const {
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

  static unsigned int sum_list(const mylist<unsigned int> &l);
  static mylist<std::function<unsigned int(unsigned int)>>
  build_summers(const mylist<tree> &trees);
  static unsigned int
  apply_fns(const mylist<std::function<unsigned int(unsigned int)>> &fns,
            unsigned int x);
  static inline const unsigned int test_store_closures = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::leaf(), 10u, tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::leaf(), 20u, tree::leaf()),
            mylist<tree>::mycons(tree::node(tree::leaf(), 30u, tree::leaf()),
                                 mylist<tree>::mynil())));
    mylist<std::function<unsigned int(unsigned int)>> fns =
        build_summers(std::move(trees));
    return apply_fns(std::move(fns), 0u);
  }();

  /// TEST 2: Fold that accumulates a function by composing closures.
  /// Each step captures the tree from the current list element.
  static unsigned int
  compose_summers(const mylist<tree> &trees,
                  std::function<unsigned int(unsigned int)> acc,
                  unsigned int _x0) { /// _Enter: captures varying parameters
                                      /// for each recursive call.

    struct _Enter {
      std::function<unsigned int(unsigned int)> acc;
      mylist<tree> trees;
    };

    using _Frame = std::variant<_Enter>;
    unsigned int _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{acc, trees});
    /// Loopified compose_summers: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<unsigned int(unsigned int)> acc = std::move(_f.acc);
      const mylist<tree> &trees = _f.trees;
      _result = [=]() mutable -> std::function<unsigned int(unsigned int)> {
        if (std::holds_alternative<typename mylist<tree>::Mynil>(trees.v())) {
          return acc;
        } else {
          const auto &[a0, a1] =
              std::get<typename mylist<tree>::Mycons>(trees.v());
          const mylist<tree> &a1_value = *a1;
          return [=](unsigned int _x0) mutable -> unsigned int {
            return compose_summers(
                a1_value,
                [=](unsigned int n) mutable {
                  return acc((a0.tree_sum() + n));
                },
                _x0);
          };
        }
      }()(_x0);
    }
    return _result;
  }

  static inline const unsigned int test_compose = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::leaf(), 5u, tree::leaf()),
        mylist<tree>::mycons(
            tree::node(tree::leaf(), 10u, tree::leaf()),
            mylist<tree>::mycons(tree::node(tree::leaf(), 15u, tree::leaf()),
                                 mylist<tree>::mynil())));
    return compose_summers(
        std::move(trees), [](unsigned int n) { return n; }, 0u);
  }();
  /// TEST 3: Build a list of closures where each closure captures
  /// the SAME tree at different levels.
  /// Tests whether the tree is properly cloned for each closure.
  static mylist<std::function<unsigned int(unsigned int)>>
  multi_capture_tree(tree t, unsigned int n);
  static inline const unsigned int test_multi_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                        tree::node(tree::leaf(), 11u, tree::leaf()));
    mylist<std::function<unsigned int(unsigned int)>> fns =
        multi_capture_tree(std::move(t), 3u);
    return apply_fns(std::move(fns), 0u);
  }();
  /// TEST 4: Return a closure from inside a NESTED match.
  /// The closure captures bindings from BOTH match levels.
  static unsigned int nested_match_closure(const tree &t,
                                           const mylist<unsigned int> &l,
                                           unsigned int n);
  static inline const unsigned int test_nested_match = []() {
    tree t = tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                        tree::node(tree::leaf(), 15u, tree::leaf()));
    mylist<unsigned int> l = mylist<unsigned int>::mycons(
        7u, mylist<unsigned int>::mycons(99u, mylist<unsigned int>::mynil()));
    return nested_match_closure(std::move(t), std::move(l), 3u);
  }();
  static inline const unsigned int test_pair_closure = []() {
    return []() {
      tree t1 = tree::node(tree::leaf(), 100u, tree::leaf());
      tree t2 = tree::node(tree::node(tree::leaf(), 50u, tree::leaf()), 25u,
                           tree::leaf());
      std::function<unsigned int(unsigned int)> f =
          [=](unsigned int _x0) mutable -> unsigned int {
        return t1.pair_closure(t2, _x0);
      };
      return (f(0u) + f(0u));
    }();
  }();
  static inline const unsigned int test_deep_nested = []() {
    tree t =
        tree::node(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                              tree::node(tree::leaf(), 3u, tree::leaf())),
                   10u,
                   tree::node(tree::node(tree::leaf(), 4u, tree::leaf()), 5u,
                              tree::node(tree::leaf(), 6u, tree::leaf())));
    return std::move(t).deep_nested_closure(0u);
  }();
  /// TEST 7: Map + apply pattern: build closures from tree children,
  /// apply them to values from another list.
  static mylist<unsigned int>
  zip_apply(const mylist<std::function<unsigned int(unsigned int)>> &fns,
            const mylist<unsigned int> &vals);
  static inline const unsigned int test_zip_apply = []() {
    mylist<tree> trees = mylist<tree>::mycons(
        tree::node(tree::leaf(), 10u, tree::leaf()),
        mylist<tree>::mycons(tree::node(tree::leaf(), 20u, tree::leaf()),
                             mylist<tree>::mynil()));
    mylist<std::function<unsigned int(unsigned int)>> fns =
        build_summers(std::move(trees));
    mylist<unsigned int> vals = mylist<unsigned int>::mycons(
        1u, mylist<unsigned int>::mycons(2u, mylist<unsigned int>::mynil()));
    mylist<unsigned int> results = zip_apply(std::move(fns), std::move(vals));
    return sum_list(std::move(results));
  }();
  static inline const unsigned int test_tree_map = []() {
    tree t = tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                        tree::node(tree::leaf(), 3u, tree::leaf()));
    return std::move(t).tree_map_val().tree_sum();
  }();

  /// TEST 9: CPS-style flattening where each step builds a continuation
  /// that captures tree structure.
  static mylist<unsigned int> flatten_cps_aux(
      const tree &t,
      std::function<mylist<unsigned int>(mylist<unsigned int>)>
          k) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      std::function<mylist<unsigned int>(mylist<unsigned int>)> k;
      const tree *t;
    };

    using _Frame = std::variant<_Enter>;
    mylist<unsigned int> _result{};
    std::vector<_Frame> _stack;
    _stack.reserve(8);
    _stack.emplace_back(_Enter{k, &t});
    /// Loopified flatten_cps_aux: _Enter.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      auto _f = std::move(std::get<_Enter>(_frame));
      std::function<mylist<unsigned int>(mylist<unsigned int>)> k =
          std::move(_f.k);
      const tree &t = *_f.t;
      if (std::holds_alternative<typename tree::Leaf>(t.v())) {
        _result = k(mylist<unsigned int>::mynil());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(t.v());
        const tree &a0_value = *a0;
        const tree &a2_value = *a2;
        _stack.emplace_back(_Enter{
            [=](const mylist<unsigned int> &ll) mutable {
              return flatten_cps_aux(
                  a2_value, [=](mylist<unsigned int> rl) mutable {
                    return k(ll.myapp(mylist<unsigned int>::mycons(a1, rl)));
                  });
            },
            a0.get()});
      }
    }
    return _result;
  }

  static mylist<unsigned int> flatten_cps(const tree &t);
  static inline const unsigned int test_flatten_cps = []() {
    tree t = tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                        tree::node(tree::leaf(), 3u, tree::leaf()));
    return sum_list(flatten_cps(std::move(t)));
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE16
