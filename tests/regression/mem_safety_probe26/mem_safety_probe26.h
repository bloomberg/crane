#ifndef INCLUDED_MEM_SAFETY_PROBE26
#define INCLUDED_MEM_SAFETY_PROBE26

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe26 {
  /// Probe 26: Closures stored in inductives capturing match-bound tree data.
  ///
  /// Attack vector: Force creation of actual closure objects (not inlined)
  /// by storing them in inductive constructors. The closures capture
  /// tree children from match bindings, which are structured binding
  /// references to unique_ptr fields. If Crane fails to create explicit
  /// value copies, the closures hold dangling references.
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

    /// TEST 8: Conditional closure creation — match result determines
    /// which closure to store. Both branches create closures that
    /// capture tree data.
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
    conditional_closure(unsigned int n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](unsigned int x) { return x; }, 0u);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        tree a2_value = *a2;
        if (n <= a1) {
          return std::make_pair(
              [=](unsigned int x) mutable { return (x + a0_value.tree_sum()); },
              a1);
        } else {
          return std::make_pair(
              [=](unsigned int x) mutable { return (x + a2_value.tree_sum()); },
              a1);
        }
      }
    }

    /// TEST 7: Closure captures tree child and also uses it immediately
    /// in an expression — tests clone independence under shared access.
    std::pair<std::function<unsigned int(unsigned int)>, tree>
    shared_child_closure() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](unsigned int x) { return x; }, tree::leaf());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        return std::make_pair(
            [=](unsigned int x) mutable { return (x + a0_value.tree_sum()); },
            a0_value);
      }
    }

    /// TEST 6: Closure captures grandchild — two levels of deref.
    /// ll is accessed via l which is accessed via t.
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
    deep_closure_pair() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](unsigned int x) { return x; }, 0u);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        if (std::holds_alternative<typename tree::Leaf>(a0_value.v())) {
          return std::make_pair(
              [=](unsigned int x) mutable { return (x + a1); }, 0u);
        } else {
          const auto &[a00, a10, a20] =
              std::get<typename tree::Node>(a0_value.v());
          tree a00_value = *a00;
          tree a20_value = *a20;
          return std::make_pair(
              [=](unsigned int x) mutable {
                return ((x + a00_value.tree_sum()) + a10);
              },
              (a1 + a20_value.tree_sum()));
        }
      }
    }

    /// TEST 5: Closure captures tree child, then child is also used
    /// elsewhere in the same expression. Tests whether clone is
    /// independent of the original.
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
    closure_and_sum() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](unsigned int x) { return x; }, 0u);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        tree a2_value = *a2;
        return std::make_pair(
            [=](unsigned int x) mutable { return (x + a0_value.tree_sum()); },
            ((a0_value.tree_sum() + a1) + a2_value.tree_sum()));
      }
    }

    /// TEST 3: Closure stored in option, captures tree children.
    /// The option prevents inlining.
    std::optional<std::function<unsigned int(unsigned int)>>
    match_to_option() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::optional<std::function<unsigned int(unsigned int)>>();
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        tree a2_value = *a2;
        return std::make_optional<std::function<unsigned int(unsigned int)>>(
            [=](unsigned int x) mutable {
              return (((x + a0_value.tree_sum()) + a1) + a2_value.tree_sum());
            });
      }
    }

    /// TEST 2: Two closures in a pair, each captures a different child.
    /// Tests that both children are correctly cloned into their
    /// respective closures.
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
    split_closures() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](unsigned int x) { return x; },
                              [](unsigned int x) { return x; });
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        tree a2_value = *a2;
        return std::make_pair(
            [=](unsigned int x) mutable {
              return ((x + a0_value.tree_sum()) + a1);
            },
            [=](unsigned int x) mutable {
              return ((x + a1) + a2_value.tree_sum());
            });
      }
    }

    /// TEST 1: Closure stored in pair, captures tree children from match.
    /// The closure captures l and r — tree children accessed via unique_ptr.
    /// The test constructs the pair, then calls the closure after the
    /// original tree temporary is destroyed.
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int>
    match_to_pair() const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return std::make_pair([](unsigned int x) { return x; }, 0u);
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        tree a0_value = *a0;
        tree a2_value = *a2;
        return std::make_pair(
            [=](unsigned int x) mutable {
              return ((x + a0_value.tree_sum()) + a2_value.tree_sum());
            },
            a1);
      }
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
            _result = f;
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
            _result = f;
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

  static inline const unsigned int test_match_to_pair = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                   tree::node(tree::leaf(), 11u, tree::leaf()))
            .match_to_pair();
    return (p.first(100u) + p.second);
  }();
  static inline const unsigned int test_split_closures = []() {
    std::pair<std::function<unsigned int(unsigned int)>,
              std::function<unsigned int(unsigned int)>>
        p = tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                       tree::node(tree::leaf(), 11u, tree::leaf()))
                .split_closures();
    return (p.first(100u) + p.second(200u));
  }();
  static inline const unsigned int test_match_to_option = []() -> unsigned int {
    auto _cs = tree::node(tree::node(tree::leaf(), 2u, tree::leaf()), 5u,
                          tree::node(tree::leaf(), 8u, tree::leaf()))
                   .match_to_option();
    if (_cs.has_value()) {
      const std::function<unsigned int(unsigned int)> &f = *_cs;
      return f(100u);
    } else {
      return 0u;
    }
  }();

  /// TEST 4: Recursive function building list of closures.
  /// Each closure captures tree children from its level.
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
            _result = f;
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
            _result = f;
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

  static mylist<std::function<unsigned int(unsigned int)>>
  build_tree_closures(const tree &t);
  static unsigned int apply_first_closure(
      const mylist<std::function<unsigned int(unsigned int)>> &l,
      unsigned int x);
  static inline const unsigned int test_build_tree_closures = []() {
    mylist<std::function<unsigned int(unsigned int)>> closures =
        build_tree_closures(
            tree::node(tree::node(tree::leaf(), 4u, tree::leaf()), 6u,
                       tree::node(tree::leaf(), 9u, tree::leaf())));
    return apply_first_closure(std::move(closures), 100u);
  }();
  static inline const unsigned int test_closure_and_sum = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                   tree::node(tree::leaf(), 11u, tree::leaf()))
            .closure_and_sum();
    return (p.first(100u) + p.second);
  }();
  static inline const unsigned int test_deep_closure_pair = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p =
        tree::node(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()), 2u,
                              tree::node(tree::leaf(), 3u, tree::leaf())),
                   10u, tree::leaf())
            .deep_closure_pair();
    return (p.first(100u) + p.second);
  }();
  static inline const unsigned int test_shared_child_closure = []() {
    std::pair<std::function<unsigned int(unsigned int)>, tree> p =
        tree::node(tree::node(tree::leaf(), 5u, tree::leaf()), 10u,
                   tree::leaf())
            .shared_child_closure();
    return (p.first(100u) + p.second.tree_sum());
  }();
  static inline const unsigned int test_conditional_closure = []() {
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p1 =
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                   tree::node(tree::leaf(), 11u, tree::leaf()))
            .conditional_closure(5u);
    std::pair<std::function<unsigned int(unsigned int)>, unsigned int> p2 =
        tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u,
                   tree::node(tree::leaf(), 11u, tree::leaf()))
            .conditional_closure(10u);
    return (((p1.first(100u) + p1.second) + p2.first(200u)) + p2.second);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE26
