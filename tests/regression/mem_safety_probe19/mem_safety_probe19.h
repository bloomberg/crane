#ifndef INCLUDED_MEM_SAFETY_PROBE19
#define INCLUDED_MEM_SAFETY_PROBE19

#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct MemSafetyProbe19 {
  /// Probe 19: return_captures_by_value gap.
  ///
  /// Attack vector: return_captures_by_value (translation.ml:1220-1227)
  /// only processes top-level Sreturn statements. When a function's body
  /// is an Sif or Smatch (from if/match in Rocq), the outer List.map
  /// matches s -> s and passes through unchanged, leaving & lambdas
  /// inside branches unconverted to =. This means closures returned
  /// from inside if/match branches capture local variables by reference,
  /// creating dangling references after the function returns.
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

    tree(tree &&_other) : v_(std::move(_other.v_)) {}

    tree &operator=(const tree &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    tree &operator=(tree &&_other) {
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

    /// TEST 7: Nested match returning closures at multiple levels.
    unsigned int nested_match_fn(bool b1, bool b2, unsigned int n) const {
      if (b1) {
        if (b2) {
          return ((*this).tree_sum() + n);
        } else {
          return (((*this).tree_sum() + (*this).tree_sum()) + n);
        }
      } else {
        return n;
      }
    }

    /// TEST 1: Return closure from if-branch.
    /// The if becomes a top-level Sif in the function body.
    /// return_captures_by_value won't recurse into it.
    unsigned int choose_fn(bool b, unsigned int n) const {
      if (b) {
        return ((*this).tree_sum() + n);
      } else {
        return n;
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

  static inline const unsigned int test_choose =
      tree::node(tree::leaf(), 42u, tree::leaf()).choose_fn(true, 0u);

  /// TEST 2: Return closure from match on option.
  /// The match becomes a top-level Smatch.
  template <typename A> struct myopt {
    // TYPES
    struct Mynone {};

    struct Mysome {
      A a0;
    };

    using variant_t = std::variant<Mynone, Mysome>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    myopt() {}

    explicit myopt(Mynone _v) : v_(_v) {}

    explicit myopt(Mysome _v) : v_(std::move(_v)) {}

    myopt(const myopt<A> &_other) : v_(std::move(_other.clone().v_)) {}

    myopt(myopt<A> &&_other) : v_(std::move(_other.v_)) {}

    myopt<A> &operator=(const myopt<A> &_other) {
      v_ = std::move(_other.clone().v_);
      return *this;
    }

    myopt<A> &operator=(myopt<A> &&_other) {
      v_ = std::move(_other.v_);
      return *this;
    }

    // ACCESSORS
    myopt<A> clone() const {
      if (std::holds_alternative<Mynone>(this->v())) {
        return myopt<A>(Mynone{});
      } else {
        const auto &[a0] = std::get<Mysome>(this->v());
        return myopt<A>(Mysome{a0});
      }
    }

    // CREATORS
    template <typename _U> explicit myopt(const myopt<_U> &_other) {
      if (std::holds_alternative<typename myopt<_U>::Mynone>(_other.v())) {
        this->v_ = Mynone{};
      } else {
        const auto &[a0] = std::get<typename myopt<_U>::Mysome>(_other.v());
        this->v_ = Mysome{A(a0)};
      }
    }

    static myopt<A> mynone() { return myopt(Mynone{}); }

    static myopt<A> mysome(A a0) { return myopt(Mysome{std::move(a0)}); }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    T1 myopt_rec(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename myopt<A>::Mynone>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename myopt<A>::Mysome>(this->v());
        return f0(a0);
      }
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &>
    T1 myopt_rect(T1 f, F1 &&f0) const {
      if (std::holds_alternative<typename myopt<A>::Mynone>(this->v())) {
        return f;
      } else {
        const auto &[a0] = std::get<typename myopt<A>::Mysome>(this->v());
        return f0(a0);
      }
    }
  };

  static unsigned int option_fn(const tree &t, const myopt<unsigned int> &o,
                                unsigned int n);
  static inline const unsigned int test_option_fn =
      option_fn(tree::node(tree::leaf(), 10u, tree::leaf()),
                myopt<unsigned int>::mysome(5u), 3u);
  /// TEST 3: Return closure from match on custom 3-constructor type.
  enum class Choice { CLEFT, CRIGHT, CBOTH };

  template <typename T1> static T1 choice_rect(T1 f, T1 f0, T1 f1, Choice c) {
    switch (c) {
    case Choice::CLEFT: {
      return f;
    }
    case Choice::CRIGHT: {
      return f0;
    }
    case Choice::CBOTH: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  template <typename T1> static T1 choice_rec(T1 f, T1 f0, T1 f1, Choice c) {
    switch (c) {
    case Choice::CLEFT: {
      return f;
    }
    case Choice::CRIGHT: {
      return f0;
    }
    case Choice::CBOTH: {
      return f1;
    }
    default:
      std::unreachable();
    }
  }

  static unsigned int choice_fn(const tree &t, Choice c, unsigned int n);
  static inline const unsigned int test_choice_left = choice_fn(
      tree::node(tree::node(tree::leaf(), 3u, tree::leaf()), 7u, tree::leaf()),
      Choice::CLEFT, 0u);
  /// tree_sum = 3 + 7 = 10. f(0) = 10
  static inline const unsigned int test_choice_both =
      choice_fn(tree::node(tree::leaf(), 5u, tree::leaf()), Choice::CBOTH, 1u);
  /// TEST 4: Closure returned from if, capturing a locally-built tree.
  /// The let-bound tree is on the stack. If the returned lambda
  /// captures by &, it holds a reference to the dead stack frame.
  static unsigned int make_adder(unsigned int n, bool b, unsigned int _x0);
  static inline const unsigned int test_make_adder = make_adder(20u, true, 5u);
  /// TEST 5: Double use of returned closure.
  /// Ensures the closure is a real std::function, not inlined.
  static inline const unsigned int test_double_use = []() {
    std::function<unsigned int(unsigned int)> f =
        [](unsigned int _x0) -> unsigned int {
      return tree::node(tree::leaf(), 7u, tree::leaf()).choose_fn(true, _x0);
    };
    return (f(1u) + f(2u));
  }();

  /// TEST 6: Pass returned closure to a higher-order function.
  template <typename F0>
    requires std::is_invocable_r_v<unsigned int, F0 &, unsigned int &>
  static unsigned int apply_to(F0 &&f, unsigned int _x0) {
    return f(_x0);
  }

  static inline const unsigned int test_pass_closure = []() {
    std::function<unsigned int(unsigned int)> f =
        [](unsigned int _x0) -> unsigned int {
      return tree::node(tree::leaf(), 15u, tree::leaf()).choose_fn(true, _x0);
    };
    return apply_to(f, 10u);
  }();
  static inline const unsigned int test_nested_match =
      tree::node(tree::leaf(), 4u, tree::leaf())
          .nested_match_fn(true, true, 0u);
  /// f(0) = 4
  static inline const unsigned int test_nested_match2 =
      tree::node(tree::leaf(), 4u, tree::leaf())
          .nested_match_fn(true, false, 0u);
  /// TEST 8: Closure from match, used across let-bindings.
  /// Maximum distance between closure creation and use.
  static inline const unsigned int test_delayed_use = []() {
    std::function<unsigned int(unsigned int)> f =
        [](unsigned int _x0) -> unsigned int {
      return choice_fn(tree::node(tree::node(tree::leaf(), 1u, tree::leaf()),
                                  2u,
                                  tree::node(tree::leaf(), 3u, tree::leaf())),
                       Choice::CLEFT, _x0);
    };
    unsigned int a = 100u;
    unsigned int b = (a + 200u);
    unsigned int c = (b + 300u);
    return f(c);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE19
