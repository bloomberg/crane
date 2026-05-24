#ifndef INCLUDED_MEM_SAFETY_PROBE19
#define INCLUDED_MEM_SAFETY_PROBE19

#include <any>
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
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    /// TEST 7: Nested match returning closures at multiple levels.
    uint64_t nested_match_fn(bool b1, bool b2, uint64_t n) const {
      if (b1) {
        if (b2) {
          return (this->tree_sum() + n);
        } else {
          return ((this->tree_sum() + this->tree_sum()) + n);
        }
      } else {
        return n;
      }
    }

    /// TEST 1: Return closure from if-branch.
    /// The if becomes a top-level Sif in the function body.
    /// return_captures_by_value won't recurse into it.
    uint64_t choose_fn(bool b, uint64_t n) const {
      if (b) {
        return (this->tree_sum() + n);
      } else {
        return n;
      }
    }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [_s0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *_s0;
        uint64_t a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
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
            _result = UINT64_C(0);
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
          _result = ((std::move(_result) + _f.a1) + std::move(_f._result));
        }
      }
      return _result;
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

  static inline const uint64_t test_choose =
      tree::node(tree::leaf(), UINT64_C(42), tree::leaf())
          .choose_fn(true, UINT64_C(0));

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

    template <typename _U> explicit myopt(const myopt<_U> &_other) {
      if (std::holds_alternative<typename myopt<_U>::Mynone>(_other.v())) {
        this->v_ = Mynone{};
      } else {
        const auto &[a0] = std::get<typename myopt<_U>::Mysome>(_other.v());
        this->v_ = Mysome{[&]() -> A {
          if constexpr (std::is_same_v<_U, std::any>) {
            if (a0.type() == typeid(A))
              return std::any_cast<A>(a0);
            if constexpr (requires {
                            typename A::first_type;
                            typename A::second_type;
                          }) {
              const auto &[_k, _v] =
                  std::any_cast<std::pair<std::any, std::any>>(a0);
              return A{[&]() -> typename A::first_type {
                         if constexpr (std::is_same_v<typename A::first_type,
                                                      std::any>)
                           return _k;
                         else
                           return std::any_cast<typename A::first_type>(_k);
                       }(),
                       [&]() -> typename A::second_type {
                         if constexpr (std::is_same_v<typename A::second_type,
                                                      std::any>)
                           return _v;
                         else
                           return std::any_cast<typename A::second_type>(_v);
                       }()};
            }
            return std::any_cast<A>(a0);
          } else
            return A(a0);
        }()};
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

  static uint64_t option_fn(const tree &t, const myopt<uint64_t> &o,
                            uint64_t n);
  static inline const uint64_t test_option_fn =
      option_fn(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                myopt<uint64_t>::mysome(UINT64_C(5)), UINT64_C(3));
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

  static uint64_t choice_fn(const tree &t, Choice c, uint64_t n);
  static inline const uint64_t test_choice_left =
      choice_fn(tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                           UINT64_C(7), tree::leaf()),
                Choice::CLEFT, UINT64_C(0));
  /// tree_sum = 3 + 7 = 10. f(0) = 10
  static inline const uint64_t test_choice_both =
      choice_fn(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                Choice::CBOTH, UINT64_C(1));
  /// TEST 4: Closure returned from if, capturing a locally-built tree.
  /// The let-bound tree is on the stack. If the returned lambda
  /// captures by &, it holds a reference to the dead stack frame.
  static uint64_t make_adder(uint64_t n, bool b, uint64_t _x0);
  static inline const uint64_t test_make_adder =
      make_adder(UINT64_C(20), true, UINT64_C(5));
  /// TEST 5: Double use of returned closure.
  /// Ensures the closure is a real std::function, not inlined.
  static inline const uint64_t test_double_use = []() {
    std::function<uint64_t(uint64_t)> f = [](uint64_t _x0) -> uint64_t {
      return tree::node(tree::leaf(), UINT64_C(7), tree::leaf())
          .choose_fn(true, _x0);
    };
    return (f(UINT64_C(1)) + f(UINT64_C(2)));
  }();

  /// TEST 6: Pass returned closure to a higher-order function.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_to(F0 &&f, uint64_t _x0) {
    return f(_x0);
  }

  static inline const uint64_t test_pass_closure = []() {
    std::function<uint64_t(uint64_t)> f = [](uint64_t _x0) -> uint64_t {
      return tree::node(tree::leaf(), UINT64_C(15), tree::leaf())
          .choose_fn(true, _x0);
    };
    return apply_to(f, UINT64_C(10));
  }();
  static inline const uint64_t test_nested_match =
      tree::node(tree::leaf(), UINT64_C(4), tree::leaf())
          .nested_match_fn(true, true, UINT64_C(0));
  /// f(0) = 4
  static inline const uint64_t test_nested_match2 =
      tree::node(tree::leaf(), UINT64_C(4), tree::leaf())
          .nested_match_fn(true, false, UINT64_C(0));
  /// TEST 8: Closure from match, used across let-bindings.
  /// Maximum distance between closure creation and use.
  static inline const uint64_t test_delayed_use = []() {
    std::function<uint64_t(uint64_t)> f = [](uint64_t _x0) -> uint64_t {
      return choice_fn(
          tree::node(tree::node(tree::leaf(), UINT64_C(1), tree::leaf()),
                     UINT64_C(2),
                     tree::node(tree::leaf(), UINT64_C(3), tree::leaf())),
          Choice::CLEFT, _x0);
    };
    uint64_t a = UINT64_C(100);
    uint64_t b = (a + UINT64_C(200));
    uint64_t c = (b + UINT64_C(300));
    return f(c);
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE19
