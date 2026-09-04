#ifndef INCLUDED_MEM_SAFETY_PROBE11
#define INCLUDED_MEM_SAFETY_PROBE11

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct MemSafetyProbe11 {
  /// Probe 11: Closure escape through ACCUMULATOR in loopified
  /// tail-recursive functions, specifically testing the interaction
  /// between the new flatten optimization (make_owned_param_matches)
  /// and closure capture in match branches.
  ///
  /// Key attack vector: A tail-recursive function with an accumulator
  /// that stores closures. Each closure captures a unique_ptr field
  /// from the match destructuring. After loopification, the match
  /// uses v_mut() and mutable bindings. If closures capture mutable
  /// bindings by reference and the field is later moved, we get
  /// use-after-move.
  template <typename A> struct mylist {
    // TYPES
    struct Mynil {};

    struct Mycons {
      A a0;
      std::shared_ptr<mylist<A>> a1;
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

    template <typename _U> mylist(const mylist<_U> &_other) {
      if (std::holds_alternative<typename mylist<_U>::Mynil>(_other.v())) {
        this->v_ = Mynil{};
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<_U>::Mycons>(_other.v());
        this->v_ = Mycons{[&]() -> A {
                            if constexpr (std::is_same_v<_U, std::any>) {
                              return crane_any_cast<A>(a0);
                            } else {
                              return A(a0);
                            }
                          }(),
                          (a1 ? std::make_shared<mylist<A>>(*a1) : nullptr)};
      }
    }

    static mylist<A> mynil() { return mylist<A>(Mynil{}); }

    static mylist<A> mycons(A a0, mylist<A> a1) {
      return mylist<A>(
          Mycons{std::move(a0), std::make_shared<mylist<A>>(std::move(a1))});
    }

    // MANIPULATORS
    ~mylist() {
      crane::small_vector<std::shared_ptr<mylist<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Mycons>(&_v)) {
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    mylist(const mylist &) = default;
    mylist &operator=(const mylist &) = default;
    mylist(mylist &&) noexcept = default;
    mylist &operator=(mylist &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t length() const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Resume_Mycons: saves [_s0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        std::decay_t<decltype(UINT64_C(1))> _s0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified length: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{UINT64_C(1)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = (_f._s0 + std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rec(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Resume_Mycons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        mylist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rec: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, A &, mylist<A> &, T1 &>
    T1 mylist_rect(T1 f, F1 &&f0) const {
      const mylist<A> *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const mylist<A> *_self;
      };

      /// _Resume_Mycons: saves [a1, a0], resumes after recursive call with
      /// _result.
      struct _Resume_Mycons {
        mylist<A> a1;
        std::decay_t<A> a0;
      };

      using _Frame = std::variant<_Enter, _Resume_Mycons>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mylist_rect: _Enter -> _Resume_Mycons.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const mylist<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1] =
                std::get<typename mylist<A>::Mycons>(_sv.v());
            _stack.emplace_back(_Resume_Mycons{*a1, a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else {
          auto _f = std::move(std::get<_Resume_Mycons>(_frame));
          _result = f0(std::move(_f.a0), std::move(_f.a1), std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t sum_fns(const mylist<std::function<uint64_t(uint64_t)>> &l);

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
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a2) {
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

    /// TEST 6: Function that matches on a tree AND returns a closure
    /// that RETURNS A TREE. Tests capture of value types in returned
    /// closures where the return type contains unique_ptr.
    tree tree_transformer(uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return tree::node(tree::leaf(), n, tree::leaf());
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        return tree::node(*a0, (a1 + n), *a2);
      }
    }

    /// TEST 4: Closure capturing pattern variables from a NESTED match.
    /// The outer match destructs a tree, the inner match destructs a list.
    /// Tests pre-copy across nested match scopes.
    uint64_t nested_capture(const mylist<uint64_t> &l, uint64_t n) const {
      if (std::holds_alternative<typename tree::Leaf>(this->v())) {
        return n;
      } else {
        const auto &[a0, a1, a2] = std::get<typename tree::Node>(this->v());
        if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
          return (a1 + n);
        } else {
          const auto &[a00, a10] =
              std::get<typename mylist<uint64_t>::Mycons>(l.v());
          return ((((a0->tree_sum() + a2->tree_sum()) + a00) + a1) + n);
        }
      }
    }

    uint64_t tree_depth() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _Cont_Node: saves [a2], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Node {
        std::shared_ptr<tree> a2;
      };

      /// _Cont_Node_1: saves [dl], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Node_1 {
        uint64_t dl;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_depth: _Enter -> _Cont_Node -> _Cont_Node_1.
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
            _stack.emplace_back(_Cont_Node{a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          uint64_t dl = std::move(_result);
          _stack.emplace_back(_Cont_Node_1{dl});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          uint64_t dl = _f.dl;
          uint64_t dr = std::move(_result);
          _result = (UINT64_C(1) + (dl <= dr ? dr : dl));
        }
      }
      return _result;
    }

    uint64_t tree_sum() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0, a1], dispatches next recursive call.
      struct _After_Node {
        tree *a0;
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
      crane::small_vector<_Frame> _stack;
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
            _stack.emplace_back(_After_Node{crane_raw(a0), a1});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f.a0});
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

      /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *a0_0;
        tree a2;
        uint64_t a1;
        tree a0_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
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
            _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result));
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

      /// _After_Node: saves [a0_0, a2, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_Node {
        tree *a0_0;
        tree a2;
        uint64_t a1;
        tree a0_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
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
            _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }
  };

  /// TEST 1: Accumulate closures that capture BOTH subtrees.
  /// Each closure uses tree_sum on both l and r.
  /// Both subtrees are also used in recursive calls.
  /// After loopification with flatten, the subtrees' unique_ptrs
  /// may be moved into continuation frames.
  template <typename T1>
  static uint64_t _collect_dual_captures_f(const T1, const tree l,
                                           const tree r) {
    return (std::move(l).tree_sum() + r.tree_sum());
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  collect_dual_captures(const tree &t,
                        mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_dual_capture = []() {
    tree t = tree::node(
        tree::node(tree::leaf(), UINT64_C(5), tree::leaf()), UINT64_C(10),
        tree::node(tree::leaf(), UINT64_C(15),
                   tree::node(tree::leaf(), UINT64_C(20), tree::leaf())));
    return sum_fns(collect_dual_captures(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil()));
  }();

  /// TEST 2: Closure captures the TAIL of the list (unique_ptr field).
  /// Each closure computes length of the tail.
  /// After loopification, the tail pointer may be moved.
  template <typename T1>
  static uint64_t _capture_tails_f(const T1, const uint64_t x,
                                   const mylist<uint64_t> xs) {
    return (std::move(x) + xs.length());
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  capture_tails(const mylist<uint64_t> &l,
                mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_capture_tails = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(100),
        mylist<uint64_t>::mycons(
            UINT64_C(200), mylist<uint64_t>::mycons(
                               UINT64_C(300), mylist<uint64_t>::mynil())));
    return sum_fns(capture_tails(
        std::move(l), mylist<std::function<uint64_t(uint64_t)>>::mynil()));
  }();

  /// TEST 3: Closure captures a SUBTREE, but the subtree is ALSO
  /// passed to a recursive call AND used in the continuation.
  /// Tests whether the clone/pre-copy mechanism handles triple use.
  template <typename T1>
  static uint64_t _triple_use_tree_fl(const T1, const tree l) {
    return std::move(l).tree_sum();
  }

  template <typename T1>
  static uint64_t _triple_use_tree_fr(const T1, const tree r) {
    return r.tree_sum();
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  triple_use_tree(const tree &t, mylist<std::function<uint64_t(uint64_t)>> acc);
  static inline const uint64_t test_triple_use = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(3), tree::leaf()),
                        UINT64_C(7),
                        tree::node(tree::leaf(), UINT64_C(11), tree::leaf()));
    return sum_fns(triple_use_tree(
        std::move(t), mylist<std::function<uint64_t(uint64_t)>>::mynil()));
  }();
  static inline const uint64_t test_nested_capture = []() {
    tree t = tree::node(tree::node(tree::leaf(), UINT64_C(10), tree::leaf()),
                        UINT64_C(20),
                        tree::node(tree::leaf(), UINT64_C(30), tree::leaf()));
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(5),
        mylist<uint64_t>::mycons(UINT64_C(99), mylist<uint64_t>::mynil()));
    return std::move(t).nested_capture(std::move(l), UINT64_C(7));
  }();

  /// TEST 5: Tail-recursive function with two accumulators,
  /// one of which stores closures that capture the other.
  /// Tests whether accumulator values are properly captured.
  template <typename T1>
  static uint64_t _dual_accum_f(const T1, const uint64_t new_sum) {
    return new_sum;
  }

  static mylist<std::function<uint64_t(uint64_t)>>
  dual_accum(const mylist<uint64_t> &l, uint64_t sum_acc,
             mylist<std::function<uint64_t(uint64_t)>> fn_acc);
  static inline const uint64_t test_dual_accum = []() {
    mylist<uint64_t> l = mylist<uint64_t>::mycons(
        UINT64_C(10),
        mylist<uint64_t>::mycons(
            UINT64_C(20),
            mylist<uint64_t>::mycons(UINT64_C(30), mylist<uint64_t>::mynil())));
    return sum_fns(
        dual_accum(std::move(l), UINT64_C(0),
                   mylist<std::function<uint64_t(uint64_t)>>::mynil()));
  }();
  static inline const uint64_t test_tree_transformer = []() {
    return []() {
      tree t = tree::node(tree::node(tree::leaf(), UINT64_C(5), tree::leaf()),
                          UINT64_C(10),
                          tree::node(tree::leaf(), UINT64_C(15), tree::leaf()));
      std::function<tree(uint64_t)> f = [&](uint64_t _x0) -> tree {
        return std::move(t).tree_transformer(_x0);
      };
      tree t2 = f(UINT64_C(100));
      return std::move(t2).tree_sum();
    }();
  }();
};

#endif // INCLUDED_MEM_SAFETY_PROBE11
