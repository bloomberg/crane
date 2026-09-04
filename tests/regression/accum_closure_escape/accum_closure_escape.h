#ifndef INCLUDED_ACCUM_CLOSURE_ESCAPE
#define INCLUDED_ACCUM_CLOSURE_ESCAPE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct AccumClosureEscape {
  /// This test explores closure escape through ACCUMULATOR patterns,
  /// which are different from the direct-return-in-constructor pattern
  /// tested by the other wip tests.
  ///
  /// Key difference: closures are built up in an accumulator during
  /// recursion. Each recursive step adds a new closure to a list.
  /// The closures capture pattern variables from the current match
  /// scope, which may be references into shared_ptr nodes.
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
                            if constexpr (std::is_same_v<_U, std::any>)
                              return crane_any_cast<A>(a0);
                            else
                              return A(a0);
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

    mylist<A> mylist_append(mylist<A> l2) const {
      std::shared_ptr<mylist<A>> _head{};
      std::shared_ptr<mylist<A>> *_write = &_head;
      const mylist<A> *_loop_self = this;
      mylist<A> _loop_l2 = std::move(l2);
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename mylist<A>::Mynil>(_sv.v())) {
          *_write = std::make_shared<mylist<A>>(std::move(_loop_l2));
          break;
        } else {
          const auto &[a0, a1] = std::get<typename mylist<A>::Mycons>(_sv.v());
          auto _cell = std::make_shared<mylist<A>>(
              typename mylist<A>::Mycons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename mylist<A>::Mycons>((*_write)->v_mut()).a1;
          _loop_self = crane_raw(a1);
          continue;
        }
      }
      return std::move(*_head);
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

  /// A simple tree for supplying values.
  struct tree {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<tree> a0;
      uint64_t a1;
      std::shared_ptr<tree> a2;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    tree() {}

    explicit tree(TLeaf _v) : v_(_v) {}

    explicit tree(TNode _v) : v_(std::move(_v)) {}

    static tree tleaf() { return tree(TLeaf{}); }

    static tree tnode(tree a0, uint64_t a1, tree a2) {
      return tree(TNode{std::make_shared<tree>(std::move(a0)), a1,
                        std::make_shared<tree>(std::move(a2))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
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

    /// Build closures from TREE traversal: tree nodes become closures.
    /// Each closure captures pattern variables from tree match.
    mylist<std::function<uint64_t(uint64_t)>> tree_to_adders() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_TNode: saves [_s0, _s1], dispatches next recursive call.
      struct _After_TNode {
        std::decay_t<decltype(&std::declval<const tree &>())> _s0;
        std::function<uint64_t(uint64_t)> _s1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        mylist<std::function<uint64_t(uint64_t)>> _result;
        std::function<uint64_t(uint64_t)> _s1;
      };

      using _Frame = std::variant<_Enter, _After_TNode, _Combine_TNode>;
      mylist<std::function<uint64_t(uint64_t)>> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_to_adders: _Enter -> _After_TNode -> _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = mylist<std::function<uint64_t(uint64_t)>>::mynil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            const tree &a0_value = *a0;
            const tree &a2_value = *a2;
            _stack.emplace_back(_After_TNode{
                &a0_value, [=](uint64_t x) mutable { return (a1 + x); }});
            _stack.emplace_back(_Enter{&a2_value});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(
              _Combine_TNode{std::move(_result), std::move(_f._s1)});
          _stack.emplace_back(_Enter{_f._s0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = mylist<std::function<uint64_t(uint64_t)>>::mycons(
              std::move(_f._s1),
              std::move(_result).mylist_append(std::move(_f._result)));
        }
      }
      return _result;
    }

    mylist<uint64_t> tree_to_list() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_TNode: saves [a0, a1], dispatches next recursive call.
      struct _After_TNode {
        tree *a0;
        uint64_t a1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        mylist<uint64_t> _result;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _After_TNode, _Combine_TNode>;
      mylist<uint64_t> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_to_list: _Enter -> _After_TNode -> _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = mylist<uint64_t>::mynil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode{crane_raw(a0), a1});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_Combine_TNode{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = mylist<uint64_t>::mycons(
              _f.a1, std::move(_result).mylist_append(std::move(_f._result)));
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

      /// _After_TNode: saves [a0_0, a2, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_TNode {
        tree *a0_0;
        tree a2;
        uint64_t a1;
        tree a0_1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        std::decay_t<T1> _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_TNode, _Combine_TNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rec: _Enter -> _After_TNode -> _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_Combine_TNode{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
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

      /// _After_TNode: saves [a0_0, a2, a1, a0_1], dispatches next recursive
      /// call.
      struct _After_TNode {
        tree *a0_0;
        tree a2;
        uint64_t a1;
        tree a0_1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        std::decay_t<T1> _result;
        tree a2;
        uint64_t a1;
        tree a0;
      };

      using _Frame = std::variant<_Enter, _After_TNode, _Combine_TNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_rect: _Enter -> _After_TNode -> _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_Combine_TNode{
              std::move(_result), std::move(_f.a2), _f.a1, std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), _f.a1,
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }
  };

  /// Fold-left that builds a closure from each element.
  ///
  /// SIMPLE LAMBDA VERSION: Each closure fun x => h + x captures
  /// h from the pattern match. These are simple lambdas, so they
  /// should capture by =.
  static mylist<std::function<uint64_t(uint64_t)>>
  build_adders(const mylist<uint64_t> &l,
               mylist<std::function<uint64_t(uint64_t)>> acc);
  /// Apply first closure from the list.
  static uint64_t
  apply_first(const mylist<std::function<uint64_t(uint64_t)>> &fns, uint64_t x);
  /// Apply all closures and sum.
  static uint64_t
  apply_all_sum(const mylist<std::function<uint64_t(uint64_t)>> &fns,
                uint64_t x);
  /// test1: build_adders 10, 20, 30  = 30+_, 20+_, 10+_ (reversed)
  /// apply_first result 5 = 30 + 5 = 35
  static inline const uint64_t test1 = []() {
    mylist<std::function<uint64_t(uint64_t)>> fns = build_adders(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return apply_first(std::move(fns), UINT64_C(5));
  }();
  /// test2: apply all closures: (30+5) + (20+5) + (10+5) = 35+25+15 = 75
  static inline const uint64_t test2 = []() {
    mylist<std::function<uint64_t(uint64_t)>> fns = build_adders(
        mylist<uint64_t>::mycons(
            UINT64_C(10),
            mylist<uint64_t>::mycons(
                UINT64_C(20), mylist<uint64_t>::mycons(
                                  UINT64_C(30), mylist<uint64_t>::mynil()))),
        mylist<std::function<uint64_t(uint64_t)>>::mynil());
    return apply_all_sum(std::move(fns), UINT64_C(5));
  }();

  /// COMPOSE CLOSURES: Each step builds a composed function.
  /// This creates closures that capture OTHER closures.
  static uint64_t compose_from_list(const mylist<uint64_t> &l,
                                    std::function<uint64_t(uint64_t)> acc,
                                    uint64_t _x0) {
    return [=]() mutable -> std::function<uint64_t(uint64_t)> {
      if (std::holds_alternative<typename mylist<uint64_t>::Mynil>(l.v())) {
        return acc;
      } else {
        const auto &[a0, a1] =
            std::get<typename mylist<uint64_t>::Mycons>(l.v());
        const mylist<uint64_t> &a1_value = *a1;
        return [=](uint64_t _x0) mutable -> uint64_t {
          return compose_from_list(
              a1_value, [=](uint64_t x) mutable { return acc((a0 + x)); }, _x0);
        };
      }
    }()(_x0);
  }

  /// test3: compose_from_list 10, 20, 30 id
  /// = fun x => id (10 + (20 + (30 + x)))
  /// = fun x => 60 + x
  /// test3 = 60 + 7 = 67
  static inline const uint64_t test3 = compose_from_list(
      mylist<uint64_t>::mycons(
          UINT64_C(10),
          mylist<uint64_t>::mycons(
              UINT64_C(20), mylist<uint64_t>::mycons(
                                UINT64_C(30), mylist<uint64_t>::mynil()))),
      [](uint64_t x) { return x; }, UINT64_C(7));
  /// test4: Tree (Node (Node Leaf 10 Leaf) 20 (Node Leaf 30 Leaf))
  /// Closures: 20+_, 10+_, 30+_
  /// apply_all_sum with 5: (20+5) + (10+5) + (30+5) = 25+15+35 = 75
  static inline const uint64_t test4 = []() {
    tree t = tree::tnode(
        tree::tnode(tree::tleaf(), UINT64_C(10), tree::tleaf()), UINT64_C(20),
        tree::tnode(tree::tleaf(), UINT64_C(30), tree::tleaf()));
    return apply_all_sum(std::move(t).tree_to_adders(), UINT64_C(5));
  }();
  /// Store a closure and then clobber the stack before using it.
  static inline const uint64_t test5 = []() {
    tree t =
        tree::tnode(tree::tnode(tree::tleaf(), UINT64_C(42), tree::tleaf()),
                    UINT64_C(100), tree::tleaf());
    mylist<std::function<uint64_t(uint64_t)>> fns =
        std::move(t).tree_to_adders();
    return apply_first(std::move(fns), UINT64_C(0));
  }();
};

#endif // INCLUDED_ACCUM_CLOSURE_ESCAPE
