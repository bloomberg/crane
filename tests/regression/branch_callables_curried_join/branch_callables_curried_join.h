#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Ascii;
struct String;

struct Nat {};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, crane::shared_child_slot<String> a1) {
    return String(String0{std::move(a0), a1.take()});
  }

  // MANIPULATORS
  ~String() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// Match branches producing two-argument function values, one a curried
/// lambda, the other a composed let-lambda (let cf .. in let cg .. in fun c
/// => cf (cg c)), bound by a beta-redex: the C++ declares the variable at
/// one branch's type and assigns the other ("no viable overloaded '='").
/// Remaining after d7cf5aaae (common crane::fn type for joined callables).
/// A match's branches now carry the slot into their tails, so the lambda
/// knows the Core type backing the two-parameter function it is written
/// against, and takes the parameter its body leaves to a partial
/// application.

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct BranchCallablesCurriedJoin {
  struct pt {
    uint64_t px;
    bool py;
  };

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

    static tree node(crane::shared_child_slot<tree> a0, uint64_t a1,
                     crane::shared_child_slot<tree> a2) {
      return tree(Node{a0.take(), a1, a2.take()});
    }

    // MANIPULATORS
    ~tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<Leaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<Node>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
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
    tree(tree &&) = default;
    tree &operator=(tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t tree_obs() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_obs: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_obs_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_obs_in_Node_2 {
        uint64_t a1;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_obs_in_Node,
                                  _after_tree_obs_in_Node_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_obs_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_obs_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_obs_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_obs_in_Node_2{a1,
                                                        std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_obs_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          auto _once1 = (((_f._tmp2 * UINT64_C(7)) + a1) +
                         (std::move(_result) * UINT64_C(3)));
          _result = (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
        }
      }
      return _result;
    }

    tree tins(uint64_t n) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tins: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tins_in_false {
        std::shared_ptr<tree> a0;
        uint64_t a1;
      };

      struct _after_tins_in_true {
        uint64_t a1;
        std::shared_ptr<tree> a2;
      };

      using _frame =
          std::variant<_call, _after_tins_in_false, _after_tins_in_true>;
      tree _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = tree::node(tree::leaf(), n, tree::leaf());
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            if (n < a1) {
              _stack.emplace_back(_after_tins_in_true{a1, a2});
              _stack.emplace_back(_call{crane_raw(a0)});
            } else {
              _stack.emplace_back(_after_tins_in_false{a0, a1});
              _stack.emplace_back(_call{crane_raw(a2)});
            }
          }
        } else if (std::holds_alternative<_after_tins_in_false>(_popped)) {
          auto _f = std::move(std::get<_after_tins_in_false>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          _result = tree::node(crane::shared_child(a0), a1, std::move(_result));
        } else {
          auto _f = std::move(std::get<_after_tins_in_true>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          _result = tree::node(std::move(_result), a1, crane::shared_child(a2));
        }
      }
      return _result;
    }

    template <typename T1, typename F1> T1 tree_rec(T1 f, F1 &&f0) const {
      return this->template tree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 tree_rect(T1 f, F1 &&f0) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_tree_rect_in_Node {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
      };

      struct _after_tree_rect_in_Node_2 {
        std::shared_ptr<tree> a0;
        uint64_t a1;
        const tree *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_tree_rect_in_Node,
                                  _after_tree_rect_in_Node_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_tree_rect_in_Node{a0, a1,
                                                         crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_tree_rect_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_tree_rect_in_Node>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_tree_rect_in_Node_2{std::move(a0), a1, &a2,
                                                         std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_rect_in_Node_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<tree> a0 = std::move(_f.a0);
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  struct sz_nat {
    constexpr static uint64_t sz(uint64_t n) { return n; }
  };

  static_assert(Sz<sz_nat, uint64_t>);

  struct sz_bool {
    constexpr static uint64_t sz(bool b) {
      if (b) {
        return UINT64_C(1);
      } else {
        return UINT64_C(0);
      }
    }
  };

  static_assert(Sz<sz_bool, bool>);

  struct sz_tree {
    static uint64_t sz(tree a0) { return a0.tree_obs(); }
  };

  static_assert(Sz<sz_tree, tree>);

  template <typename _tcI0, typename T1>
    requires Sz<_tcI0, T1>
  struct sz_list {
    static uint64_t sz(List<T1> l) {
      return l.template fold_left<uint64_t>(
          [=](uint64_t a, const T1 &x) {
            auto _once1 = (a + _tcI0::sz(x));
            return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
          },
          UINT64_C(0));
    }
  };

  template <typename A> struct ptree {
    // TYPES
    struct PLeaf {};

    struct PNode {
      std::shared_ptr<ptree<A>> a0;
      A a1;
      std::shared_ptr<ptree<A>> a2;
    };

    using variant_t = std::variant<PLeaf, PNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ptree() {}

    explicit ptree(PLeaf _v) : v_(_v) {}

    explicit ptree(PNode _v) : v_(std::move(_v)) {}

    template <typename CraneU>
    ptree(const ptree<CraneU> &_other)
        : v_([&]() -> variant_t {
            if (std::holds_alternative<typename ptree<CraneU>::PLeaf>(
                    _other.v())) {
              return PLeaf{};
            } else {
              const auto &[a0, a1, a2] =
                  std::get<typename ptree<CraneU>::PNode>(_other.v());
              return PNode{
                  (a0 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a0))
                      : nullptr),
                  [&]() -> A {
                    if constexpr (crane_convertible<A, const CraneU &>) {
                      return crane_convert<A>(a1);
                    } else {
                      throw std::logic_error("unreachable: inactive "
                                             "constructor field at this "
                                             "instantiation");
                    }
                  }(),
                  (a2 ? std::make_shared<ptree<A>>(crane_convert<ptree<A>>(*a2))
                      : nullptr)};
            }
          }()) {}

    static ptree<A> pleaf() { return ptree<A>(PLeaf{}); }

    static ptree<A> pnode(crane::shared_child_slot<ptree<A>> a0, A a1,
                          crane::shared_child_slot<ptree<A>> a2) {
      return ptree<A>(PNode{a0.take(), std::move(a1), a2.take()});
    }

    // MANIPULATORS
    ~ptree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<PLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<PNode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a2 && _alt->a2.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<ptree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<PNode>(&_v)) {
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

    ptree(const ptree &) = default;
    ptree &operator=(const ptree &) = default;
    ptree(ptree &&) = default;
    ptree &operator=(ptree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename T1, typename F1> T1 ptree_rec(T1 f, F1 &&f0) const {
      return this->template ptree_rect<T1>(std::move(f), f0);
    }

    template <typename T1, typename F1> T1 ptree_rect(T1 f, F1 &&f0) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of ptree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
      };

      struct _after_ptree_rect_in_PNode {
        std::shared_ptr<ptree<A>> a0;
        A a1;
        const ptree<A> *a2;
      };

      struct _after_ptree_rect_in_PNode_2 {
        std::shared_ptr<ptree<A>> a0;
        A a1;
        const ptree<A> *a2;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_ptree_rect_in_PNode,
                                  _after_ptree_rect_in_PNode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ptree<A> *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(
                _after_ptree_rect_in_PNode{a0, a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_ptree_rect_in_PNode>(_popped)) {
          auto _f = std::move(std::get<_after_ptree_rect_in_PNode>(_popped));
          _stack.pop_back();
          std::shared_ptr<ptree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(_after_ptree_rect_in_PNode_2{
              std::move(a0), std::move(a1), &a2, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_ptree_rect_in_PNode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<ptree<A>> a0 = std::move(_f.a0);
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _result = f0(*a0, std::move(_f._tmp2), a1, a2, std::move(_result));
        }
      }
      return _result;
    }
  };

  static uint64_t t(const List<uint64_t> &l);
  /// The same join as a fold_left step's result: the accumulator passes
  /// through fold_left's type variable, so the step returns its curried
  /// spelling, and so do both branches.
  static uint64_t t2(const List<uint64_t> &l);
  /// Round-8 variants: the join at list types; a class method as a curried
  /// result; a callable inside a pair; a let-wrapped composition passed for
  /// a local fixpoint's function parameter.
  static inline const uint64_t v1 = []() -> uint64_t {
    auto _cs = sz_list<sz_tree, tree>::sz(List<tree>::nil());
    if (_cs <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t _x = _cs - 1;
      crane::fn<uint64_t(List<tree>, uint64_t)> cf =
          [](const List<tree> &, uint64_t) { return UINT64_C(0); };
      crane::fn<List<tree>(List<uint64_t>)> cg = [](const List<uint64_t> &) {
        return List<tree>::cons(tree::leaf(), List<tree>::nil());
      };
      List<uint64_t> c =
          List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
      return cf(cg(std::move(c)), UINT64_C(2));
    }
  }();
  static inline const uint64_t v2 = []() -> uint64_t {
    auto _cs = sz_list<sz_tree, tree>::sz(List<tree>::nil());
    if (_cs <= 0) {
      List<uint64_t> y =
          List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
      if (std::holds_alternative<typename List<uint64_t>::Nil>(y.v_mut())) {
        return sz_nat::sz(UINT64_C(2));
      } else {
        return UINT64_C(0);
      }
    } else {
      uint64_t _x = _cs - 1;
      crane::fn<uint64_t(List<tree>, uint64_t)> cf =
          [](const List<tree> &, uint64_t) { return UINT64_C(0); };
      crane::fn<List<tree>(List<uint64_t>)> cg = [](const List<uint64_t> &) {
        return List<tree>::cons(tree::leaf(), List<tree>::nil());
      };
      List<uint64_t> c =
          List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil());
      return cf(cg(std::move(c)), UINT64_C(2));
    }
  }();
  static uint64_t v3(const std::optional<uint64_t> &x);
  static uint64_t f1(const ptree<std::pair<uint64_t, uint64_t>> &_x,
                     uint64_t x0_, const tree &x1_);
  static inline const uint64_t v4 = f1(
      ptree<std::pair<uint64_t, uint64_t>>::pleaf(), UINT64_C(3), tree::leaf());
  /// Round-9 variants, at ptree bool -> bool -> string: branches over a
  /// mapped list; the match a pair's field, invoked in place, whose return
  /// type is joined after its branches, so the lambda takes its parameters
  /// from the branch's Core type; a fold_left step.
  static inline const uint64_t v5 = []() {
    crane::fn<String(ptree<bool>, bool)> w = [](const ptree<bool> &, bool) {
      auto &&_sv = List<uint64_t>::nil().template map<tree>(
          [](uint64_t) { return tree::leaf(); });
      if (std::holds_alternative<typename List<tree>::Nil>(_sv.v())) {
        return String::emptystring();
      } else {
        return String::string0(
            Ascii::ascii0(true, false, false, false, false, true, true, false),
            String::emptystring());
      }
    };
    auto &&_sv = w(ptree<bool>::pleaf(), true);
    if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }();

  template <typename F0> static uint64_t app2(F0 &&w) {
    auto &&_sv = w(ptree<bool>::pleaf(), true);
    if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
      return UINT64_C(1);
    } else {
      return UINT64_C(2);
    }
  }

  static std::pair<uint64_t, crane::fn<String(ptree<bool>, bool)>>
  v10(const List<uint64_t> &l);
  static uint64_t v11(const List<uint64_t> &l);
  static uint64_t v12(const List<uint64_t> &l);
};
