#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

struct Z {};

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
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: the generated program as shrunk by ephyra (hand
/// reduction lost the trigger).
///
/// g1 recurses on a tree; its Node branch calls a local fixpoint whose
/// base case and initial accumulator both call g1 on the left subtree.
/// The explicit-stack frames read acc29, declared only as a member of
/// _after_g1_in_Nil: "use of undeclared identifier 'acc29'".  The frame
/// kept the local _x2 a pattern bound at acc29's level in the branch the
/// continuation ran in; it now keeps the local bound at the site the
/// recursion plan names (as loopify_rematch_frame_binder).

template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct FrameBinderLocalFixAcc {
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

    int64_t g1(bool _x, int64_t a2) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of g1: _call frames are
      // pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
        bool _x;
        int64_t a2;
      };

      struct _after_g1_in_Nil {
        int64_t acc29;
      };

      struct _after_g1_in_Nil_2 {
        int64_t acc29;
      };

      struct _after_g1_in_Nil_3 {
        int64_t acc29;
      };

      struct _after_g1_in_Zneg {
        const tree *a0;
        List<uint64_t> l28;
      };

      using _frame = std::variant<_call, _after_g1_in_Nil, _after_g1_in_Nil_2,
                                  _after_g1_in_Nil_3, _after_g1_in_Zneg>;
      int64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self, _x, a2});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          bool _x = _f._x;
          int64_t a2 = _f.a2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = INT64_C(0);
          } else {
            const auto &[a0, _, _] = std::get<typename tree::Node>(_sv.v());
            List<uint64_t> l28 = List<uint64_t>::nil();
            int64_t acc29;
            if (a2 == 0) {
              acc29 = INT64_C(0);
              {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        l28.v_mut())) {
                  _stack.emplace_back(_after_g1_in_Nil{acc29});
                  _stack.emplace_back(_call{crane_raw(a0), true, INT64_C(0)});
                } else {
                  _result = INT64_C(0);
                }
              }
            } else if (a2 > 0) {
              unsigned int _x2 = static_cast<unsigned int>(a2);
              acc29 = INT64_C(0);
              {
                if (std::holds_alternative<typename List<uint64_t>::Nil>(
                        l28.v_mut())) {
                  _stack.emplace_back(_after_g1_in_Nil_2{acc29});
                  _stack.emplace_back(_call{crane_raw(a0), true, INT64_C(0)});
                } else {
                  _result = INT64_C(0);
                }
              }
            } else {
              unsigned int _x2 = static_cast<unsigned int>(-a2);
              _stack.emplace_back(
                  _after_g1_in_Zneg{crane_raw(a0), std::move(l28)});
              _stack.emplace_back(_call{crane_raw(a0), true, INT64_C(0)});
            }
          }
        } else if (std::holds_alternative<_after_g1_in_Nil>(_popped)) {
          auto _f = std::move(std::get<_after_g1_in_Nil>(_popped));
          _stack.pop_back();
          int64_t acc29 = _f.acc29;
          _result = std::min(_result, acc29);
        } else if (std::holds_alternative<_after_g1_in_Nil_2>(_popped)) {
          auto _f = std::move(std::get<_after_g1_in_Nil_2>(_popped));
          _stack.pop_back();
          int64_t acc29 = _f.acc29;
          _result = std::min(_result, acc29);
        } else if (std::holds_alternative<_after_g1_in_Nil_3>(_popped)) {
          auto _f = std::move(std::get<_after_g1_in_Nil_3>(_popped));
          _stack.pop_back();
          int64_t acc29 = _f.acc29;
          _result = std::min(_result, acc29);
        } else {
          auto _f = std::move(std::get<_after_g1_in_Zneg>(_popped));
          _stack.pop_back();
          const tree &a0 = *_f.a0;
          List<uint64_t> l28 = std::move(_f.l28);
          auto acc29 = _result;
          if (std::holds_alternative<typename List<uint64_t>::Nil>(l28.v_mut())) {
            _stack.emplace_back(_after_g1_in_Nil_3{acc29});
            _stack.emplace_back(_call{_f.a0, true, INT64_C(0)});
          } else {
            _result = INT64_C(0);
          }
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
          _stack.emplace_back(_after_tree_obs_in_Node_2{a1, _result});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_tree_obs_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          auto _once1 = _f._tmp2 * UINT64_C(7) + a1 + _result * UINT64_C(3);
          _result = (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
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

  struct pt {
    uint64_t px;
    bool py;
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
            auto _once1 = a + _tcI0::sz(x);
            return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
          },
          UINT64_C(0));
    }
  };

  template <typename _tcI0, typename _tcI1, typename T1, typename T2>
    requires Sz<_tcI0, T1> && Sz<_tcI1, T2>
  struct sz_pair {
    static uint64_t sz(std::pair<T1, T2> p) {
      auto _once1 = _tcI0::sz(std::move(p.first)) * UINT64_C(3) +
                    _tcI1::sz(std::move(p.second));
      return (UINT64_C(10007) ? _once1 % UINT64_C(10007) : _once1);
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

    uint64_t psize() const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of psize: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
      };

      struct _after_psize_in_PNode {
        const ptree<A> *a2;
      };

      struct _after_psize_in_PNode_2 {
        uint64_t _tmp2;
      };

      using _frame =
          std::variant<_call, _after_psize_in_PNode, _after_psize_in_PNode_2>;
      uint64_t _result{};
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
            _result = UINT64_C(0);
          } else {
            const auto &[a0, _, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_after_psize_in_PNode{crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_psize_in_PNode>(_popped)) {
          auto _f = std::move(std::get<_after_psize_in_PNode>(_popped));
          _stack.pop_back();
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(_after_psize_in_PNode_2{_result});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_psize_in_PNode_2>(_popped));
          _stack.pop_back();
          _result = ((_f._tmp2 + _result) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, T1 &&, A &>
    T1 pfold(F0 &&f, T1 acc) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of pfold: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
        T1 acc;
      };

      struct _after_pfold_in_PNode {
        A a1;
        const ptree<A> *a2;
      };

      using _frame = std::variant<_call, _after_pfold_in_PNode>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self, std::move(acc)});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const ptree<A> *_self = _f._self;
          auto acc = std::move(_f.acc);
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ptree<A>::PLeaf>(_sv.v())) {
            _result = std::move(acc);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_after_pfold_in_PNode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0), std::move(acc)});
          }
        } else {
          auto _f = std::move(std::get<_after_pfold_in_PNode>(_popped));
          _stack.pop_back();
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(_call{_f.a2, f(std::move(_result), a1)});
        }
      }
      return _result;
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    ptree<T1> pmap(F0 &&f) const {
      const ptree<A> *_self = this;

      // Explicit stack replaces the non-tail recursion of pmap: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const ptree<A> *_self;
      };

      struct _after_pmap_in_PNode {
        A a1;
        const ptree<A> *a2;
      };

      struct _after_pmap_in_PNode_2 {
        A a1;
        ptree<T1> _tmp2;
      };

      using _frame =
          std::variant<_call, _after_pmap_in_PNode, _after_pmap_in_PNode_2>;
      ptree<T1> _result{};
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
            _result = ptree<T1>::pleaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename ptree<A>::PNode>(_sv.v());
            _stack.emplace_back(_after_pmap_in_PNode{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_pmap_in_PNode>(_popped)) {
          auto _f = std::move(std::get<_after_pmap_in_PNode>(_popped));
          _stack.pop_back();
          auto a1 = std::move(_f.a1);
          const ptree<A> &a2 = *_f.a2;
          _stack.emplace_back(
              _after_pmap_in_PNode_2{std::move(a1), std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_pmap_in_PNode_2>(_popped));
          _stack.pop_back();
          auto a1 = std::move(_f.a1);
          _result =
              ptree<T1>::pnode(std::move(_f._tmp2), f(a1), std::move(_result));
        }
      }
      return _result;
    }

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

  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct SCons_ {
      uint64_t a0;
      CraneS0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream sconst(uint64_t n);
  static stream sfrom(uint64_t n);
  static stream smap(const crane::fn<uint64_t(uint64_t)> &f, const stream &s);
  static List<uint64_t> stake(uint64_t k, const stream &s);
  static uint64_t shd(const stream &s);
  static stream stl(const stream &s);
  static constexpr uint64_t t_1 = UINT64_C(0);
};
