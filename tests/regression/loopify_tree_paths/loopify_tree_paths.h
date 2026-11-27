#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct LoopifyTreePaths {
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

    List<uint64_t> flatten_paths() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of flatten_paths: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_flatten_paths_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_flatten_paths_in_Node_2 {
        uint64_t a1;
        List<uint64_t> _tmp2;
      };

      using _frame = std::variant<_call, _after_flatten_paths_in_Node,
                                  _after_flatten_paths_in_Node_2>;
      List<uint64_t> _result{};
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
            _result = List<uint64_t>::nil();
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_flatten_paths_in_Node{a1,
                                                             crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_flatten_paths_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_flatten_paths_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(
              _after_flatten_paths_in_Node_2{a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f =
              std::move(std::get<_after_flatten_paths_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = List<uint64_t>::cons(a1, _f._tmp2.app(std::move(_result)));
        }
      }
      return _result;
    }

    uint64_t max_path_sum() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of max_path_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_max_path_sum_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_max_path_sum_in_Node_2 {
        uint64_t a1;
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_max_path_sum_in_Node,
                                  _after_max_path_sum_in_Node_2>;
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
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_max_path_sum_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_max_path_sum_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_max_path_sum_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_max_path_sum_in_Node_2{a1, _result});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_max_path_sum_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result = (a1 + std::max(_f._tmp2, _result));
        }
      }
      return _result;
    }

    std::optional<List<uint64_t>> find_path_sum(uint64_t acc,
                                                uint64_t target) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of find_path_sum: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
        uint64_t acc;
      };

      struct _after_find_path_sum_in_Node {
        uint64_t a1;
        const tree *a2;
        uint64_t new_acc;
      };

      struct _after_find_path_sum_in_None {
        uint64_t a1;
      };

      using _frame = std::variant<_call, _after_find_path_sum_in_Node,
                                  _after_find_path_sum_in_None>;
      std::optional<List<uint64_t>> _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self, acc});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          uint64_t acc = _f.acc;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            if (acc == target) {
              _result =
                  std::make_optional<List<uint64_t>>(List<uint64_t>::nil());
            } else {
              _result = std::optional<List<uint64_t>>();
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            uint64_t new_acc = (acc + a1);
            _stack.emplace_back(
                _after_find_path_sum_in_Node{a1, crane_raw(a2), new_acc});
            _stack.emplace_back(_call{crane_raw(a0), new_acc});
          }
        } else if (
                std::holds_alternative<_after_find_path_sum_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_find_path_sum_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          uint64_t new_acc = _f.new_acc;
          std::optional<List<uint64_t>> _tmp2 = std::move(_result);
          if (_tmp2.has_value()) {
            const List<uint64_t> &path = *_tmp2;
            _result = std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            _stack.emplace_back(_after_find_path_sum_in_None{a1});
            _stack.emplace_back(_call{_f.a2, new_acc});
          }
        } else {
          auto _f = std::move(std::get<_after_find_path_sum_in_None>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          std::optional<List<uint64_t>> _tmp1 = std::move(_result);
          if (_tmp1.has_value()) {
            const List<uint64_t> &path = *_tmp1;
            _result = std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            _result = std::optional<List<uint64_t>>();
          }
        }
      }
      return _result;
    }

    uint64_t count_paths_sum(uint64_t target) const {
      return this->count_paths_sum_aux(UINT64_C(0), target);
    }

    uint64_t count_paths_sum_aux(uint64_t acc, uint64_t target) const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of count_paths_sum_aux:
      // _call frames are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
        uint64_t acc;
      };

      struct _after_count_paths_sum_aux_in_Node {
        const tree *a2;
        uint64_t new_acc;
      };

      struct _after_count_paths_sum_aux_in_Node_2 {
        uint64_t _tmp2;
      };

      using _frame = std::variant<_call, _after_count_paths_sum_aux_in_Node,
                                  _after_count_paths_sum_aux_in_Node_2>;
      uint64_t _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self, acc});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const tree *_self = _f._self;
          uint64_t acc = _f.acc;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            if (acc == target) {
              _result = UINT64_C(1);
            } else {
              _result = UINT64_C(0);
            }
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            uint64_t new_acc = (acc + a1);
            _stack.emplace_back(
                _after_count_paths_sum_aux_in_Node{crane_raw(a2), new_acc});
            _stack.emplace_back(_call{crane_raw(a0), new_acc});
          }
        } else if (std::holds_alternative<_after_count_paths_sum_aux_in_Node>(
                       _popped)) {
          auto _f =
              std::move(std::get<_after_count_paths_sum_aux_in_Node>(_popped));
          _stack.pop_back();
          const tree &a2 = *_f.a2;
          uint64_t new_acc = _f.new_acc;
          _stack.emplace_back(_after_count_paths_sum_aux_in_Node_2{_result});
          _stack.emplace_back(_call{_f.a2, new_acc});
        } else {
          auto _f = std::move(
              std::get<_after_count_paths_sum_aux_in_Node_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 + _result);
        }
      }
      return _result;
    }

    List<List<uint64_t>> paths() const {
      const tree *_self = this;

      // Explicit stack replaces the non-tail recursion of paths: _call frames
      // are pending calls, _after frames resume a caller.
      struct _call {
        const tree *_self;
      };

      struct _after_paths_in_Node {
        uint64_t a1;
        const tree *a2;
      };

      struct _after_paths_in_Node_2 {
        uint64_t a1;
        List<List<uint64_t>> _tmp2;
      };

      using _frame =
          std::variant<_call, _after_paths_in_Node, _after_paths_in_Node_2>;
      List<List<uint64_t>> _result{};
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
            _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                                 List<List<uint64_t>>::nil());
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_after_paths_in_Node{a1, crane_raw(a2)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_paths_in_Node>(_popped)) {
          auto _f = std::move(std::get<_after_paths_in_Node>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          const tree &a2 = *_f.a2;
          _stack.emplace_back(_after_paths_in_Node_2{a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a2});
        } else {
          auto _f = std::move(std::get<_after_paths_in_Node_2>(_popped));
          _stack.pop_back();
          uint64_t a1 = _f.a1;
          _result =
              map_cons(a1, std::move(_f._tmp2)).app(
                  map_cons(a1, std::move(_result)));
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

  static List<List<uint64_t>> map_cons(uint64_t x,
                                       const List<List<uint64_t>> &ll);

  struct bool_tree {
    // TYPES
    struct BLeaf {
      uint64_t a0;
    };

    struct BNode {
      std::shared_ptr<bool_tree> a0;
      std::shared_ptr<bool_tree> a1;
    };

    using variant_t = std::variant<BLeaf, BNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    bool_tree() {}

    explicit bool_tree(BLeaf _v) : v_(std::move(_v)) {}

    explicit bool_tree(BNode _v) : v_(std::move(_v)) {}

    static bool_tree bleaf(uint64_t a0) { return bool_tree(BLeaf{a0}); }

    static bool_tree bnode(crane::shared_child_slot<bool_tree> a0,
                           crane::shared_child_slot<bool_tree> a1) {
      return bool_tree(BNode{a0.take(), a1.take()});
    }

    // MANIPULATORS
    ~bool_tree() {
      // Release the children this node alone owns in a loop, not recursively,
      // so a deep value cannot overflow the stack.
      if (std::holds_alternative<BLeaf>(v_mut())) {
        return;
      }
      if (auto *_alt = std::get_if<BNode>(&v_mut())) {
        if (!((_alt->a0 && _alt->a0.use_count() == 1) ||
              (_alt->a1 && _alt->a1.use_count() == 1))) {
          return;
        }
      }
      crane::small_vector<std::shared_ptr<bool_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BNode>(&_v)) {
          if (_alt->a0 && _alt->a0.use_count() == 1) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1 && _alt->a1.use_count() == 1) {
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

    bool_tree(const bool_tree &) = default;
    bool_tree &operator=(const bool_tree &) = default;
    bool_tree(bool_tree &&) = default;
    bool_tree &operator=(bool_tree &&) = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, const uint64_t &>
    bool and_search(F0 &&p) const {
      const bool_tree *_self = this;

      // Explicit stack replaces the non-tail recursion of and_search: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bool_tree *_self;
      };

      struct _after_and_search_in_BNode {
        const bool_tree *a1;
      };

      struct _after_and_search_in_BNode_2 {
        bool _tmp2;
      };

      using _frame = std::variant<_call, _after_and_search_in_BNode,
                                  _after_and_search_in_BNode_2>;
      bool _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_after_and_search_in_BNode{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_and_search_in_BNode>(_popped)) {
          auto _f = std::move(std::get<_after_and_search_in_BNode>(_popped));
          _stack.pop_back();
          const bool_tree &a1 = *_f.a1;
          _stack.emplace_back(_after_and_search_in_BNode_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_and_search_in_BNode_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 && _result);
        }
      }
      return _result;
    }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, const uint64_t &>
    bool or_search(F0 &&p) const {
      const bool_tree *_self = this;

      // Explicit stack replaces the non-tail recursion of or_search: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bool_tree *_self;
      };

      struct _after_or_search_in_BNode {
        const bool_tree *a1;
      };

      struct _after_or_search_in_BNode_2 {
        bool _tmp2;
      };

      using _frame = std::variant<_call, _after_or_search_in_BNode,
                                  _after_or_search_in_BNode_2>;
      bool _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_after_or_search_in_BNode{crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_after_or_search_in_BNode>(_popped)) {
          auto _f = std::move(std::get<_after_or_search_in_BNode>(_popped));
          _stack.pop_back();
          const bool_tree &a1 = *_f.a1;
          _stack.emplace_back(_after_or_search_in_BNode_2{_result});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f = std::move(std::get<_after_or_search_in_BNode_2>(_popped));
          _stack.pop_back();
          _result = (_f._tmp2 || _result);
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      return this->template bool_tree_rect<T1>(f, f0);
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, const uint64_t &>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      // Explicit stack replaces the non-tail recursion of bool_tree_rect: _call
      // frames are pending calls, _after frames resume a caller.
      struct _call {
        const bool_tree *_self;
      };

      struct _after_bool_tree_rect_in_BNode {
        std::shared_ptr<bool_tree> a0;
        const bool_tree *a1;
      };

      struct _after_bool_tree_rect_in_BNode_2 {
        std::shared_ptr<bool_tree> a0;
        const bool_tree *a1;
        T1 _tmp2;
      };

      using _frame = std::variant<_call, _after_bool_tree_rect_in_BNode,
                                  _after_bool_tree_rect_in_BNode_2>;
      T1 _result{};
      crane::small_vector<_frame> _stack;
      _stack.emplace_back(_call{_self});
      while (!_stack.empty()) {
        _frame &_popped = _stack.back();
        if (std::holds_alternative<_call>(_popped)) {
          auto _f = std::move(std::get<_call>(_popped));
          _stack.pop_back();
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(
                _after_bool_tree_rect_in_BNode{a0, crane_raw(a1)});
            _stack.emplace_back(_call{crane_raw(a0)});
          }
        } else if (
                std::holds_alternative<_after_bool_tree_rect_in_BNode>(_popped)) {
          auto _f =
              std::move(std::get<_after_bool_tree_rect_in_BNode>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_tree> a0 = std::move(_f.a0);
          const bool_tree &a1 = *_f.a1;
          _stack.emplace_back(_after_bool_tree_rect_in_BNode_2{
              std::move(a0), &a1, std::move(_result)});
          _stack.emplace_back(_call{_f.a1});
        } else {
          auto _f =
              std::move(std::get<_after_bool_tree_rect_in_BNode_2>(_popped));
          _stack.pop_back();
          std::shared_ptr<bool_tree> a0 = std::move(_f.a0);
          const bool_tree &a1 = *_f.a1;
          _result = f0(*a0, std::move(_f._tmp2), a1, std::move(_result));
        }
      }
      return _result;
    }
  };
};
