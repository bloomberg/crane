#ifndef INCLUDED_LOOPIFY_TREE_PATHS
#define INCLUDED_LOOPIFY_TREE_PATHS

#include "crane_fn.h"
#include "small_vector.h"
#include <algorithm>
#include <any>
#include <atomic>
#include <memory>
#include <optional>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
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
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
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

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
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

    List<uint64_t> flatten_paths() const {
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
        List<uint64_t> _result;
        uint64_t a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      List<uint64_t> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified flatten_paths: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<uint64_t>::nil();
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
          _result = List<uint64_t>::cons(
              _f.a1, std::move(_result).app(std::move(_f._result)));
        }
      }
      return _result;
    }

    uint64_t max_path_sum() const {
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
      /// Loopified max_path_sum: _Enter -> _After_Node -> _Combine_Node.
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
          _result =
              (_f.a1 + std::max(std::move(_result), std::move(_f._result)));
        }
      }
      return _result;
    }

    std::optional<List<uint64_t>> find_path_sum(uint64_t acc,
                                                uint64_t target) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        uint64_t acc;
      };

      /// _Cont2: saves [a1], resumes after recursive call, then processes rest.
      struct _Cont2 {
        uint64_t a1;
      };

      /// _Cont_Node: saves [a1, a2, new_acc], resumes after recursive call,
      /// then processes rest.
      struct _Cont_Node {
        uint64_t a1;
        std::shared_ptr<tree> a2;
        uint64_t new_acc;
      };

      using _Frame = std::variant<_Enter, _Cont2, _Cont_Node>;
      std::optional<List<uint64_t>> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, acc});
      /// Loopified find_path_sum: _Enter -> _Cont2 -> _Cont_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_Cont_Node{a1, a2, new_acc});
            _stack.emplace_back(_Enter{crane_raw(a0), new_acc});
          }
        } else if (std::holds_alternative<_Cont2>(_frame)) {
          auto _f = std::move(std::get<_Cont2>(_frame));
          uint64_t a1 = _f.a1;
          auto _cs1 = std::move(_result);
          if (_cs1.has_value()) {
            const List<uint64_t> &path = *_cs1;
            _result = std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            _result = std::optional<List<uint64_t>>();
          }
        } else {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          uint64_t a1 = _f.a1;
          std::shared_ptr<tree> a2 = std::move(_f.a2);
          uint64_t new_acc = _f.new_acc;
          auto _cs = std::move(_result);
          if (_cs.has_value()) {
            const List<uint64_t> &path = *_cs;
            _result = std::make_optional<List<uint64_t>>(
                List<uint64_t>::cons(a1, path));
          } else {
            _stack.emplace_back(_Cont2{a1});
            _stack.emplace_back(_Enter{crane_raw(a2), new_acc});
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

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        uint64_t acc;
      };

      /// _After_Node: saves [a0, new_acc], dispatches next recursive call.
      struct _After_Node {
        tree *a0;
        uint64_t new_acc;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, acc});
      /// Loopified count_paths_sum_aux: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
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
            _stack.emplace_back(_After_Node{crane_raw(a0), new_acc});
            _stack.emplace_back(_Enter{crane_raw(a2), new_acc});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0, _f.new_acc});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        }
      }
      return _result;
    }

    List<List<uint64_t>> paths() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0, a1_0, a1_1], dispatches next recursive call.
      struct _After_Node {
        tree *a0;
        uint64_t a1_0;
        uint64_t a1_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        List<List<uint64_t>> _result;
        uint64_t a1_0;
        uint64_t a1_1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      List<List<uint64_t>> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified paths: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree::Leaf>(_sv.v())) {
            _result = List<List<uint64_t>>::cons(List<uint64_t>::nil(),
                                                 List<List<uint64_t>>::nil());
          } else {
            const auto &[a0, a1, a2] = std::get<typename tree::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), a1, a1});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(
              _Combine_Node{std::move(_result), _f.a1_0, _f.a1_1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = map_cons(_f.a1_1, std::move(_result))
                        .app(map_cons(_f.a1_0, std::move(_f._result)));
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

    static bool_tree bnode(bool_tree a0, bool_tree a1) {
      return bool_tree(BNode{std::make_shared<bool_tree>(std::move(a0)),
                             std::make_shared<bool_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~bool_tree() {
      crane::small_vector<std::shared_ptr<bool_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<BNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
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

    bool_tree(const bool_tree &) = default;
    bool_tree &operator=(const bool_tree &) = default;
    bool_tree(bool_tree &&) noexcept = default;
    bool_tree &operator=(bool_tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
    bool and_search(F0 &&p) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [a0], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *a0;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        bool _result;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      bool _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified and_search: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(_Combine_BNode{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = (std::move(_result) && std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename F0>
      requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
    bool or_search(F0 &&p) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [a0], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *a0;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        bool _result;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      bool _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified or_search: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = p(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(_Combine_BNode{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = (std::move(_result) || std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, bool_tree &, T1 &, bool_tree &,
                                     T1 &>
    T1 bool_tree_rec(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *a0_0;
        bool_tree a1;
        bool_tree a0_1;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        std::decay_t<T1> _result;
        bool_tree a1;
        bool_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_tree_rec: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(_Combine_BNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, bool_tree &, T1 &, bool_tree &,
                                     T1 &>
    T1 bool_tree_rect(F0 &&f, F1 &&f0) const {
      const bool_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const bool_tree *_self;
      };

      /// _After_BNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_BNode {
        bool_tree *a0_0;
        bool_tree a1;
        bool_tree a0_1;
      };

      /// _Combine_BNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_BNode {
        std::decay_t<T1> _result;
        bool_tree a1;
        bool_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_BNode, _Combine_BNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified bool_tree_rect: _Enter -> _After_BNode -> _Combine_BNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const bool_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename bool_tree::BLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename bool_tree::BLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] = std::get<typename bool_tree::BNode>(_sv.v());
            _stack.emplace_back(_After_BNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_BNode>(_frame)) {
          auto _f = std::move(std::get<_After_BNode>(_frame));
          _stack.emplace_back(_Combine_BNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_BNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };
};

#endif // INCLUDED_LOOPIFY_TREE_PATHS
