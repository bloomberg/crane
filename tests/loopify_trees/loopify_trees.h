#ifndef INCLUDED_LOOPIFY_TREES
#define INCLUDED_LOOPIFY_TREES

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

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
    const List *_loop_self = this;
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

struct LoopifyTrees {
  template <typename A> struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::shared_ptr<tree<A>> l;
      A x;
      std::shared_ptr<tree<A>> r;
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

    template <typename _U> tree(const tree<_U> &_other) {
      if (std::holds_alternative<typename tree<_U>::Leaf>(_other.v())) {
        this->v_ = Leaf{};
      } else {
        const auto &[l, x, r] = std::get<typename tree<_U>::Node>(_other.v());
        this->v_ = Node{
            l ? std::make_shared<tree<A>>(*l) : nullptr,
            [&]() -> A {
              if constexpr (std::is_same_v<_U, std::any>) {
                if (x.type() == typeid(A))
                  return std::any_cast<A>(x);
                if constexpr (requires {
                                typename A::first_type;
                                typename A::second_type;
                              }) {
                  const auto &[_k, _v] =
                      std::any_cast<std::pair<std::any, std::any>>(x);
                  return A{
                      [&]() -> typename A::first_type {
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
                return std::any_cast<A>(x);
              } else
                return A(x);
            }(),
            r ? std::make_shared<tree<A>>(*r) : nullptr};
      }
    }

    static tree<A> leaf() { return tree<A>(Leaf{}); }

    static tree<A> node(tree<A> l, A x, tree<A> r) {
      return tree<A>(Node{std::make_shared<tree<A>>(std::move(l)), std::move(x),
                          std::make_shared<tree<A>>(std::move(r))});
    }

    // MANIPULATORS
    ~tree() {
      crane::small_vector<std::shared_ptr<tree<A>>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Node>(&_v)) {
          if (_alt->l) {
            _stack.push_back(std::move(_alt->l));
          }
          if (_alt->r) {
            _stack.push_back(std::move(_alt->r));
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

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, A &>
    tree<T1> tree_map(F0 &&f) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0, a1], dispatches next recursive call.
      struct _After_Node {
        tree<A> *a0;
        std::decay_t<decltype(std::declval<F0 &>()(std::declval<A &>()))> a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree<T1> _result;
        std::decay_t<decltype(std::declval<F0 &>()(std::declval<A &>()))> a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree<T1> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_map: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = tree<T1>::leaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), f(a1)});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f.a1});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result =
              tree<T1>::node(std::move(_result), _f.a1, std::move(_f._result));
        }
      }
      return _result;
    }

    bool mirror_equal(const tree<A> &t2) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        const tree<A> *t2;
      };

      /// _After_Node: saves [a0, a20, _s2], dispatches next recursive call.
      struct _After_Node {
        tree<A> *a0;
        const tree<A> *a20;
        std::decay_t<decltype(true)> _s2;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        bool _result;
        std::decay_t<decltype(true)> _s1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      bool _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, &t2});
      /// Loopified mirror_equal: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          const tree<A> &t2 = *_f.t2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
              _result = true;
            } else {
              _result = false;
            }
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            if (std::holds_alternative<typename tree<A>::Leaf>(t2.v())) {
              _result = false;
            } else {
              const auto &[a00, a10, a20] =
                  std::get<typename tree<A>::Node>(t2.v());
              _stack.emplace_back(
                  _After_Node{crane_raw(a0), crane_raw(a20), true});
              _stack.emplace_back(_Enter{crane_raw(a2), crane_raw(a00)});
            }
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result), _f._s2});
          _stack.emplace_back(_Enter{_f.a0, _f.a20});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((std::move(_result) && std::move(_f._result)) && _f._s1);
        }
      }
      return _result;
    }

    List<A> tree_to_list() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0, a1], dispatches next recursive call.
      struct _After_Node {
        tree<A> *a0;
        std::decay_t<A> a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        List<A> _result;
        std::decay_t<A> a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      List<A> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_to_list: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = List<A>::nil();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), a1});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(
              _Combine_Node{std::move(_result), std::move(_f.a1)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = std::move(_result).app(
              List<A>::cons(std::move(_f.a1), std::move(_f._result)));
        }
      }
      return _result;
    }

    uint64_t count_leaves() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0], dispatches next recursive call.
      struct _After_Node {
        tree<A> *a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified count_leaves: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(1);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        }
      }
      return _result;
    }

    A rightmost(A default0) const {
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return default0;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
          auto &&_sv = *a2;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            return a1;
          } else {
            _loop_self = crane_raw(a2);
          }
        }
      }
    }

    A leftmost(A default0) const {
      const tree *_loop_self = this;
      while (true) {
        auto &&_sv = *_loop_self;
        if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
          return default0;
        } else {
          const auto &[a0, a1, a2] = std::get<typename tree<A>::Node>(_sv.v());
          auto &&_sv = *a0;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            return a1;
          } else {
            _loop_self = crane_raw(a0);
          }
        }
      }
    }

    template <typename T1> bool same_shape(const tree<T1> &t2) const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
        const tree<T1> *t2;
      };

      /// _Cont_Node: saves [a2, a20], resumes after recursive call, then
      /// processes rest.
      struct _Cont_Node {
        std::shared_ptr<tree<A>> a2;
        const tree<T1> *a20;
      };

      using _Frame = std::variant<_Enter, _Cont_Node>;
      bool _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, &t2});
      /// Loopified same_shape: _Enter -> _Cont_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          const tree<T1> &t2 = *_f.t2;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
              _result = true;
            } else {
              _result = false;
            }
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            if (std::holds_alternative<typename tree<T1>::Leaf>(t2.v())) {
              _result = false;
            } else {
              const auto &[a00, a10, a20] =
                  std::get<typename tree<T1>::Node>(t2.v());
              _stack.emplace_back(_Cont_Node{a2, crane_raw(a20)});
              _stack.emplace_back(_Enter{crane_raw(a0), crane_raw(a00)});
            }
          }
        } else {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          const tree<T1> &a20 = *_f.a20;
          bool _rc1 = std::move(_result);
          if (_rc1) {
            _stack.emplace_back(_Enter{crane_raw(a2), &a20});
          } else {
            _result = false;
          }
        }
      }
      return _result;
    }

    tree<A> mirror() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a2, a1], dispatches next recursive call.
      struct _After_Node {
        tree<A> *a2;
        std::decay_t<A> a1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        tree<A> _result;
        std::decay_t<A> a1;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      tree<A> _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified mirror: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = tree<A>::leaf();
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a2), a1});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(
              _Combine_Node{std::move(_result), std::move(_f.a1)});
          _stack.emplace_back(_Enter{_f.a2});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = tree<A>::node(std::move(_result), std::move(_f.a1),
                                  std::move(_f._result));
        }
      }
      return _result;
    }

    uint64_t tree_size() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _After_Node: saves [a0], dispatches next recursive call.
      struct _After_Node {
        tree<A> *a0;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_Node, _Combine_Node>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_size: _Enter -> _After_Node -> _Combine_Node.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = ((std::move(_result) + std::move(_f._result)) + 1);
        }
      }
      return _result;
    }

    uint64_t tree_height() const {
      const tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const tree *_self;
      };

      /// _Cont_Node: saves [a2], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Node {
        std::shared_ptr<tree<A>> a2;
      };

      /// _Cont_Node_1: saves [lh], resumes after recursive call, then processes
      /// rest.
      struct _Cont_Node_1 {
        uint64_t lh;
      };

      using _Frame = std::variant<_Enter, _Cont_Node, _Cont_Node_1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified tree_height: _Enter -> _Cont_Node -> _Cont_Node_1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_Cont_Node{a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_Node>(_frame)) {
          auto _f = std::move(std::get<_Cont_Node>(_frame));
          std::shared_ptr<tree<A>> a2 = std::move(_f.a2);
          uint64_t lh = std::move(_result);
          _stack.emplace_back(_Cont_Node_1{lh});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_Node_1>(_frame));
          uint64_t lh = _f.lh;
          uint64_t rh = std::move(_result);
          _result = ((lh <= rh ? rh : lh) + 1);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
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
        tree<A> *a0_0;
        tree<A> a2;
        std::decay_t<A> a1;
        tree<A> a0_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        tree<A> a2;
        std::decay_t<A> a1;
        tree<A> a0;
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
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result),
                                            std::move(_f.a2), std::move(_f.a1),
                                            std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, tree<A> &, T1 &, A &, tree<A> &,
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
        tree<A> *a0_0;
        tree<A> a2;
        std::decay_t<A> a1;
        tree<A> a0_1;
      };

      /// _Combine_Node: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Node {
        std::decay_t<T1> _result;
        tree<A> a2;
        std::decay_t<A> a1;
        tree<A> a0;
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
          if (std::holds_alternative<typename tree<A>::Leaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2] =
                std::get<typename tree<A>::Node>(_sv.v());
            _stack.emplace_back(_After_Node{crane_raw(a0), *a2, a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_Node>(_frame)) {
          auto _f = std::move(std::get<_After_Node>(_frame));
          _stack.emplace_back(_Combine_Node{std::move(_result),
                                            std::move(_f.a2), std::move(_f.a1),
                                            std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Node>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f.a2), std::move(_f._result));
        }
      }
      return _result;
    }
  };

  static uint64_t tree_sum(const tree<uint64_t> &t);
  static uint64_t leaf_sum(const tree<uint64_t> &t);
  static tree<uint64_t> insert_bst(uint64_t x, const tree<uint64_t> &t);
  static uint64_t count_paths(const tree<uint64_t> &t, uint64_t n);
  static uint64_t sum_of_max_branches(const tree<uint64_t> &t);

  struct ternary {
    // TYPES
    struct TLeaf {};

    struct TNode {
      std::shared_ptr<ternary> a0;
      std::shared_ptr<ternary> a1;
      std::shared_ptr<ternary> a2;
      uint64_t a3;
    };

    using variant_t = std::variant<TLeaf, TNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    ternary() {}

    explicit ternary(TLeaf _v) : v_(_v) {}

    explicit ternary(TNode _v) : v_(std::move(_v)) {}

    static ternary tleaf() { return ternary(TLeaf{}); }

    static ternary tnode(ternary a0, ternary a1, ternary a2, uint64_t a3) {
      return ternary(TNode{std::make_shared<ternary>(std::move(a0)),
                           std::make_shared<ternary>(std::move(a1)),
                           std::make_shared<ternary>(std::move(a2)), a3});
    }

    // MANIPULATORS
    ~ternary() {
      crane::small_vector<std::shared_ptr<ternary>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<TNode>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
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

    ternary(const ternary &) = default;
    ternary &operator=(const ternary &) = default;
    ternary(ternary &&) noexcept = default;
    ternary &operator=(ternary &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t ternary_depth() const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _Cont_TNode: saves [a1, a2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_TNode {
        std::shared_ptr<ternary> a1;
        std::shared_ptr<ternary> a2;
      };

      /// _Cont_TNode_1: saves [a2, d1], resumes after recursive call, then
      /// processes rest.
      struct _Cont_TNode_1 {
        std::shared_ptr<ternary> a2;
        uint64_t d1;
      };

      /// _Cont_TNode_2: saves [d1, d2], resumes after recursive call, then
      /// processes rest.
      struct _Cont_TNode_2 {
        uint64_t d1;
        uint64_t d2;
      };

      using _Frame =
          std::variant<_Enter, _Cont_TNode, _Cont_TNode_1, _Cont_TNode_2>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_depth: _Enter -> _Cont_TNode -> _Cont_TNode_1 ->
      /// _Cont_TNode_2.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_Cont_TNode{a1, a2});
            _stack.emplace_back(_Enter{crane_raw(a0)});
          }
        } else if (std::holds_alternative<_Cont_TNode>(_frame)) {
          auto _f = std::move(std::get<_Cont_TNode>(_frame));
          std::shared_ptr<ternary> a1 = std::move(_f.a1);
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t d1 = std::move(_result);
          _stack.emplace_back(_Cont_TNode_1{std::move(a2), d1});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        } else if (std::holds_alternative<_Cont_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_Cont_TNode_1>(_frame));
          std::shared_ptr<ternary> a2 = std::move(_f.a2);
          uint64_t d1 = _f.d1;
          uint64_t d2 = std::move(_result);
          _stack.emplace_back(_Cont_TNode_2{d1, d2});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        } else {
          auto _f = std::move(std::get<_Cont_TNode_2>(_frame));
          uint64_t d1 = _f.d1;
          uint64_t d2 = _f.d2;
          uint64_t d3 = std::move(_result);
          _result = ([&]() -> uint64_t {
            if ((d1 <= d2 ? d2 : d1) <= d3) {
              return d3;
            } else {
              if (d1 <= d2) {
                return d2;
              } else {
                return d1;
              }
            }
          }() + 1);
        }
      }
      return _result;
    }

    uint64_t ternary_sum() const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a1, a0, a3], dispatches next recursive call.
      struct _After_TNode {
        const ternary *a1;
        const ternary *a0;
        uint64_t a3;
      };

      /// _After_TNode_1: saves [_result, a0, a3], dispatches next recursive
      /// call.
      struct _After_TNode_1 {
        uint64_t _result;
        const ternary *a0;
        uint64_t a3;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t a3;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_sum: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(_After_TNode{crane_raw(a1), crane_raw(a0), a3});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{std::move(_result), _f.a0, _f.a3});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(
              _Combine_TNode{_f._result, std::move(_result), _f.a3});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result =
              (_f.a3 + (std::move(_result) + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, ternary &, T1 &,
                                     ternary &, T1 &, uint64_t &>
    T1 ternary_rec(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a1_0, a0_0, a3, a2, a1_1, a0_1], dispatches next
      /// recursive call.
      struct _After_TNode {
        const ternary *a1_0;
        const ternary *a0_0;
        uint64_t a3;
        ternary a2;
        ternary a1_1;
        ternary a0_1;
      };

      /// _After_TNode_1: saves [_result, a0_0, a3, a2, a1, a0_1], dispatches
      /// next recursive call.
      struct _After_TNode_1 {
        std::decay_t<T1> _result;
        const ternary *a0_0;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0_1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_rec: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{crane_raw(a1), crane_raw(a0), a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{
              std::move(_result), _f.a0_0, _f.a3, std::move(_f.a2),
              std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{
              std::move(_f._result), std::move(_result), _f.a3,
              std::move(_f.a2), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_1), std::move(_f.a2),
                       std::move(_f._result_0), _f.a3);
        }
      }
      return _result;
    }

    template <typename T1, typename F1>
      requires std::is_invocable_r_v<T1, F1 &, ternary &, T1 &, ternary &, T1 &,
                                     ternary &, T1 &, uint64_t &>
    T1 ternary_rect(T1 f, F1 &&f0) const {
      const ternary *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const ternary *_self;
      };

      /// _After_TNode: saves [a1_0, a0_0, a3, a2, a1_1, a0_1], dispatches next
      /// recursive call.
      struct _After_TNode {
        const ternary *a1_0;
        const ternary *a0_0;
        uint64_t a3;
        ternary a2;
        ternary a1_1;
        ternary a0_1;
      };

      /// _After_TNode_1: saves [_result, a0_0, a3, a2, a1, a0_1], dispatches
      /// next recursive call.
      struct _After_TNode_1 {
        std::decay_t<T1> _result;
        const ternary *a0_0;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0_1;
      };

      /// _Combine_TNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_TNode {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        uint64_t a3;
        ternary a2;
        ternary a1;
        ternary a0;
      };

      using _Frame =
          std::variant<_Enter, _After_TNode, _After_TNode_1, _Combine_TNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified ternary_rect: _Enter -> _After_TNode -> _After_TNode_1 ->
      /// _Combine_TNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const ternary *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename ternary::TLeaf>(_sv.v())) {
            _result = f;
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename ternary::TNode>(_sv.v());
            _stack.emplace_back(
                _After_TNode{crane_raw(a1), crane_raw(a0), a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        } else if (std::holds_alternative<_After_TNode>(_frame)) {
          auto _f = std::move(std::get<_After_TNode>(_frame));
          _stack.emplace_back(_After_TNode_1{
              std::move(_result), _f.a0_0, _f.a3, std::move(_f.a2),
              std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_TNode_1>(_frame)) {
          auto _f = std::move(std::get<_After_TNode_1>(_frame));
          _stack.emplace_back(_Combine_TNode{
              std::move(_f._result), std::move(_result), _f.a3,
              std::move(_f.a2), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_TNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_1), std::move(_f.a2),
                       std::move(_f._result_0), _f.a3);
        }
      }
      return _result;
    }
  };

  struct rose {
    // TYPES
    struct RNode {
      uint64_t a0;
      std::shared_ptr<List<rose>> a1;
    };

    using variant_t = std::variant<RNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    rose() {}

    explicit rose(RNode _v) : v_(std::move(_v)) {}

    static rose rnode(uint64_t a0, List<rose> a1) {
      return rose(RNode{a0, std::make_shared<List<rose>>(std::move(a1))});
    }

    // MANIPULATORS
    ~rose() {
      crane::small_vector<std::shared_ptr<rose>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<RNode>(&_v)) {
          if (_alt->a1 && _alt->a1.use_count() == 1) {
            std::atomic_thread_fence(std::memory_order_acquire);
            auto *_lp = _alt->a1.get();
            while (
                std::holds_alternative<typename List<rose>::Cons>(_lp->v())) {
              auto &_lc = std::get<typename List<rose>::Cons>(_lp->v_mut());
              _stack.push_back(std::make_shared<rose>(std::move(_lc.a)));
              if (_lc.l && _lc.l.use_count() == 1) {
                std::atomic_thread_fence(std::memory_order_acquire);
                _lp = _lc.l.get();
              } else {
                break;
              }
            }
            _alt->a1.reset();
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

    rose(const rose &) = default;
    rose &operator=(const rose &) = default;
    rose(rose &&) noexcept = default;
    rose &operator=(rose &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t rose_depth() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return (depth_rose_list_fuel(UINT64_C(1000), *a1) + 1);
    }

    List<uint64_t> rose_flatten() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return List<uint64_t>::cons(a0,
                                  flatten_rose_list_fuel(UINT64_C(1000), *a1));
    }

    template <typename F0>
      requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
    rose rose_map(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return rose::rnode(f(a0), map_rose_list_fuel(UINT64_C(1000), f, *a1));
    }

    uint64_t rose_sum() const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return (a0 + sum_rose_list_fuel(UINT64_C(1000), *a1));
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<rose> &>
    T1 rose_rec(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return f(a0, *a1);
    }

    template <typename T1, typename F0>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &, List<rose> &>
    T1 rose_rect(F0 &&f) const {
      const auto &[a0, a1] = std::get<typename rose::RNode>(this->v());
      return f(a0, *a1);
    }
  };

  static uint64_t sum_rose_list_fuel(uint64_t fuel, const List<rose> &cs);

  template <typename F1>
    requires std::is_invocable_r_v<uint64_t, F1 &, uint64_t &>
  static List<rose> map_rose_list_fuel(
      uint64_t fuel, F1 &&f,
      const List<rose> &
          cs) { /// _Enter: captures varying parameters for each recursive call.

    struct _Enter {
      const List<rose> *cs;
      uint64_t fuel;
    };

    /// _After_RNode: saves [a10, g, a00], dispatches next recursive call.
    struct _After_RNode {
      const List<rose> *a10;
      uint64_t g;
      uint64_t a00;
    };

    /// _Combine_RNode: receives partial results, combines with _result from
    /// final call.
    struct _Combine_RNode {
      List<rose> _result;
      uint64_t a00;
    };

    using _Frame = std::variant<_Enter, _After_RNode, _Combine_RNode>;
    List<rose> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&cs, fuel});
    /// Loopified map_rose_list_fuel: _Enter -> _After_RNode -> _Combine_RNode.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<rose> &cs = *_f.cs;
        uint64_t fuel = _f.fuel;
        if (fuel <= 0) {
          _result = List<rose>::nil();
        } else {
          uint64_t g = fuel - 1;
          if (std::holds_alternative<typename List<rose>::Nil>(cs.v())) {
            _result = List<rose>::nil();
          } else {
            const auto &[a0, a1] = std::get<typename List<rose>::Cons>(cs.v());
            const auto &[a00, a10] = std::get<typename rose::RNode>(a0.v());
            _stack.emplace_back(_After_RNode{crane_raw(a10), g, f(a00)});
            _stack.emplace_back(_Enter{crane_raw(a1), g});
          }
        }
      } else if (std::holds_alternative<_After_RNode>(_frame)) {
        auto _f = std::move(std::get<_After_RNode>(_frame));
        _stack.emplace_back(_Combine_RNode{std::move(_result), _f.a00});
        _stack.emplace_back(_Enter{_f.a10, _f.g});
      } else {
        auto _f = std::move(std::get<_Combine_RNode>(_frame));
        _result = List<rose>::cons(rose::rnode(_f.a00, std::move(_result)),
                                   std::move(_f._result));
      }
    }
    return _result;
  }

  static List<uint64_t> flatten_rose_list_fuel(uint64_t fuel,
                                               const List<rose> &cs);
  static uint64_t depth_rose_list_fuel(uint64_t fuel, const List<rose> &cs);
  static tree<uint64_t> tree_max(tree<uint64_t> t1, tree<uint64_t> t2);
  static List<uint64_t> extract_tree_values(const List<tree<uint64_t>> &ts);
  static List<tree<uint64_t>>
  extract_tree_children(const List<tree<uint64_t>> &ts);
  static List<List<uint64_t>>
  tree_levels_fuel(uint64_t fuel, const List<tree<uint64_t>> &trees);
  static List<List<uint64_t>> tree_levels(tree<uint64_t> t);
  static std::pair<uint64_t, uint64_t> count_nodes(const tree<uint64_t> &t);
  static List<List<uint64_t>> append_list_lists(const List<List<uint64_t>> &l1,
                                                List<List<uint64_t>> l2);
  static List<List<uint64_t>> map_cons_to_all(uint64_t x,
                                              const List<List<uint64_t>> &lsts);
  static List<List<uint64_t>> paths(const tree<uint64_t> &t);
  static List<uint64_t> collect_unsorted(const tree<uint64_t> &t);
  static List<uint64_t> insert_sorted(uint64_t x, const List<uint64_t> &l);
  static List<uint64_t> sort_list(const List<uint64_t> &l);
  static List<uint64_t> collect_sorted(const tree<uint64_t> &t);

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, uint64_t &>
  static bool
  or_search(F0 &&p,
            const tree<uint64_t> &t) { /// _Enter: captures varying parameters
                                       /// for each recursive call.

    struct _Enter {
      const tree<uint64_t> *t;
    };

    /// _After2: saves [a0], dispatches next recursive call.
    struct _After2 {
      const tree<uint64_t> *a0;
    };

    /// _Combine1: receives partial results, combines with _result from final
    /// call.
    struct _Combine1 {
      bool _result;
    };

    using _Frame = std::variant<_Enter, _After2, _Combine1>;
    bool _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{&t});
    /// Loopified or_search: _Enter -> _After2 -> _Combine1.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const tree<uint64_t> &t = *_f.t;
        if (std::holds_alternative<typename tree<uint64_t>::Leaf>(t.v())) {
          _result = false;
        } else {
          const auto &[a0, a1, a2] =
              std::get<typename tree<uint64_t>::Node>(t.v());
          if (p(a1)) {
            _result = true;
          } else {
            _stack.emplace_back(_After2{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a2)});
          }
        }
      } else if (std::holds_alternative<_After2>(_frame)) {
        auto _f = std::move(std::get<_After2>(_frame));
        _stack.emplace_back(_Combine1{std::move(_result)});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine1>(_frame));
        _result = (std::move(_result) || std::move(_f._result));
      }
    }
    return _result;
  }

  struct quadtree {
    // TYPES
    struct QLeaf {
      uint64_t a0;
    };

    struct Quad {
      std::shared_ptr<quadtree> a0;
      std::shared_ptr<quadtree> a1;
      std::shared_ptr<quadtree> a2;
      std::shared_ptr<quadtree> a3;
    };

    using variant_t = std::variant<QLeaf, Quad>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    quadtree() {}

    explicit quadtree(QLeaf _v) : v_(std::move(_v)) {}

    explicit quadtree(Quad _v) : v_(std::move(_v)) {}

    static quadtree qleaf(uint64_t a0) { return quadtree(QLeaf{a0}); }

    static quadtree quad(quadtree a0, quadtree a1, quadtree a2, quadtree a3) {
      return quadtree(Quad{std::make_shared<quadtree>(std::move(a0)),
                           std::make_shared<quadtree>(std::move(a1)),
                           std::make_shared<quadtree>(std::move(a2)),
                           std::make_shared<quadtree>(std::move(a3))});
    }

    // MANIPULATORS
    ~quadtree() {
      crane::small_vector<std::shared_ptr<quadtree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<Quad>(&_v)) {
          if (_alt->a0) {
            _stack.push_back(std::move(_alt->a0));
          }
          if (_alt->a1) {
            _stack.push_back(std::move(_alt->a1));
          }
          if (_alt->a2) {
            _stack.push_back(std::move(_alt->a2));
          }
          if (_alt->a3) {
            _stack.push_back(std::move(_alt->a3));
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

    quadtree(const quadtree &) = default;
    quadtree &operator=(const quadtree &) = default;
    quadtree(quadtree &&) noexcept = default;
    quadtree &operator=(quadtree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t quad_depth() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2, a1, a0], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_1: saves [_result, a1, a0], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_depth: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            _result = UINT64_C(0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{crane_raw(a2), crane_raw(a1), crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{std::move(_result), _f.a1, _f.a0});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{_f._result, std::move(_result), _f.a0});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (max4_impl(std::move(_result), _f._result_2, _f._result_1,
                               _f._result_0) +
                     1);
        }
      }
      return _result;
    }

    uint64_t quad_sum() const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2, a1, a0], dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_1: saves [_result, a1, a0], dispatches next recursive
      /// call.
      struct _After_Quad_1 {
        uint64_t _result;
        const quadtree *a1;
        const quadtree *a0;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0], dispatches next
      /// recursive call.
      struct _After_Quad_2 {
        uint64_t _result_0;
        uint64_t _result_1;
        const quadtree *a0;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        uint64_t _result_0;
        uint64_t _result_1;
        uint64_t _result_2;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quad_sum: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(
                _After_Quad{crane_raw(a2), crane_raw(a1), crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{std::move(_result), _f.a1, _f.a0});
          _stack.emplace_back(_Enter{_f.a2});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{_f._result, std::move(_result), _f.a0});
          _stack.emplace_back(_Enter{_f.a1});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(
              _Combine_Quad{_f._result_0, _f._result_1, std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = (std::move(_result) +
                     (_f._result_2 + (_f._result_1 + _f._result_0)));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rec(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2_0;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2_1;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        std::decay_t<T1> _result;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0_1;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rec: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{crane_raw(a2), crane_raw(a1),
                                            crane_raw(a0), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
              std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                            std::move(_f.a3), std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), std::move(_f.a2),
                       std::move(_f._result_1), std::move(_f.a3),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, quadtree &, T1 &, quadtree &,
                                     T1 &, quadtree &, T1 &, quadtree &, T1 &>
    T1 quadtree_rect(F0 &&f, F1 &&f0) const {
      const quadtree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const quadtree *_self;
      };

      /// _After_Quad: saves [a2_0, a1_0, a0_0, a3, a2_1, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad {
        const quadtree *a2_0;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2_1;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_1: saves [_result, a1_0, a0_0, a3, a2, a1_1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_1 {
        std::decay_t<T1> _result;
        const quadtree *a1_0;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1_1;
        quadtree a0_1;
      };

      /// _After_Quad_2: saves [_result_0, _result_1, a0_0, a3, a2, a1, a0_1],
      /// dispatches next recursive call.
      struct _After_Quad_2 {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        const quadtree *a0_0;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0_1;
      };

      /// _Combine_Quad: receives partial results, combines with _result from
      /// final call.
      struct _Combine_Quad {
        std::decay_t<T1> _result_0;
        std::decay_t<T1> _result_1;
        std::decay_t<T1> _result_2;
        quadtree a3;
        quadtree a2;
        quadtree a1;
        quadtree a0;
      };

      using _Frame = std::variant<_Enter, _After_Quad, _After_Quad_1,
                                  _After_Quad_2, _Combine_Quad>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified quadtree_rect: _Enter -> _After_Quad -> _After_Quad_1 ->
      /// _After_Quad_2 -> _Combine_Quad.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const quadtree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename quadtree::QLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename quadtree::QLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1, a2, a3] =
                std::get<typename quadtree::Quad>(_sv.v());
            _stack.emplace_back(_After_Quad{crane_raw(a2), crane_raw(a1),
                                            crane_raw(a0), *a3, *a2, *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a3)});
          }
        } else if (std::holds_alternative<_After_Quad>(_frame)) {
          auto _f = std::move(std::get<_After_Quad>(_frame));
          _stack.emplace_back(_After_Quad_1{
              std::move(_result), _f.a1_0, _f.a0_0, std::move(_f.a3),
              std::move(_f.a2_1), std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a2_0});
        } else if (std::holds_alternative<_After_Quad_1>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_1>(_frame));
          _stack.emplace_back(
              _After_Quad_2{std::move(_f._result), std::move(_result), _f.a0_0,
                            std::move(_f.a3), std::move(_f.a2),
                            std::move(_f.a1_1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a1_0});
        } else if (std::holds_alternative<_After_Quad_2>(_frame)) {
          auto _f = std::move(std::get<_After_Quad_2>(_frame));
          _stack.emplace_back(_Combine_Quad{
              std::move(_f._result_0), std::move(_f._result_1),
              std::move(_result), std::move(_f.a3), std::move(_f.a2),
              std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_Quad>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result_2), std::move(_f.a2),
                       std::move(_f._result_1), std::move(_f.a3),
                       std::move(_f._result_0));
        }
      }
      return _result;
    }
  };

  static uint64_t max4_impl(uint64_t a, uint64_t b, uint64_t c, uint64_t d);

  struct simple_tree {
    // TYPES
    struct SLeaf {
      uint64_t a0;
    };

    struct SNode {
      std::shared_ptr<simple_tree> a0;
      std::shared_ptr<simple_tree> a1;
    };

    using variant_t = std::variant<SLeaf, SNode>;

  private:
    // DATA
    variant_t v_;

  public:
    // CREATORS
    simple_tree() {}

    explicit simple_tree(SLeaf _v) : v_(std::move(_v)) {}

    explicit simple_tree(SNode _v) : v_(std::move(_v)) {}

    static simple_tree sleaf(uint64_t a0) { return simple_tree(SLeaf{a0}); }

    static simple_tree snode(simple_tree a0, simple_tree a1) {
      return simple_tree(SNode{std::make_shared<simple_tree>(std::move(a0)),
                               std::make_shared<simple_tree>(std::move(a1))});
    }

    // MANIPULATORS
    ~simple_tree() {
      crane::small_vector<std::shared_ptr<simple_tree>> _stack = {};
      auto _drain = [&](variant_t &_v) {
        if (auto *_alt = std::get_if<SNode>(&_v)) {
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

    simple_tree(const simple_tree &) = default;
    simple_tree &operator=(const simple_tree &) = default;
    simple_tree(simple_tree &&) noexcept = default;
    simple_tree &operator=(simple_tree &&) noexcept = default;

    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }

    uint64_t count_paths_simple(uint64_t n) const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
        uint64_t n;
      };

      /// _After2: saves [a0, _s1], dispatches next recursive call.
      struct _After2 {
        simple_tree *a0;
        std::decay_t<decltype((
            ((std::declval<uint64_t &>() - UINT64_C(1)) >
                     std::declval<uint64_t &>()
                 ? 0
                 : (std::declval<uint64_t &>() - UINT64_C(1)))))>
            _s1;
      };

      /// _Combine1: receives partial results, combines with _result from final
      /// call.
      struct _Combine1 {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After2, _Combine1>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self, n});
      /// Loopified count_paths_simple: _Enter -> _After2 -> _Combine1.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          uint64_t n = _f.n;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            if (a0 == n) {
              _result = UINT64_C(1);
            } else {
              _result = UINT64_C(0);
            }
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            if (n <= UINT64_C(0)) {
              _result = UINT64_C(0);
            } else {
              _stack.emplace_back(
                  _After2{crane_raw(a0),
                          (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
              _stack.emplace_back(
                  _Enter{crane_raw(a1),
                         (((n - UINT64_C(1)) > n ? 0 : (n - UINT64_C(1))))});
            }
          }
        } else if (std::holds_alternative<_After2>(_frame)) {
          auto _f = std::move(std::get<_After2>(_frame));
          _stack.emplace_back(_Combine1{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0, _f._s1});
        } else {
          auto _f = std::move(std::get<_Combine1>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        }
      }
      return _result;
    }

    uint64_t simple_tree_sum() const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
      };

      /// _After_SNode: saves [a0], dispatches next recursive call.
      struct _After_SNode {
        simple_tree *a0;
      };

      /// _Combine_SNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_SNode {
        uint64_t _result;
      };

      using _Frame = std::variant<_Enter, _After_SNode, _Combine_SNode>;
      uint64_t _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_tree_sum: _Enter -> _After_SNode -> _Combine_SNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = std::move(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_After_SNode{crane_raw(a0)});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_SNode>(_frame)) {
          auto _f = std::move(std::get<_After_SNode>(_frame));
          _stack.emplace_back(_Combine_SNode{std::move(_result)});
          _stack.emplace_back(_Enter{_f.a0});
        } else {
          auto _f = std::move(std::get<_Combine_SNode>(_frame));
          _result = (std::move(_result) + std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_tree &, T1 &,
                                     simple_tree &, T1 &>
    T1 simple_tree_rec(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
      };

      /// _After_SNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_SNode {
        simple_tree *a0_0;
        simple_tree a1;
        simple_tree a0_1;
      };

      /// _Combine_SNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_SNode {
        std::decay_t<T1> _result;
        simple_tree a1;
        simple_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_SNode, _Combine_SNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_tree_rec: _Enter -> _After_SNode -> _Combine_SNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_After_SNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_SNode>(_frame)) {
          auto _f = std::move(std::get<_After_SNode>(_frame));
          _stack.emplace_back(_Combine_SNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_SNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }

    template <typename T1, typename F0, typename F1>
      requires std::is_invocable_r_v<T1, F0 &, uint64_t &> &&
               std::is_invocable_r_v<T1, F1 &, simple_tree &, T1 &,
                                     simple_tree &, T1 &>
    T1 simple_tree_rect(F0 &&f, F1 &&f0) const {
      const simple_tree *_self = this;

      /// _Enter: captures varying parameters for each recursive call.
      struct _Enter {
        const simple_tree *_self;
      };

      /// _After_SNode: saves [a0_0, a1, a0_1], dispatches next recursive call.
      struct _After_SNode {
        simple_tree *a0_0;
        simple_tree a1;
        simple_tree a0_1;
      };

      /// _Combine_SNode: receives partial results, combines with _result from
      /// final call.
      struct _Combine_SNode {
        std::decay_t<T1> _result;
        simple_tree a1;
        simple_tree a0;
      };

      using _Frame = std::variant<_Enter, _After_SNode, _Combine_SNode>;
      T1 _result{};
      crane::small_vector<_Frame> _stack;
      _stack.emplace_back(_Enter{_self});
      /// Loopified simple_tree_rect: _Enter -> _After_SNode -> _Combine_SNode.
      while (!_stack.empty()) {
        _Frame _frame = std::move(_stack.back());
        _stack.pop_back();
        if (std::holds_alternative<_Enter>(_frame)) {
          auto _f = std::move(std::get<_Enter>(_frame));
          const simple_tree *_self = _f._self;
          auto &&_sv = *_self;
          if (std::holds_alternative<typename simple_tree::SLeaf>(_sv.v())) {
            const auto &[a0] = std::get<typename simple_tree::SLeaf>(_sv.v());
            _result = f(a0);
          } else {
            const auto &[a0, a1] =
                std::get<typename simple_tree::SNode>(_sv.v());
            _stack.emplace_back(_After_SNode{crane_raw(a0), *a1, *a0});
            _stack.emplace_back(_Enter{crane_raw(a1)});
          }
        } else if (std::holds_alternative<_After_SNode>(_frame)) {
          auto _f = std::move(std::get<_After_SNode>(_frame));
          _stack.emplace_back(_Combine_SNode{
              std::move(_result), std::move(_f.a1), std::move(_f.a0_1)});
          _stack.emplace_back(_Enter{_f.a0_0});
        } else {
          auto _f = std::move(std::get<_Combine_SNode>(_frame));
          _result = f0(std::move(_f.a0), std::move(_result), std::move(_f.a1),
                       std::move(_f._result));
        }
      }
      return _result;
    }
  };

  static uint64_t min3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t max3(uint64_t a, uint64_t b, uint64_t c);
  static std::pair<uint64_t, uint64_t> tree_min_max(const tree<uint64_t> &t);
  static uint64_t all_paths_sum(const tree<uint64_t> &t);
  static bool tree_contains(uint64_t x, const tree<uint64_t> &t);
};

#endif // INCLUDED_LOOPIFY_TREES
