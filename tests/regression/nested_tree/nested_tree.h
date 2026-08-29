#ifndef INCLUDED_NESTED_TREE
#define INCLUDED_NESTED_TREE

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

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

struct NestedTree {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      std::any a;
      std::shared_ptr<tree> t;
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

    static tree node(std::any a, tree t) {
      return tree(Node{std::move(a), std::make_shared<tree>(std::move(t))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2, typename F1>
  static T1 tree_rect(const T1 &f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      return std::any_cast<T1>(
          f0(a0, *a1, tree_rect(f, crane_erase_fn<T1>(f0), *a1)));
    }
  }

  template <typename T1, typename T2, typename F1>
  static T1 tree_rec(const T1 &f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      return std::any_cast<T1>(
          f0(a0, *a1, tree_rec(f, crane_erase_fn<T1>(f0), *a1)));
    }
  }

  static inline const tree example1 = tree::node(
      Nat::s(Nat::o()),
      tree::node(
          std::make_pair(Nat::s(Nat::s(Nat::o())),
                         Nat::s(Nat::s(Nat::s(Nat::o())))),
          tree::node(
              std::make_pair(
                  std::make_pair(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))),
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                  std::make_pair(
                      Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))),
                      Nat::s(Nat::s(
                          Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))))))),
              tree::leaf())));

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<List<T2>, F0 &, T1 &>
  static List<T2> lift(F0 &&f, const std::pair<T1, T1> &p) {
    const auto &[x, y] = p;
    return f(x).app(f(y));
  }

  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<List<T2>, F0 &, T1 &>
  static List<List<T2>> _flatten_tree_go(F0 &&f, const tree t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return List<List<T2>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return List<List<T2>>::cons(
          f(a0), _flatten_tree_go<T1, T2>(
                     [=](std::pair<T1, T1> _x0) mutable -> List<T2> {
                       return lift<T1, T2>(f, _x0);
                     },
                     *a1));
    }
  }

  template <typename T1 = std::any>
  static List<List<T1>> flatten_tree(const tree &t) {
    return _flatten_tree_go<T1, T1>(
        [](T1 x) { return List<T1>::cons(x, List<T1>::nil()); }, t);
  }
};

#endif // INCLUDED_NESTED_TREE
