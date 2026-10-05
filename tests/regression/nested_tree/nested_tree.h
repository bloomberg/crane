#ifndef INCLUDED_NESTED_TREE
#define INCLUDED_NESTED_TREE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
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
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(_loop_m);
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

struct NestedTree {
  struct tree {
    // TYPES
    struct Leaf {};

    struct Node {
      crane::obj a;
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

    static tree node(crane::obj a, tree t) {
      return tree(Node{std::move(a), std::make_shared<tree>(std::move(t))});
    }

    // MANIPULATORS
    inline variant_t &v_mut() { return v_; }

    // ACCESSORS
    const variant_t &v() const { return v_; }
  };

  template <typename T1, typename T2 = void, typename F1>
  static T1 tree_rect(const T1 &f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      return crane_any_cast<T1>(
          f0(a0, *a1, tree_rect(f, crane_erase_fn<T1>(f0), *a1)));
    }
  }

  template <typename T1, typename T2 = void, typename F1>
  static T1 tree_rec(const T1 &f, F1 &&f0, const tree &t) {
    if (std::holds_alternative<typename tree::Leaf>(t.v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t.v());
      return crane_any_cast<T1>(
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
  static List<T2> lift(F0 &&f, const std::pair<T1, T1> &p) {
    const auto &[x, y] = p;
    return f(x).app(f(y));
  }

  template <typename T1, typename T2>
  static List<List<T2>> flatten_tree_crane_go(const crane::fn<List<T2>(T1)> f,
                                              const tree t0) {
    if (std::holds_alternative<typename tree::Leaf>(t0.v())) {
      return List<List<T2>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename tree::Node>(t0.v());
      return List<List<T2>>::cons(f(a0),
                                  flatten_tree_crane_go<T1, T2>(
                                      [=](std::pair<T1, T1> _x0) -> List<T2> {
                                        return lift<T1, T2>(f, _x0);
                                      },
                                      *a1));
    }
  }

  template <typename T1> static List<List<T1>> flatten_tree(const tree &t) {
    return flatten_tree_crane_go<T1, T1>(
        [](const T1 &x) { return List<T1>::cons(x, List<T1>::nil()); }, t);
  }
};

#endif // INCLUDED_NESTED_TREE
