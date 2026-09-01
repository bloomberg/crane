#ifndef INCLUDED_GRAPH
#define INCLUDED_GRAPH

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
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

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(List<A>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell =
              std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }
};

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.

/// Decidable equality via a boolean function eqb.
template <typename I, typename A>
concept Eq = requires {
  { I::eqb(std::declval<A>(), std::declval<A>()) } -> std::convertible_to<bool>;
};
/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
template <typename I, typename A>
concept Graph = requires {
  typename I::template G<std::any>;
  typename I::edge;
  { I::empty() } -> std::convertible_to<typename I::template G<A>>;
  {
    I::add_node(std::declval<typename I::template G<A>>(), std::declval<A>())
  } -> std::convertible_to<typename I::template G<A>>;
  {
    I::add_edge(std::declval<typename I::template G<A>>(),
                std::declval<typename I::edge>())
  } -> std::convertible_to<typename I::template G<A>>;
  {
    I::nodes(std::declval<typename I::template G<A>>())
  } -> std::convertible_to<List<A>>;
  {
    I::edges(std::declval<typename I::template G<A>>(), std::declval<A>())
  } -> std::convertible_to<List<typename I::edge>>;
};

template <typename g, typename a> using edge = std::any;

/// An edge in a directed graph, from edge_from to edge_to.
template <typename A> struct DirectedEdge {
  A edge_from;
  A edge_to;
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool directed_originates(const T1 &a, const DirectedEdge<T1> &e) {
  return _tcI0::eqb(e.edge_from, a);
}

/// A directed graph storing its directed_nodes and directed_edges.
template <typename A> struct Directed {
  List<A> directed_nodes;
  List<DirectedEdge<A>> directed_edges;
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
struct DirectedGraph {
  template <typename _A0> using G = Directed<_A0>;
  using edge = DirectedEdge<T1>;

  static Directed<T1> empty() {
    return Directed<std::any>{List<std::any>::nil(),
                              List<DirectedEdge<std::any>>::nil()};
  }

  static Directed<T1> add_node(Directed<std::any> g, T1 n) {
    return Directed<std::any>{List<std::any>::cons(n, g.directed_nodes),
                              g.directed_edges};
  }

  static Directed<T1> add_edge(Directed<std::any> g, DirectedEdge<T1> e) {
    return Directed<std::any>{
        g.directed_nodes,
        List<DirectedEdge<std::any>>::cons(e, g.directed_edges)};
  }

  static List<T1> nodes(Directed<std::any> g) { return g.directed_nodes; }

  static List<edge> edges(Directed<std::any> g, T1 n) {
    return g.directed_edges.filter([=](DirectedEdge<T1> _x0) mutable -> bool {
      return directed_originates<_tcI0, T1>(n, _x0);
    });
  }
};

/// An edge in an undirected graph connecting edge_first and edge_second.
template <typename A> struct UndirectedEdge {
  A edge_first;
  A edge_second;
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool undirected_originates(const T1 &a, const UndirectedEdge<T1> &e) {
  return (_tcI0::eqb(e.edge_first, a) || _tcI0::eqb(e.edge_second, a));
}

template <typename A> struct Undirected {
  List<A> undirected_nodes;
  List<UndirectedEdge<A>> undirected_edges;
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
struct UndirectedGraph {
  template <typename _A0> using G = Undirected<_A0>;
  using edge = UndirectedEdge<T1>;

  static Undirected<T1> empty() {
    return Undirected<std::any>{List<std::any>::nil(),
                                List<UndirectedEdge<std::any>>::nil()};
  }

  static Undirected<T1> add_node(Undirected<std::any> g, T1 n) {
    return Undirected<std::any>{List<std::any>::cons(n, g.undirected_nodes),
                                g.undirected_edges};
  }

  static Undirected<T1> add_edge(Undirected<std::any> g, UndirectedEdge<T1> e) {
    return Undirected<std::any>{
        g.undirected_nodes,
        List<UndirectedEdge<std::any>>::cons(e, g.undirected_edges)};
  }

  static List<T1> nodes(Undirected<std::any> g) { return g.undirected_nodes; }

  static List<edge> edges(Undirected<std::any> g, T1 n) {
    return g.undirected_edges.filter(
        [=](UndirectedEdge<T1> _x0) mutable -> bool {
          return undirected_originates<_tcI0, T1>(n, _x0);
        });
  }
};

bool nat_eqb(const Nat &n, const Nat &m);

struct NatEq {
  static bool eqb(Nat a0, Nat a1) { return nat_eqb(a0, a1); }
};

static_assert(Eq<NatEq, Nat>);

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool test_eq(const T1 &x, const T1 &y) {
  return _tcI0::eqb(x, y);
}

const bool test_int_eq =
    test_eq<NatEq, Nat>(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))),
                        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));

#endif // INCLUDED_GRAPH
