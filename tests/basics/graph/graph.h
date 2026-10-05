#ifndef INCLUDED_GRAPH
#define INCLUDED_GRAPH

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename A> struct DirectedEdge;
template <typename A> struct Directed;
template <typename A> struct UndirectedEdge;
template <typename A> struct Undirected;
struct NatEq;
template <typename g = void, typename a = void> using edge = crane::obj;

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

  template <typename F0> List<A> filter(F0 &&f) const {
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<A>::nil();
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell = typename List<A>::Cons(a0, nullptr);
          List<A> &_node =
              (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
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
  typename I::template G<crane::obj>;
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

/// An edge in a directed graph, from edge_from to edge_to.
template <typename A> struct DirectedEdge {
  A edge_from;
  A edge_to;

  // ACCESSORS
  template <typename CraneU>
    requires crane_convertible<CraneU, const A &> &&
             crane_convertible<CraneU, const A &>
  operator DirectedEdge<CraneU>() const {
    return {crane_convert<CraneU>(edge_from), crane_convert<CraneU>(edge_to)};
  }
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

  // ACCESSORS
  template <typename CraneU> operator Directed<CraneU>() const {
    return {crane_convert<List<CraneU>>(directed_nodes),
            crane_convert<List<DirectedEdge<CraneU>>>(directed_edges)};
  }
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
struct DirectedGraph {
  template <typename CraneA0> using G = Directed<CraneA0>;
  using edge = DirectedEdge<T1>;

  static Directed<T1> empty() {
    return Directed<T1>{List<T1>::nil(), List<DirectedEdge<T1>>::nil()};
  }

  static Directed<T1> add_node(Directed<T1> g, T1 n) {
    return Directed<T1>{List<T1>::cons(std::move(n), g.directed_nodes),
                        g.directed_edges};
  }

  static Directed<T1> add_edge(Directed<T1> g, DirectedEdge<T1> e) {
    return Directed<T1>{g.directed_nodes, List<DirectedEdge<T1>>::cons(
                                              std::move(e), g.directed_edges)};
  }

  static List<T1> nodes(Directed<T1> g) { return std::move(g).directed_nodes; }

  static List<edge> edges(Directed<T1> g, T1 n) {
    return g.directed_edges.filter([=](DirectedEdge<T1> _x0) -> bool {
      return directed_originates<_tcI0, T1>(n, _x0);
    });
  }
};

/// An edge in an undirected graph connecting edge_first and edge_second.
template <typename A> struct UndirectedEdge {
  A edge_first;
  A edge_second;

  // ACCESSORS
  template <typename CraneU>
    requires crane_convertible<CraneU, const A &> &&
             crane_convertible<CraneU, const A &>
  operator UndirectedEdge<CraneU>() const {
    return {crane_convert<CraneU>(edge_first),
            crane_convert<CraneU>(edge_second)};
  }
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool undirected_originates(const T1 &a, const UndirectedEdge<T1> &e) {
  return (_tcI0::eqb(e.edge_first, a) || _tcI0::eqb(e.edge_second, a));
}

template <typename A> struct Undirected {
  List<A> undirected_nodes;
  List<UndirectedEdge<A>> undirected_edges;

  // ACCESSORS
  template <typename CraneU> operator Undirected<CraneU>() const {
    return {crane_convert<List<CraneU>>(undirected_nodes),
            crane_convert<List<UndirectedEdge<CraneU>>>(undirected_edges)};
  }
};

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
struct UndirectedGraph {
  template <typename CraneA0> using G = Undirected<CraneA0>;
  using edge = UndirectedEdge<T1>;

  static Undirected<T1> empty() {
    return Undirected<T1>{List<T1>::nil(), List<UndirectedEdge<T1>>::nil()};
  }

  static Undirected<T1> add_node(Undirected<T1> g, T1 n) {
    return Undirected<T1>{List<T1>::cons(std::move(n), g.undirected_nodes),
                          g.undirected_edges};
  }

  static Undirected<T1> add_edge(Undirected<T1> g, UndirectedEdge<T1> e) {
    return Undirected<T1>{
        g.undirected_nodes,
        List<UndirectedEdge<T1>>::cons(std::move(e), g.undirected_edges)};
  }

  static List<T1> nodes(Undirected<T1> g) {
    return std::move(g).undirected_nodes;
  }

  static List<edge> edges(Undirected<T1> g, T1 n) {
    return g.undirected_edges.filter([=](UndirectedEdge<T1> _x0) -> bool {
      return undirected_originates<_tcI0, T1>(n, _x0);
    });
  }
};

bool nat_eqb(const Nat &n, const Nat &m);

struct NatEq {
  static bool eqb(Nat a0, Nat a1) {
    return nat_eqb(std::move(a0), std::move(a1));
  }
};

static_assert(Eq<NatEq, Nat>);

template <typename _tcI0, typename T1>
  requires Eq<_tcI0, T1>
bool test_eq(const T1 &x, const T1 &y) {
  return _tcI0::eqb(x, y);
}

inline constexpr bool test_int_eq = true;

#endif // INCLUDED_GRAPH
