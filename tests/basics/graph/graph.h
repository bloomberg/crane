#ifndef INCLUDED_GRAPH
#define INCLUDED_GRAPH

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit Nat(O _v) : d_v_(std::move(_v)) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<Nat> O_() {
      return std::shared_ptr<Nat>(new Nat(O{}));
    }

    static std::shared_ptr<Nat> S_(const std::shared_ptr<Nat> &a0) {
      return std::shared_ptr<Nat>(new Nat(S{a0}));
    }

    static std::unique_ptr<Nat> O_uptr() {
      return std::unique_ptr<Nat>(new Nat(O{}));
    }

    static std::unique_ptr<Nat> S_uptr(const std::shared_ptr<Nat> &a0) {
      return std::unique_ptr<Nat>(new Nat(S{a0}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

public:
  // TYPES
  struct ctor {
    ctor() = delete;

    static std::shared_ptr<List<t_A>> Nil_() {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::shared_ptr<List<t_A>>
    Cons_(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::shared_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }

    static std::unique_ptr<List<t_A>> Nil_uptr() {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Nil{}));
    }

    static std::unique_ptr<List<t_A>>
    Cons_uptr(t_A a0, const std::shared_ptr<List<t_A>> &a1) {
      return std::unique_ptr<List<t_A>>(new List<t_A>(Cons{a0, a1}));
    }
  };

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  std::shared_ptr<List<t_A>> filter(F0 &&f) const {
    return std::visit(Overloaded{[](const typename List<t_A>::Nil _args)
                                     -> std::shared_ptr<List<t_A>> {
                                   return List<t_A>::ctor::Nil_();
                                 },
                                 [&](const typename List<t_A>::Cons _args)
                                     -> std::shared_ptr<List<t_A>> {
                                   t_A x = _args.d_a0;
                                   std::shared_ptr<List<t_A>> l0 = _args.d_a1;
                                   if (f(x)) {
                                     return List<t_A>::ctor::Cons_(
                                         x, std::move(l0)->filter(f));
                                   } else {
                                     return std::move(l0)->filter(f);
                                   }
                                 }},
                      this->v());
  }
};

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.

/// Decidable equality via a boolean function eqb.
template <typename I, typename t_A>
concept Eq = requires(t_A a0, t_A a1) {
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
};
/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
template <typename I, typename t_G, typename t_A>
concept Graph = requires(t_G a0, t_A a1) {
  typename I::edge;
  { I::empty() } -> std::convertible_to<t_G>;
  { I::add_node(a1, a0) } -> std::convertible_to<t_G>;
  { I::add_edge(a1, a0) } -> std::convertible_to<t_G>;
  { I::nodes(a0) } -> std::convertible_to<std::shared_ptr<List<t_A>>>;
  {
    I::edges(a1, a0)
  } -> std::convertible_to<std::shared_ptr<List<typename I::edge>>>;
};

template <typename g, typename a> using edge = std::any;

/// An edge in a directed graph, from edge_from to edge_to.
template <typename t_A> struct DirectedEdge {
  t_A edge_from;
  t_A edge_to;
};

template <typename _tcI0, typename T1>
__attribute__((pure)) bool
directed_originates(const T1 a, const std::shared_ptr<DirectedEdge<T1>> &e) {
  return _tcI0::eqb(e->edge_from, a);
}

/// A directed graph storing its directed_nodes and directed_edges.
template <typename t_A> struct Directed {
  std::shared_ptr<List<t_A>> directed_nodes;
  std::shared_ptr<List<std::shared_ptr<DirectedEdge<t_A>>>> directed_edges;
};

template <typename _tcI0, typename T1> struct DirectedGraph {
  using edge = std::shared_ptr<DirectedEdge<T1>>;

  static std::shared_ptr<Directed<std::any>> empty() {
    return std::make_shared<Directed<std::any>>(Directed<std::any>{
        List<std::any>::ctor::Nil_(),
        List<std::shared_ptr<DirectedEdge<std::any>>>::ctor::Nil_()});
  }

  static std::shared_ptr<Directed<std::any>>
  add_node(std::shared_ptr<Directed<std::any>> g, T1 n) {
    return std::make_shared<Directed<std::any>>(Directed<std::any>{
        List<std::any>::ctor::Cons_(n, g->directed_nodes), g->directed_edges});
  }

  static std::shared_ptr<Directed<std::any>>
  add_edge(std::shared_ptr<Directed<std::any>> g,
           std::shared_ptr<DirectedEdge<T1>> e) {
    return std::make_shared<Directed<std::any>>(Directed<std::any>{
        g->directed_nodes,
        List<std::shared_ptr<DirectedEdge<std::any>>>::ctor::Cons_(
            e, g->directed_edges)});
  }

  static std::shared_ptr<List<T1>>
  nodes(std::shared_ptr<Directed<std::any>> g) {
    return g->directed_nodes;
  }

  static std::shared_ptr<List<std::shared_ptr<DirectedEdge<T1>>>>
  edges(std::shared_ptr<Directed<std::any>> g, T1 n) {
    return g->directed_edges->filter(
        [&](const std::shared_ptr<DirectedEdge<T1>> &_x0) -> bool {
          return directed_originates<_tcI0, T1>(n, _x0);
        });
  }
};

/// An edge in an undirected graph connecting edge_first and edge_second.
template <typename t_A> struct UndirectedEdge {
  t_A edge_first;
  t_A edge_second;
};

template <typename _tcI0, typename T1>
__attribute__((pure)) bool
undirected_originates(const T1 a,
                      const std::shared_ptr<UndirectedEdge<T1>> &e) {
  return (_tcI0::eqb(e->edge_first, a) || _tcI0::eqb(e->edge_second, a));
}

template <typename t_A> struct Undirected {
  std::shared_ptr<List<t_A>> undirected_nodes;
  std::shared_ptr<List<std::shared_ptr<UndirectedEdge<t_A>>>> undirected_edges;
};

template <typename _tcI0, typename T1> struct UndirectedGraph {
  using edge = std::shared_ptr<UndirectedEdge<T1>>;

  static std::shared_ptr<Undirected<std::any>> empty() {
    return std::make_shared<Undirected<std::any>>(Undirected<std::any>{
        List<std::any>::ctor::Nil_(),
        List<std::shared_ptr<UndirectedEdge<std::any>>>::ctor::Nil_()});
  }

  static std::shared_ptr<Undirected<std::any>>
  add_node(std::shared_ptr<Undirected<std::any>> g, T1 n) {
    return std::make_shared<Undirected<std::any>>(Undirected<std::any>{
        List<std::any>::ctor::Cons_(n, g->undirected_nodes),
        g->undirected_edges});
  }

  static std::shared_ptr<Undirected<std::any>>
  add_edge(std::shared_ptr<Undirected<std::any>> g,
           std::shared_ptr<UndirectedEdge<T1>> e) {
    return std::make_shared<Undirected<std::any>>(Undirected<std::any>{
        g->undirected_nodes,
        List<std::shared_ptr<UndirectedEdge<std::any>>>::ctor::Cons_(
            e, g->undirected_edges)});
  }

  static std::shared_ptr<List<T1>>
  nodes(std::shared_ptr<Undirected<std::any>> g) {
    return g->undirected_nodes;
  }

  static std::shared_ptr<List<std::shared_ptr<UndirectedEdge<T1>>>>
  edges(std::shared_ptr<Undirected<std::any>> g, T1 n) {
    return g->undirected_edges->filter(
        [&](const std::shared_ptr<UndirectedEdge<T1>> &_x0) -> bool {
          return undirected_originates<_tcI0, T1>(n, _x0);
        });
  }
};

__attribute__((pure)) bool nat_eqb(const std::shared_ptr<Nat> &n,
                                   const std::shared_ptr<Nat> &m);

struct NatEq {
  __attribute__((pure)) static bool eqb(std::shared_ptr<Nat> a0,
                                        std::shared_ptr<Nat> a1) {
    return nat_eqb(a0, a1);
  }
};

static_assert(Eq<NatEq, std::shared_ptr<Nat>>);

template <typename _tcI0, typename T1>
__attribute__((pure)) bool test_eq(const T1 x, const T1 y) {
  return _tcI0::eqb(x, y);
}

const bool test_int_eq = test_eq<NatEq, std::shared_ptr<Nat>>(
    Nat::ctor::S_(Nat::ctor::S_(
        Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))),
    Nat::ctor::S_(Nat::ctor::S_(
        Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))));

#endif // INCLUDED_GRAPH
