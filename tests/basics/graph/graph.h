#ifndef INCLUDED_GRAPH
#define INCLUDED_GRAPH

#include <any>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  return x ? std::make_shared<T>(x->clone()) : nullptr;
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x.clone());
      }
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> d_a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : d_v_(_v) {}

  explicit Nat(S _v) : d_v_(std::move(_v)) {}

  Nat(const Nat &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  Nat(Nat &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) Nat &operator=(const Nat &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) Nat &operator=(Nat &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) Nat clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<O>(_sv.v())) {
      return Nat(O{});
    } else {
      const auto &[d_a0] = std::get<S>(_sv.v());
      return Nat(S{clone_as_value<std::unique_ptr<Nat>>(d_a0)});
    }
  }

  // CREATORS
  __attribute__((pure)) static Nat o() { return Nat(O{}); }

  __attribute__((pure)) static Nat s(const Nat &a0) {
    return Nat(S{std::make_unique<Nat>(a0.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) Nat *operator->() { return this; }

  __attribute__((pure)) const Nat *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = Nat(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) List<t_A> filter(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      if (f(d_a0)) {
        return List<t_A>::cons(d_a0, (*(d_a1)).filter(f));
      } else {
        return (*(d_a1)).filter(f);
      }
    }
  }
};

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.

/// Decidable equality via a boolean function eqb.
template <typename I, typename t_A>
concept Eq = requires(t_A a0, t_A a1) {
  { I::eqb(a0, a1) } -> std::convertible_to<bool>;
};
/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
template <typename I, typename t_G, typename t_A>
concept Graph = requires(t_G a0, t_A a1) {
  typename I::edge;
  { I::empty() } -> std::convertible_to<t_G>;
  { I::add_node(a0, a1) } -> std::convertible_to<t_G>;
  { I::add_edge(a0, a1) } -> std::convertible_to<t_G>;
  { I::nodes(a0) } -> std::convertible_to<List<t_A>>;
  { I::edges(a0, a1) } -> std::convertible_to<List<typename I::edge>>;
};

template <typename g, typename a> using edge = std::any;

/// An edge in a directed graph, from edge_from to edge_to.
template <typename t_A> struct DirectedEdge {
  t_A edge_from;
  t_A edge_to;

  __attribute__((pure)) DirectedEdge<t_A> *operator->() { return this; }

  __attribute__((pure)) const DirectedEdge<t_A> *operator->() const {
    return this;
  }
};

template <typename _tcI0, typename T1>
__attribute__((pure)) bool directed_originates(const T1 a,
                                               const DirectedEdge<T1> &e) {
  return _tcI0::eqb(e.edge_from, a);
}

/// A directed graph storing its directed_nodes and directed_edges.
template <typename t_A> struct Directed {
  List<t_A> directed_nodes;
  List<DirectedEdge<t_A>> directed_edges;

  __attribute__((pure)) Directed<t_A> *operator->() { return this; }

  __attribute__((pure)) const Directed<t_A> *operator->() const { return this; }
};

template <typename _tcI0, typename T1> struct DirectedGraph {
  using edge = DirectedEdge<T1>;

  constexpr static Directed<std::any> empty() {
    return Directed<std::any>{List<std::any>::nil(),
                              List<DirectedEdge<std::any>>::nil()};
  }

  __attribute__((pure)) static Directed<std::any> add_node(Directed<std::any> g,
                                                           T1 n) {
    return Directed<std::any>{List<std::any>::cons(n, g.directed_nodes),
                              g.directed_edges};
  }

  constexpr static Directed<std::any> add_edge(Directed<std::any> g,
                                               DirectedEdge<T1> e) {
    return Directed<std::any>{
        g.directed_nodes,
        List<DirectedEdge<std::any>>::cons(e, g.directed_edges)};
  }

  __attribute__((pure)) static List<T1> nodes(Directed<std::any> g) {
    return g.directed_nodes;
  }

  __attribute__((pure)) static List<DirectedEdge<T1>>
  edges(Directed<std::any> g, T1 n) {
    return g.directed_edges.filter([=](DirectedEdge<T1> _x0) mutable -> bool {
      return directed_originates<_tcI0, T1>(n, _x0);
    });
  }
};

/// An edge in an undirected graph connecting edge_first and edge_second.
template <typename t_A> struct UndirectedEdge {
  t_A edge_first;
  t_A edge_second;

  __attribute__((pure)) UndirectedEdge<t_A> *operator->() { return this; }

  __attribute__((pure)) const UndirectedEdge<t_A> *operator->() const {
    return this;
  }
};

template <typename _tcI0, typename T1>
__attribute__((pure)) bool undirected_originates(const T1 a,
                                                 const UndirectedEdge<T1> &e) {
  return (_tcI0::eqb(e.edge_first, a) || _tcI0::eqb(e.edge_second, a));
}

template <typename t_A> struct Undirected {
  List<t_A> undirected_nodes;
  List<UndirectedEdge<t_A>> undirected_edges;

  __attribute__((pure)) Undirected<t_A> *operator->() { return this; }

  __attribute__((pure)) const Undirected<t_A> *operator->() const {
    return this;
  }
};

template <typename _tcI0, typename T1> struct UndirectedGraph {
  using edge = UndirectedEdge<T1>;

  constexpr static Undirected<std::any> empty() {
    return Undirected<std::any>{List<std::any>::nil(),
                                List<UndirectedEdge<std::any>>::nil()};
  }

  __attribute__((pure)) static Undirected<std::any>
  add_node(Undirected<std::any> g, T1 n) {
    return Undirected<std::any>{List<std::any>::cons(n, g.undirected_nodes),
                                g.undirected_edges};
  }

  constexpr static Undirected<std::any> add_edge(Undirected<std::any> g,
                                                 UndirectedEdge<T1> e) {
    return Undirected<std::any>{
        g.undirected_nodes,
        List<UndirectedEdge<std::any>>::cons(e, g.undirected_edges)};
  }

  __attribute__((pure)) static List<T1> nodes(Undirected<std::any> g) {
    return g.undirected_nodes;
  }

  __attribute__((pure)) static List<UndirectedEdge<T1>>
  edges(Undirected<std::any> g, T1 n) {
    return g.undirected_edges.filter(
        [=](UndirectedEdge<T1> _x0) mutable -> bool {
          return undirected_originates<_tcI0, T1>(n, _x0);
        });
  }
};

__attribute__((pure)) bool nat_eqb(const Nat &n, const Nat &m);

struct NatEq {
  __attribute__((pure)) static bool eqb(Nat a0, Nat a1) {
    return nat_eqb(a0, a1);
  }
};

static_assert(Eq<NatEq, Nat>);

template <typename _tcI0, typename T1>
__attribute__((pure)) bool test_eq(const T1 x, const T1 y) {
  return _tcI0::eqb(x, y);
}

const bool test_int_eq =
    test_eq<NatEq, Nat>(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))),
                        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));

#endif // INCLUDED_GRAPH
