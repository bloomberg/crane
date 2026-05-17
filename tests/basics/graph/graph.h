#ifndef INCLUDED_GRAPH
#define INCLUDED_GRAPH

#include <any>
#include <concepts>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::unique_ptr<Nat> a0;
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

  Nat(const Nat &_other) : v_(std::move(_other.clone().v_)) {}

  Nat(Nat &&_other) noexcept : v_(std::move(_other.v_)) {}

  Nat &operator=(const Nat &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  Nat &operator=(Nat &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  Nat clone() const {
    Nat _out{};

    struct _CloneFrame {
      const Nat *_src;
      Nat *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const Nat *_src = _frame._src;
      Nat *_dst = _frame._dst;
      if (std::holds_alternative<O>(_src->v())) {
        _dst->v_ = O{};
      } else {
        const auto &_alt = std::get<S>(_src->v());
        _dst->v_ = S{_alt.a0 ? std::make_unique<Nat>() : nullptr};
        auto &_dst_alt = std::get<S>(_dst->v_);
        if (_alt.a0) {
          _stack.push_back({_alt.a0.get(), _dst_alt.a0.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_unique<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    std::vector<std::unique_ptr<Nat>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](Nat &_node) {
      if (std::holds_alternative<S>(_node.v_)) {
        auto &_alt = std::get<S>(_node.v_);
        if (_alt.a0) {
          _stack.push_back(std::move(_alt.a0));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a0;
    std::unique_ptr<List<A>> a1;
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

  List(const List<A> &_other) : v_(std::move(_other.clone().v_)) {}

  List(List<A> &&_other) noexcept : v_(std::move(_other.v_)) {}

  List<A> &operator=(const List<A> &_other) {
    v_ = std::move(_other.clone().v_);
    return *this;
  }

  List<A> &operator=(List<A> &&_other) noexcept {
    v_ = std::move(_other.v_);
    return *this;
  }

  // ACCESSORS
  List<A> clone() const {
    List<A> _out{};

    struct _CloneFrame {
      const List<A> *_src;
      List<A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.reserve(8);
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<A> *_src = _frame._src;
      List<A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->v_ =
            Cons{_alt.a0, _alt.a1 ? std::make_unique<List<A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->v_);
        if (_alt.a1) {
          _stack.push_back({_alt.a1.get(), _dst_alt.a1.get()});
        }
      }
    }
    return _out;
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a0, a1] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{A(a0), a1 ? std::make_unique<List<A>>(*a1) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a0, List<A> a1) {
    return List(Cons{std::move(a0), std::make_unique<List<A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<A>>> _stack{};
    _stack.reserve(8);
    auto _drain = [&](List<A> &_node) {
      if (std::holds_alternative<Cons>(_node.v_)) {
        auto &_alt = std::get<Cons>(_node.v_);
        if (_alt.a1) {
          _stack.push_back(std::move(_alt.a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      if (f(a0)) {
        return List<A>::cons(a0, (*a1).filter(f));
      } else {
        return (*a1).filter(f);
      }
    }
  }
};

/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.

/// Decidable equality via a boolean function eqb.
template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a0, a1) } -> std::convertible_to<bool>;
};
/// A graph abstraction parameterized by a container type G and
/// node type A. Provides operations for building and querying
/// the graph.
template <typename I, typename G, typename A>
concept Graph = requires(G a0, A a1) {
  typename I::edge;
  { I::empty() } -> std::convertible_to<G>;
  { I::add_node(a0, a1) } -> std::convertible_to<G>;
  { I::add_edge(a0, a1) } -> std::convertible_to<G>;
  { I::nodes(a0) } -> std::convertible_to<List<A>>;
  { I::edges(a0, a1) } -> std::convertible_to<List<typename I::edge>>;
};

template <typename g, typename a> using edge = std::any;

/// An edge in a directed graph, from edge_from to edge_to.
template <typename A> struct DirectedEdge {
  A edge_from;
  A edge_to;

  // ACCESSORS
  DirectedEdge<A> clone() const {
    return DirectedEdge<A>{(*this).edge_from, (*this).edge_to};
  }
};

template <typename _tcI0, typename T1>
bool directed_originates(const T1 &a, const DirectedEdge<T1> &e) {
  return _tcI0::eqb(e.edge_from, a);
}

/// A directed graph storing its directed_nodes and directed_edges.
template <typename A> struct Directed {
  List<A> directed_nodes;
  List<DirectedEdge<A>> directed_edges;

  // ACCESSORS
  Directed<A> clone() const {
    return Directed<A>{(*this).directed_nodes.clone(),
                       (*this).directed_edges.clone()};
  }
};

template <typename _tcI0, typename T1> struct DirectedGraph {
  using edge = DirectedEdge<T1>;

  static Directed<std::any> empty() {
    return Directed<std::any>{List<std::any>::nil(),
                              List<DirectedEdge<std::any>>::nil()};
  }

  static Directed<std::any> add_node(Directed<std::any> g, T1 n) {
    return Directed<std::any>{List<std::any>::cons(n, g.directed_nodes),
                              g.directed_edges};
  }

  static Directed<std::any> add_edge(Directed<std::any> g, DirectedEdge<T1> e) {
    return Directed<std::any>{
        g.directed_nodes,
        List<DirectedEdge<std::any>>::cons(e, g.directed_edges)};
  }

  static List<T1> nodes(Directed<std::any> g) { return g.directed_nodes; }

  static List<DirectedEdge<T1>> edges(Directed<std::any> g, T1 n) {
    return g.directed_edges.filter([=](DirectedEdge<T1> _x0) mutable -> bool {
      return directed_originates<_tcI0, T1>(n, _x0);
    });
  }
};

/// An edge in an undirected graph connecting edge_first and edge_second.
template <typename A> struct UndirectedEdge {
  A edge_first;
  A edge_second;

  // ACCESSORS
  UndirectedEdge<A> clone() const {
    return UndirectedEdge<A>{(*this).edge_first, (*this).edge_second};
  }
};

template <typename _tcI0, typename T1>
bool undirected_originates(const T1 &a, const UndirectedEdge<T1> &e) {
  return (_tcI0::eqb(e.edge_first, a) || _tcI0::eqb(e.edge_second, a));
}

template <typename A> struct Undirected {
  List<A> undirected_nodes;
  List<UndirectedEdge<A>> undirected_edges;

  // ACCESSORS
  Undirected<A> clone() const {
    return Undirected<A>{(*this).undirected_nodes.clone(),
                         (*this).undirected_edges.clone()};
  }
};

template <typename _tcI0, typename T1> struct UndirectedGraph {
  using edge = UndirectedEdge<T1>;

  static Undirected<std::any> empty() {
    return Undirected<std::any>{List<std::any>::nil(),
                                List<UndirectedEdge<std::any>>::nil()};
  }

  static Undirected<std::any> add_node(Undirected<std::any> g, T1 n) {
    return Undirected<std::any>{List<std::any>::cons(n, g.undirected_nodes),
                                g.undirected_edges};
  }

  static Undirected<std::any> add_edge(Undirected<std::any> g,
                                       UndirectedEdge<T1> e) {
    return Undirected<std::any>{
        g.undirected_nodes,
        List<UndirectedEdge<std::any>>::cons(e, g.undirected_edges)};
  }

  static List<T1> nodes(Undirected<std::any> g) { return g.undirected_nodes; }

  static List<UndirectedEdge<T1>> edges(Undirected<std::any> g, T1 n) {
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

template <typename _tcI0, typename T1> bool test_eq(const T1 &x, const T1 &y) {
  return _tcI0::eqb(x, y);
}

const bool test_int_eq =
    test_eq<NatEq, Nat>(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))),
                        Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o()))))));

#endif // INCLUDED_GRAPH
