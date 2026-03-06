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
public:
  struct O {};
  struct S {
    std::shared_ptr<Nat> _a0;
  };
  using variant_t = std::variant<O, S>;

private:
  variant_t v_;
  explicit Nat(O _v) : v_(std::move(_v)) {}
  explicit Nat(S _v) : v_(std::move(_v)) {}

public:
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
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
};

template <typename A> struct List {
public:
  struct nil {};
  struct cons {
    A _a0;
    std::shared_ptr<List<A>> _a1;
  };
  using variant_t = std::variant<nil, cons>;

private:
  variant_t v_;
  explicit List(nil _v) : v_(std::move(_v)) {}
  explicit List(cons _v) : v_(std::move(_v)) {}

public:
  struct ctor {
    ctor() = delete;
    static std::shared_ptr<List<A>> nil_() {
      return std::shared_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::shared_ptr<List<A>> cons_(A a0,
                                          const std::shared_ptr<List<A>> &a1) {
      return std::shared_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
    static std::unique_ptr<List<A>> nil_uptr() {
      return std::unique_ptr<List<A>>(new List<A>(nil{}));
    }
    static std::unique_ptr<List<A>>
    cons_uptr(A a0, const std::shared_ptr<List<A>> &a1) {
      return std::unique_ptr<List<A>>(new List<A>(cons{a0, a1}));
    }
  };
  const variant_t &v() const { return v_; }
  variant_t &v_mut() { return v_; }
  template <MapsTo<bool, A> F0> std::shared_ptr<List<A>> filter(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<A>> {
              return List<A>::ctor::nil_();
            },
            [&](const typename List<A>::cons _args)
                -> std::shared_ptr<List<A>> {
              A x = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              if (f(x)) {
                return List<A>::ctor::cons_(x, std::move(l0)->filter(f));
              } else {
                return std::move(l0)->filter(f);
              }
            }},
        this->v());
  }
};

template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
};
template <typename I, typename G, typename A>
concept Graph = requires(G a0, A a1) {
  typename I::edge;
  { I::empty() } -> std::convertible_to<G>;
  { I::add_node(a1, a0) } -> std::convertible_to<G>;
  { I::add_edge(a1, a0) } -> std::convertible_to<G>;
  { I::nodes(a0) } -> std::convertible_to<std::shared_ptr<List<A>>>;
  {
    I::edges(a1, a0)
  } -> std::convertible_to<std::shared_ptr<List<typename I::edge>>>;
};

template <typename g, typename a> using edge = std::any;

template <typename A> struct DirectedEdge {
  A edge_from;
  A edge_to;
};

template <typename _tcI0, typename T1>
bool directed_originates(const T1 a,
                         const std::shared_ptr<DirectedEdge<T1>> &e) {
  return _tcI0::eqb(e->edge_from, a);
}

template <typename A> struct Directed {
  std::shared_ptr<List<A>> directed_nodes;
  std::shared_ptr<List<std::shared_ptr<DirectedEdge<A>>>> directed_edges;
};

template <typename _tcI0, typename T1> struct DirectedGraph {
  using edge = std::shared_ptr<DirectedEdge<T1>>;
  static std::shared_ptr<Directed<std::any>> empty() {
    return std::make_shared<Directed<std::any>>(Directed<std::any>{
        List<std::any>::ctor::nil_(),
        List<std::shared_ptr<DirectedEdge<std::any>>>::ctor::nil_()});
  }
  static std::shared_ptr<Directed<std::any>>
  add_node(std::shared_ptr<Directed<std::any>> g, T1 n) {
    return std::make_shared<Directed<std::any>>(Directed<std::any>{
        List<std::any>::ctor::cons_(n, g->directed_nodes), g->directed_edges});
  }
  static std::shared_ptr<Directed<std::any>>
  add_edge(std::shared_ptr<Directed<std::any>> g,
           std::shared_ptr<DirectedEdge<T1>> e) {
    return std::make_shared<Directed<std::any>>(Directed<std::any>{
        g->directed_nodes,
        List<std::shared_ptr<DirectedEdge<std::any>>>::ctor::cons_(
            e, g->directed_edges)});
  }
  static std::shared_ptr<List<T1>>
  nodes(std::shared_ptr<Directed<std::any>> g) {
    return g->directed_nodes;
  }
  static std::shared_ptr<List<std::shared_ptr<DirectedEdge<T1>>>>
  edges(std::shared_ptr<Directed<std::any>> g, T1 n) {
    return g->directed_edges->filter(
        [&](const std::shared_ptr<DirectedEdge<T1>> _x0) {
          return directed_originates<_tcI0, T1>(n, _x0);
        });
  }
};

template <typename A> struct UndirectedEdge {
  A edge_first;
  A edge_second;
};

template <typename _tcI0, typename T1>
bool undirected_originates(const T1 a,
                           const std::shared_ptr<UndirectedEdge<T1>> &e) {
  return (_tcI0::eqb(e->edge_first, a) || _tcI0::eqb(e->edge_second, a));
}

template <typename A> struct Undirected {
  std::shared_ptr<List<A>> undirected_nodes;
  std::shared_ptr<List<std::shared_ptr<UndirectedEdge<A>>>> undirected_edges;
};

template <typename _tcI0, typename T1> struct UndirectedGraph {
  using edge = std::shared_ptr<UndirectedEdge<T1>>;
  static std::shared_ptr<Undirected<std::any>> empty() {
    return std::make_shared<Undirected<std::any>>(Undirected<std::any>{
        List<std::any>::ctor::nil_(),
        List<std::shared_ptr<UndirectedEdge<std::any>>>::ctor::nil_()});
  }
  static std::shared_ptr<Undirected<std::any>>
  add_node(std::shared_ptr<Undirected<std::any>> g, T1 n) {
    return std::make_shared<Undirected<std::any>>(Undirected<std::any>{
        List<std::any>::ctor::cons_(n, g->undirected_nodes),
        g->undirected_edges});
  }
  static std::shared_ptr<Undirected<std::any>>
  add_edge(std::shared_ptr<Undirected<std::any>> g,
           std::shared_ptr<UndirectedEdge<T1>> e) {
    return std::make_shared<Undirected<std::any>>(Undirected<std::any>{
        g->undirected_nodes,
        List<std::shared_ptr<UndirectedEdge<std::any>>>::ctor::cons_(
            e, g->undirected_edges)});
  }
  static std::shared_ptr<List<T1>>
  nodes(std::shared_ptr<Undirected<std::any>> g) {
    return g->undirected_nodes;
  }
  static std::shared_ptr<List<std::shared_ptr<UndirectedEdge<T1>>>>
  edges(std::shared_ptr<Undirected<std::any>> g, T1 n) {
    return g->undirected_edges->filter(
        [&](const std::shared_ptr<UndirectedEdge<T1>> _x0) {
          return undirected_originates<_tcI0, T1>(n, _x0);
        });
  }
};

bool nat_eqb(const std::shared_ptr<Nat> &n, const std::shared_ptr<Nat> &m);

struct NatEq {
  static bool eqb(std::shared_ptr<Nat> a0, std::shared_ptr<Nat> a1) {
    return nat_eqb(a0, a1);
  }
};
static_assert(Eq<NatEq, std::shared_ptr<Nat>>);

template <typename _tcI0, typename T1> bool test_eq(const T1 x, const T1 y) {
  return _tcI0::eqb(x, y);
}

const bool test_int_eq = test_eq<NatEq, std::shared_ptr<Nat>>(
    Nat::ctor::S_(Nat::ctor::S_(
        Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))),
    Nat::ctor::S_(Nat::ctor::S_(
        Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::S_(Nat::ctor::O_()))))));
