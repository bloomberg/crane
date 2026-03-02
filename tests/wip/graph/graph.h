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
concept Graph = requires(G a0, A a1, std::any a1) {
  { I::empty() } -> std::convertible_to<G>;
  { I::add_node(a1, a0) } -> std::convertible_to<G>;
  { I::add_edge(a1, a0) } -> std::convertible_to<G>;
  { I::nodes(a0) } -> std::convertible_to<std::shared_ptr<List<A>>>;
  { I::edges(a1, a0) } -> std::convertible_to<std::shared_ptr<List<std::any>>>;
};

struct Graph {
  template <typename _tcI0, typename T1>
  static bool eqb(const T1 _x0, const T1 _x1) {
    return _tcI0::eqb(_x0, _x1);
  }

  template <typename g, typename a> using edge = std::any;

  template <typename _tcI0, typename T1, typename T2> static T1 empty() {
    return _tcI0::empty;
  }

  template <typename _tcI0, typename T1, typename T2>
  static T1 add_node(const T2 _x0, const T1 _x1) {
    return _tcI0::add_node(_x0, _x1);
  }

  template <typename _tcI0, typename T1, typename T2>
  static T1 add_edge(const edge<T1, T2> _x0, const T1 _x1) {
    return _tcI0::add_edge(_x0, _x1);
  }

  template <typename _tcI0, typename T1, typename T2>
  static std::shared_ptr<List<T2>> nodes(const T1 _x0) {
    return _tcI0::nodes(_x0);
  }

  template <typename _tcI0, typename T1, typename T2>
  static std::shared_ptr<List<edge<T1, T2>>> edges(const T2 _x0, const T1 _x1) {
    return _tcI0::edges(_x0, _x1);
  }

  template <typename A> struct DirectedEdge {
    A edge_from;
    A edge_to;
  };

  template <typename T1>
  static T1 edge_from(const std::shared_ptr<DirectedEdge<T1>> &d) {
    return d->edge_from;
  }

  template <typename T1>
  static T1 edge_to(const std::shared_ptr<DirectedEdge<T1>> &d) {
    return d->edge_to;
  }

  template <typename _tcI0, typename T1>
  static bool directed_originates(const T1 a,
                                  const std::shared_ptr<DirectedEdge<T1>> &e) {
    return _tcI0::eqb(e->edge_from, a);
  }

  template <typename A> struct Directed {
    std::shared_ptr<List<A>> directed_nodes;
    std::shared_ptr<List<std::shared_ptr<DirectedEdge<A>>>> directed_edges;
  };

  template <typename T1>
  static std::shared_ptr<List<T1>>
  directed_nodes(const std::shared_ptr<Directed<T1>> &d) {
    return d->directed_nodes;
  }

  template <typename T1>
  static std::shared_ptr<List<std::shared_ptr<DirectedEdge<T1>>>>
  directed_edges(const std::shared_ptr<Directed<T1>> &d) {
    return d->directed_edges;
  }

  template <typename _tcI0, typename T1>
  static std::shared_ptr<Graph<std::shared_ptr<Directed<std::any>>, T1>>
  DirectedGraph() {
    return std::make_shared<Graph<std::shared_ptr<Directed<std::any>>, T1>>(
        Graph<std::shared_ptr<Directed<std::any>>, T1>{
            std::make_shared<Directed<std::any>>(Directed<std::any>{
                List<std::any>::ctor::nil_(),
                List<std::shared_ptr<DirectedEdge<std::any>>>::ctor::nil_()}),
            [](std::shared_ptr<Directed<std::any>> g, _tcI0 n) {
              return std::make_shared<Directed<std::any>>(Directed<std::any>{
                  List<std::any>::ctor::cons_(n, g->directed_nodes),
                  g->directed_edges});
            },
            [](std::shared_ptr<Directed<std::any>> g, std::any e) {
              return std::make_shared<Directed<std::any>>(Directed<std::any>{
                  g->directed_nodes,
                  List<std::shared_ptr<DirectedEdge<std::any>>>::ctor::cons_(
                      e, g->directed_edges)});
            },
            [](std::shared_ptr<Directed<std::any>> g) {
              return g->directed_nodes;
            },
            [](std::shared_ptr<Directed<std::any>> g, _tcI0 n) {
              return
                  [&](void) {
                    dummy_type _x = g->directed_nodes;
                    std::shared_ptr<List<std::shared_ptr<DirectedEdge<T1>>>>
                        directed_edges0 = g->directed_edges;
                    return directed_edges0;
                  }()
                      ->filter(
                          [&](const std::shared_ptr<DirectedEdge<_tcI0>> _x0) {
                            return directed_originates<_tcI0, _tcI0>(n, _x0);
                          });
            }});
  }

  template <typename A> struct UndirectedEdge {
    A edge_first;
    A edge_second;
  };

  template <typename T1>
  static T1 edge_first(const std::shared_ptr<UndirectedEdge<T1>> &u) {
    return u->edge_first;
  }

  template <typename T1>
  static T1 edge_second(const std::shared_ptr<UndirectedEdge<T1>> &u) {
    return u->edge_second;
  }

  template <typename _tcI0, typename T1>
  static bool
  undirected_originates(const T1 a,
                        const std::shared_ptr<UndirectedEdge<T1>> &e) {
    return (_tcI0::eqb(e->edge_first, a) || _tcI0::eqb(e->edge_second, a));
  }

  template <typename A> struct Undirected {
    std::shared_ptr<List<A>> undirected_nodes;
    std::shared_ptr<List<std::shared_ptr<UndirectedEdge<A>>>> undirected_edges;
  };

  template <typename T1>
  static std::shared_ptr<List<T1>>
  undirected_nodes(const std::shared_ptr<Undirected<T1>> &u) {
    return u->undirected_nodes;
  }

  template <typename T1>
  static std::shared_ptr<List<std::shared_ptr<UndirectedEdge<T1>>>>
  undirected_edges(const std::shared_ptr<Undirected<T1>> &u) {
    return u->undirected_edges;
  }

  template <typename _tcI0, typename T1>
  static std::shared_ptr<Graph<std::shared_ptr<Undirected<std::any>>, T1>>
  UndirectedGraph() {
    return std::make_shared<Graph<std::shared_ptr<Undirected<std::any>>, T1>>(
        Graph<std::shared_ptr<Undirected<std::any>>, T1>{
            std::make_shared<Undirected<std::any>>(Undirected<std::any>{
                List<std::any>::ctor::nil_(),
                List<std::shared_ptr<UndirectedEdge<std::any>>>::ctor::nil_()}),
            [](std::shared_ptr<Undirected<std::any>> g, _tcI0 n) {
              return std::make_shared<Undirected<std::any>>(
                  Undirected<std::any>{
                      List<std::any>::ctor::cons_(n, g->undirected_nodes),
                      g->undirected_edges});
            },
            [](std::shared_ptr<Undirected<std::any>> g, std::any e) {
              return std::make_shared<
                  Undirected<std::any>>(Undirected<std::any>{
                  g->undirected_nodes,
                  List<std::shared_ptr<UndirectedEdge<std::any>>>::ctor::cons_(
                      e, g->undirected_edges)});
            },
            [](std::shared_ptr<Undirected<std::any>> g) {
              return g->undirected_nodes;
            },
            [](std::shared_ptr<Undirected<std::any>> g, _tcI0 n) {
              return
                  [&](void) {
                    dummy_type _x = g->undirected_nodes;
                    std::shared_ptr<List<std::shared_ptr<UndirectedEdge<T1>>>>
                        undirected_edges0 = g->undirected_edges;
                    return undirected_edges0;
                  }()
                      ->filter([&](const std::shared_ptr<UndirectedEdge<_tcI0>>
                                       _x0) {
                        return undirected_originates<_tcI0, _tcI0>(n, _x0);
                      });
            }});
  }
};
