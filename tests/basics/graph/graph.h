#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct List {
  template <typename A> struct list {
  public:
    struct nil {};
    struct cons {
      A _a0;
      std::shared_ptr<List::list<A>> _a1;
    };
    using variant_t = std::variant<nil, cons>;

  private:
    variant_t v_;
    explicit list(nil x) : v_(std::move(x)) {}
    explicit list(cons x) : v_(std::move(x)) {}

  public:
    struct ctor {
      ctor() = delete;
      static std::shared_ptr<List::list<A>> nil_() {
        return std::shared_ptr<List::list<A>>(new List::list<A>(nil{}));
      }
      static std::shared_ptr<List::list<A>>
      cons_(A a0, const std::shared_ptr<List::list<A>> &a1) {
        return std::shared_ptr<List::list<A>>(new List::list<A>(cons{a0, a1}));
      }
    };
    const variant_t &v() const { return v_; }
  };
};

template <typename T1, MapsTo<bool, T1> F0>
std::shared_ptr<List::list<T1>>
filter(F0 &&f, const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[&](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 return List::list<T1>::ctor::nil_();
                               },
                               [&](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T1>> {
                                 T1 x = _args._a0;
                                 std::shared_ptr<List::list<T1>> l0 = _args._a1;
                                 if (f(x)) {
                                   return List::list<T1>::ctor::cons_(
                                       x, filter<T1>(f, l0));
                                 } else {
                                   return filter<T1>(f, l0);
                                 }
                               }},
                    l->v());
}

template <typename I, typename A>
concept Eq = requires(A a0, A a1) {
  { I::eqb(a1, a0) } -> std::convertible_to<bool>;
};
template <typename I, typename G, typename A>
concept Graph = requires(G a0, A a1, unknown a1) {
  { I::empty() } -> std::convertible_to<G>;
  { I::add_node(a1, a0) } -> std::convertible_to<G>;
  { I::add_edge(a1, a0) } -> std::convertible_to<G>;
  { I::nodes(a0) } -> std::convertible_to<std::shared_ptr<List::list<A>>>;
  {
    I::edges(a1, a0)
  } -> std::convertible_to<std::shared_ptr<List::list<unknown>>>;
};

struct Graph {
  template <typename _tcI0, typename T1>
  static bool eqb(const T1 _x0, const T1 _x1) {
    return _tcI0::eqb(_x0, _x1);
  }

  template <typename g, typename a> using edge = unknown;

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
  static std::shared_ptr<List::list<T2>> nodes(const T1 _x0) {
    return _tcI0::nodes(_x0);
  }

  template <typename _tcI0, typename T1, typename T2>
  static std::shared_ptr<List::list<edge<T1, T2>>> edges(const T2 _x0,
                                                         const T1 _x1) {
    return _tcI0::edges(_x0, _x1);
  }

  template <typename A> struct directedEdge {
    A edge_from;
    A edge_to;
  };

  template <typename T1>
  static T1 edge_from(const std::shared_ptr<directedEdge<T1>> &d) {
    return d->edge_from;
  }

  template <typename T1>
  static T1 edge_to(const std::shared_ptr<directedEdge<T1>> &d) {
    return d->edge_to;
  }

  template <typename _tcI0, typename T1>
  static bool directed_originates(const T1 a,
                                  const std::shared_ptr<directedEdge<T1>> &e) {
    return _tcI0::eqb(e->edge_from, a);
  }

  template <typename A> struct directed {
    std::shared_ptr<List::list<A>> directed_nodes;
    std::shared_ptr<List::list<std::shared_ptr<directedEdge<A>>>>
        directed_edges;
  };

  template <typename T1>
  static std::shared_ptr<List::list<T1>>
  directed_nodes(const std::shared_ptr<directed<T1>> &d) {
    return d->directed_nodes;
  }

  template <typename T1>
  static std::shared_ptr<List::list<std::shared_ptr<directedEdge<T1>>>>
  directed_edges(const std::shared_ptr<directed<T1>> &d) {
    return d->directed_edges;
  }

  template <typename _tcI0, typename T1>
  static std::shared_ptr<graph<std::shared_ptr<directed<unknown>>, T1>>
  DirectedGraph() {
    return std::make_shared<graph<std::shared_ptr<directed<unknown>>,
                                  T1>>(Graph<std::shared_ptr<directed<unknown>>,
                                             T1>{
        std::make_shared<directed<unknown>>(Directed<unknown>{
            List::list<unknown>::ctor::nil_(),
            List::list<std::shared_ptr<directedEdge<unknown>>>::ctor::nil_()}),
        [&](std::shared_ptr<directed<unknown>> g, T1 n) {
          return std::make_shared<directed<unknown>>(Directed<unknown>{
              List::list<unknown>::ctor::cons_(n, g->directed_nodes),
              g->directed_edges});
        },
        [&](std::shared_ptr<directed<unknown>> g, unknown e) {
          return std::make_shared<directed<unknown>>(Directed<unknown>{
              g->directed_nodes,
              List::list<std::shared_ptr<directedEdge<unknown>>>::ctor::cons_(
                  e, g->directed_edges)});
        },
        [&](std::shared_ptr<directed<unknown>> g) { return g->directed_nodes; },
        [&](std::shared_ptr<directed<unknown>> g, T1 n) {
          return filter<std::shared_ptr<directedEdge<T1>>>(
              [&](const std::shared_ptr<directedEdge<T1>> _x0) {
                return directed_originates<_tcI0, T1>(n, _x0);
              },
              [&](void) {
                dummy_type _x = g->directed_nodes;
                std::shared_ptr<List::list<std::shared_ptr<directedEdge<T1>>>>
                    directed_edges = g->directed_edges;
                return directed_edges0;
              }());
        }});
  }

  template <typename A> struct undirectedEdge {
    A edge_first;
    A edge_second;
  };

  template <typename T1>
  static T1 edge_first(const std::shared_ptr<undirectedEdge<T1>> &u) {
    return u->edge_first;
  }

  template <typename T1>
  static T1 edge_second(const std::shared_ptr<undirectedEdge<T1>> &u) {
    return u->edge_second;
  }

  template <typename _tcI0, typename T1>
  static bool
  undirected_originates(const T1 a,
                        const std::shared_ptr<undirectedEdge<T1>> &e) {
    return (_tcI0::eqb(e->edge_first, a) || _tcI0::eqb(e->edge_second, a));
  }

  template <typename A> struct undirected {
    std::shared_ptr<List::list<A>> undirected_nodes;
    std::shared_ptr<List::list<std::shared_ptr<undirectedEdge<A>>>>
        undirected_edges;
  };

  template <typename T1>
  static std::shared_ptr<List::list<T1>>
  undirected_nodes(const std::shared_ptr<undirected<T1>> &u) {
    return u->undirected_nodes;
  }

  template <typename T1>
  static std::shared_ptr<List::list<std::shared_ptr<undirectedEdge<T1>>>>
  undirected_edges(const std::shared_ptr<undirected<T1>> &u) {
    return u->undirected_edges;
  }

  template <typename _tcI0, typename T1>
  static std::shared_ptr<graph<std::shared_ptr<undirected<unknown>>, T1>>
  UndirectedGraph() {
    return std::make_shared<
        graph<std::shared_ptr<undirected<unknown>>,
              T1>>(Graph<std::shared_ptr<undirected<unknown>>, T1>{
        std::make_shared<undirected<unknown>>(Undirected<unknown>{
            List::list<unknown>::ctor::nil_(),
            List::list<
                std::shared_ptr<undirectedEdge<unknown>>>::ctor::nil_()}),
        [&](std::shared_ptr<undirected<unknown>> g, T1 n) {
          return std::make_shared<undirected<unknown>>(Undirected<unknown>{
              List::list<unknown>::ctor::cons_(n, g->undirected_nodes),
              g->undirected_edges});
        },
        [&](std::shared_ptr<undirected<unknown>> g, unknown e) {
          return std::make_shared<undirected<unknown>>(Undirected<unknown>{
              g->undirected_nodes,
              List::list<std::shared_ptr<undirectedEdge<unknown>>>::ctor::cons_(
                  e, g->undirected_edges)});
        },
        [&](std::shared_ptr<undirected<unknown>> g) {
          return g->undirected_nodes;
        },
        [&](std::shared_ptr<undirected<unknown>> g, T1 n) {
          return filter<std::shared_ptr<undirectedEdge<T1>>>(
              [&](const std::shared_ptr<undirectedEdge<T1>> _x0) {
                return undirected_originates<_tcI0, T1>(n, _x0);
              },
              [&](void) {
                dummy_type _x = g->undirected_nodes;
                std::shared_ptr<List::list<std::shared_ptr<undirectedEdge<T1>>>>
                    undirected_edges = g->undirected_edges;
                return undirected_edges0;
              }());
        }});
  }
};
