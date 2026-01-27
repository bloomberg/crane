#include <algorithm>
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
    unsigned int length() const {
      return std::visit(
          Overloaded{
              [&](const typename List::list<A>::nil _args) -> unsigned int {
                return 0;
              },
              [&](const typename List::list<A>::cons _args) -> unsigned int {
                std::shared_ptr<List::list<A>> l_ = _args._a1;
                return (l_->length() + 1);
              }},
          this->v());
    }
    std::shared_ptr<List::list<A>>
    app(const std::shared_ptr<List::list<A>> &m) const {
      return std::visit(
          Overloaded{[&](const typename List::list<A>::nil _args)
                         -> std::shared_ptr<List::list<A>> { return m; },
                     [&](const typename List::list<A>::cons _args)
                         -> std::shared_ptr<List::list<A>> {
                       A a = _args._a0;
                       std::shared_ptr<List::list<A>> l1 = _args._a1;
                       return List::list<A>::ctor::cons_(a, l1->app(m));
                     }},
          this->v());
    }
  };
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
std::shared_ptr<List::list<T2>> map(F0 &&f,
                                    const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(Overloaded{[&](const typename List::list<T1>::nil _args)
                                   -> std::shared_ptr<List::list<T2>> {
                                 return List::list<T2>::ctor::nil_();
                               },
                               [&](const typename List::list<T1>::cons _args)
                                   -> std::shared_ptr<List::list<T2>> {
                                 T1 a = _args._a0;
                                 std::shared_ptr<List::list<T1>> l0 = _args._a1;
                                 return List::list<T2>::ctor::cons_(
                                     f(a), map<T1, T2>(f, l0));
                               }},
                    l->v());
}

std::shared_ptr<List::list<unsigned int>> seq(const unsigned int start,
                                              const unsigned int len);

template <typename T1>
std::shared_ptr<List::list<T1>>
concat(const std::shared_ptr<List::list<std::shared_ptr<List::list<T1>>>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<std::shared_ptr<List::list<T1>>>::nil
                  _args) -> std::shared_ptr<List::list<T1>> {
            return List::list<T1>::ctor::nil_();
          },
          [&](const typename List::list<std::shared_ptr<List::list<T1>>>::cons
                  _args) -> std::shared_ptr<List::list<T1>> {
            std::shared_ptr<List::list<T1>> x = _args._a0;
            std::shared_ptr<List::list<std::shared_ptr<List::list<T1>>>> l0 =
                _args._a1;
            return x->app(concat<T1>(l0));
          }},
      l->v());
}

template <typename T1, typename T2, MapsTo<T1, T2, T1> F0>
T1 fold_right(F0 &&f, const T1 a0, const std::shared_ptr<List::list<T2>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<T2>::nil _args) -> T1 { return a0; },
          [&](const typename List::list<T2>::cons _args) -> T1 {
            T2 b = _args._a0;
            std::shared_ptr<List::list<T2>> l0 = _args._a1;
            return f(b, fold_right<T1, T2>(f, a0, l0));
          }},
      l->v());
}

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

template <typename T1, MapsTo<bool, T1> F0>
std::optional<T1> find(F0 &&f, const std::shared_ptr<List::list<T1>> &l) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<T1>::nil _args) -> std::optional<T1> {
            return std::nullopt;
          },
          [&](const typename List::list<T1>::cons _args) -> std::optional<T1> {
            T1 x = _args._a0;
            std::shared_ptr<List::list<T1>> tl = _args._a1;
            if (f(x)) {
              return std::make_optional<T1>(x);
            } else {
              return find<T1>(f, tl);
            }
          }},
      l->v());
}

template <typename T1, typename T2>
std::shared_ptr<List::list<std::pair<T1, T2>>>
combine(const std::shared_ptr<List::list<T1>> &l,
        const std::shared_ptr<List::list<T2>> &l_) {
  return std::visit(
      Overloaded{
          [&](const typename List::list<T1>::nil _args)
              -> std::shared_ptr<List::list<std::pair<T1, T2>>> {
            return List::list<std::pair<T1, T2>>::ctor::nil_();
          },
          [&](const typename List::list<T1>::cons _args)
              -> std::shared_ptr<List::list<std::pair<T1, T2>>> {
            T1 x = _args._a0;
            std::shared_ptr<List::list<T1>> tl = _args._a1;
            return std::visit(
                Overloaded{
                    [&](const typename List::list<T2>::nil _args)
                        -> std::shared_ptr<List::list<std::pair<T1, T2>>> {
                      return List::list<std::pair<T1, T2>>::ctor::nil_();
                    },
                    [&](const typename List::list<T2>::cons _args)
                        -> std::shared_ptr<List::list<std::pair<T1, T2>>> {
                      T2 y = _args._a0;
                      std::shared_ptr<List::list<T2>> tl_ = _args._a1;
                      return List::list<std::pair<T1, T2>>::ctor::cons_(
                          std::make_pair(x, y), combine<T1, T2>(tl, tl_));
                    }},
                l_->v());
          }},
      l->v());
}

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> x) {
    T1 a = x.first;
    T2 b = x.second;
    return "(" + p1(a) + ", " + p2(b) + ")";
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string intersperse(F0 &&p, const std::string sep,
                                 const std::shared_ptr<List::list<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args) -> std::string {
              return "";
            },
            [&](const typename List::list<T1>::cons _args) -> std::string {
              T1 z = _args._a0;
              std::shared_ptr<List::list<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{[&](const typename List::list<T1>::nil _args)
                                 -> std::string { return sep + p(z); },
                             [&](const typename List::list<T1>::cons _args)
                                 -> std::string {
                               return sep + p(z) + intersperse<T1>(p, sep, l_);
                             }},
                  l_->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string list_to_string(F0 &&p,
                                    const std::shared_ptr<List::list<T1>> &l) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<T1>::nil _args) -> std::string {
              return "[]";
            },
            [&](const typename List::list<T1>::cons _args) -> std::string {
              T1 y = _args._a0;
              std::shared_ptr<List::list<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{[&](const typename List::list<T1>::nil _args)
                                 -> std::string { return "[" + p(y) + "]"; },
                             [&](const typename List::list<T1>::cons _args)
                                 -> std::string {
                               return "[" + p(y) +
                                      intersperse<T1>(p, "; ", l_) + "]";
                             }},
                  l_->v());
            }},
        l->v());
  }
};

struct TopSort {
  template <typename node>
  using entry = std::pair<node, std::shared_ptr<List::list<node>>>;

  template <typename node>
  using graph = std::shared_ptr<List::list<entry<node>>>;

  template <typename node>
  using order = std::shared_ptr<List::list<std::shared_ptr<List::list<node>>>>;

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<T1>>
  get_elems(F0 &&eqb_node,
            const std::shared_ptr<List::list<std::pair<T1, T1>>> &l) {
    std::function<std::shared_ptr<List::list<T1>>(
        std::shared_ptr<List::list<std::pair<T1, T1>>>,
        std::shared_ptr<List::list<T1>>)>
        get_elems_aux;
    get_elems_aux = [&](std::shared_ptr<List::list<std::pair<T1, T1>>> l0,
                        std::shared_ptr<List::list<T1>> h)
        -> std::shared_ptr<List::list<T1>> {
      return std::visit(
          Overloaded{
              [&](const typename List::list<std::pair<T1, T1>>::nil _args)
                  -> std::shared_ptr<List::list<T1>> { return h; },
              [&](const typename List::list<std::pair<T1, T1>>::cons _args)
                  -> std::shared_ptr<List::list<T1>> {
                std::pair<T1, T1> p = _args._a0;
                std::shared_ptr<List::list<std::pair<T1, T1>>> l_ = _args._a1;
                T1 e1 = p.first;
                T1 e2 = p.second;
                std::optional<T1> f1 =
                    find<T1>([&](T1 x) { return eqb_node(e1, x); }, h);
                std::optional<T1> f2 =
                    find<T1>([&](T1 x) { return eqb_node(e2, x); }, h);
                if (f1.has_value()) {
                  T1 _x = *f1;
                  if (f2.has_value()) {
                    T1 _x0 = *f2;
                    return get_elems_aux(l_, h);
                  } else {
                    return get_elems_aux(l_,
                                         List::list<T1>::ctor::cons_(e2, h));
                  }
                } else {
                  if (f2.has_value()) {
                    T1 _x = *f2;
                    return get_elems_aux(l_,
                                         List::list<T1>::ctor::cons_(e1, h));
                  } else {
                    if (eqb_node(e1, e2)) {
                      return get_elems_aux(l_,
                                           List::list<T1>::ctor::cons_(e1, h));
                    } else {
                      return get_elems_aux(
                          l_, List::list<T1>::ctor::cons_(
                                  e1, List::list<T1>::ctor::cons_(e2, h)));
                    }
                  }
                }
              }},
          l0->v());
    };
    return get_elems_aux(l, List::list<T1>::ctor::nil_());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static entry<T1>
  make_entry(F0 &&eqb_node,
             const std::shared_ptr<List::list<std::pair<T1, T1>>> &l,
             const T1 e) {
    return std::make_pair(
        e, fold_right<std::shared_ptr<List::list<T1>>, std::pair<T1, T1>>(
               [&](std::pair<T1, T1> x, std::shared_ptr<List::list<T1>> ret) {
                 if (eqb_node(e, x.first)) {
                   return List::list<T1>::ctor::cons_(x.second, ret);
                 } else {
                   return ret;
                 }
               },
               List::list<T1>::ctor::nil_(), l));
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static graph<T1>
  make_graph(F0 &&eqb_node,
             const std::shared_ptr<List::list<std::pair<T1, T1>>> &l) {
    std::shared_ptr<List::list<T1>> elems = get_elems<T1>(eqb_node, l);
    return fold_right<std::shared_ptr<List::list<entry<T1>>>, T1>(
        [&](T1 e,
            std::shared_ptr<
                List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>>
                ret) {
          return List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>::
              ctor::cons_(make_entry<T1>(eqb_node, l, e), ret);
        },
        List::list<
            std::pair<T1, std::shared_ptr<List::list<T1>>>>::ctor::nil_(),
        elems);
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<T1>> graph_lookup(
      F0 &&eqb_node, const T1 elem,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0) {
    if (find<std::pair<T1, std::shared_ptr<List::list<T1>>>>(
            [&](std::pair<T1, std::shared_ptr<List::list<T1>>> entry0) {
              return eqb_node(elem, entry0.first);
            },
            graph0)
            .has_value()) {
      std::pair<T1, std::shared_ptr<List::list<T1>>> p =
          *find<std::pair<T1, std::shared_ptr<List::list<T1>>>>(
              [&](std::pair<T1, std::shared_ptr<List::list<T1>>> entry0) {
                return eqb_node(elem, entry0.first);
              },
              graph0);
      T1 _x = p.first;
      std::shared_ptr<List::list<T1>> es = p.second;
      return es;
    } else {
      return List::list<T1>::ctor::nil_();
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bool contains(F0 &&eqb_node, const T1 elem,
                       const std::shared_ptr<List::list<T1>> &es) {
    if (find<T1>([&](T1 x) { return eqb_node(elem, x); }, es).has_value()) {
      T1 _x = *find<T1>([&](T1 x) { return eqb_node(elem, x); }, es);
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static T1 cycle_entry_aux(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0,
      const std::shared_ptr<List::list<T1>> &seens, const T1 elem,
      const unsigned int counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        unsigned int c = counter - 1;
        std::shared_ptr<List::list<T1>> l =
            graph_lookup<T1>(eqb_node, elem, graph0);
        return std::visit(
            Overloaded{[&](const typename List::list<T1>::nil _args) -> T1 {
                         return elem;
                       },
                       [&](const typename List::list<T1>::cons _args) -> T1 {
                         T1 e_ = _args._a0;
                         return cycle_entry_aux<T1>(
                             eqb_node, graph0,
                             List::list<T1>::ctor::cons_(elem, seens), e_, c);
                       }},
            l->v());
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::optional<T1> cycle_entry(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0) {
    return std::visit(
        Overloaded{
            [&](const typename List::list<
                std::pair<T1, std::shared_ptr<List::list<T1>>>>::nil _args)
                -> std::optional<T1> { return std::nullopt; },
            [&](const typename List::list<
                std::pair<T1, std::shared_ptr<List::list<T1>>>>::cons _args)
                -> std::optional<T1> {
              std::pair<T1, std::shared_ptr<List::list<T1>>> e0 = _args._a0;
              T1 e = e0.first;
              std::shared_ptr<List::list<T1>> _x0 = e0.second;
              return std::make_optional<T1>(cycle_entry_aux<T1>(
                  eqb_node, graph0, List::list<T1>::ctor::nil_(), e,
                  graph0->length()));
            }},
        graph0->v());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<T1>> cycle_extract_aux(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0,
      const unsigned int counter, const T1 elem,
      const std::shared_ptr<List::list<T1>> &cycl) {
    if (counter <= 0) {
      return cycl;
    } else {
      unsigned int c = counter - 1;
      if (contains<T1>(eqb_node, elem, cycl)) {
        return cycl;
      } else {
        return fold_right<std::shared_ptr<List::list<T1>>, T1>(
            [&](const T1 _x0, const std::shared_ptr<List::list<T1>> _x1) {
              return cycle_extract_aux<T1>(eqb_node, graph0, c, _x0, _x1);
            },
            List::list<T1>::ctor::cons_(elem, cycl),
            graph_lookup<T1>(eqb_node, elem, graph0));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<T1>> cycle_extract(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0) {
    if (cycle_entry<T1>(eqb_node, graph0).has_value()) {
      T1 elem = *cycle_entry<T1>(eqb_node, graph0);
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0->length(), elem,
                                   List::list<T1>::ctor::nil_());
    } else {
      return List::list<T1>::ctor::nil_();
    }
  }

  template <typename T1>
  static bool null(const std::shared_ptr<List::list<T1>> &xs) {
    return std::visit(
        Overloaded{[&](const typename List::list<T1>::nil _args) -> bool {
                     return true;
                   },
                   [&](const typename List::list<T1>::cons _args) -> bool {
                     return false;
                   }},
        xs->v());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static order<T1> topological_sort_aux(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0,
      const unsigned int counter) {
    if (counter <= 0) {
      return List::list<std::shared_ptr<List::list<T1>>>::ctor::nil_();
    } else {
      unsigned int c = counter - 1;
      if (null<entry<T1>>(graph0)) {
        return List::list<std::shared_ptr<List::list<T1>>>::ctor::nil_();
      } else {
        std::shared_ptr<List::list<T1>> mins =
            map<std::pair<T1, std::shared_ptr<List::list<T1>>>, T1>(
                [&](const std::pair<T1, std::shared_ptr<List::list<T1>>> _x0) {
                  return _x0.first;
                },
                filter<std::pair<T1, std::shared_ptr<List::list<T1>>>>(
                    [&](std::pair<T1, std::shared_ptr<List::list<T1>>> p) {
                      return null<T1>(p.second);
                    },
                    graph0));
        std::shared_ptr<List::list<T1>> mins_;
        if (null<T1>(mins)) {
          mins_ = cycle_extract<T1>(eqb_node, graph0);
        } else {
          mins_ = mins;
        }
        std::shared_ptr<
            List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>>
            rest = filter<std::pair<T1, std::shared_ptr<List::list<T1>>>>(
                [&](std::pair<T1, std::shared_ptr<List::list<T1>>> entry0) {
                  return !(contains<T1>(eqb_node, entry0.first, mins_));
                },
                graph0);
        std::shared_ptr<
            List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>>
            rest_ = map<std::pair<T1, std::shared_ptr<List::list<T1>>>,
                        std::pair<T1, std::shared_ptr<List::list<T1>>>>(
                [&](std::pair<T1, std::shared_ptr<List::list<T1>>> entry0) {
                  return std::make_pair(
                      entry0.first,
                      filter<T1>(
                          [&](T1 e) {
                            return !(contains<T1>(eqb_node, e, mins_));
                          },
                          entry0.second));
                },
                rest);
        return List::list<std::shared_ptr<List::list<T1>>>::ctor::cons_(
            mins_, topological_sort_aux<T1>(eqb_node, rest_, c));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<std::shared_ptr<List::list<T1>>>>
  topological_sort(F0 &&eqb_node,
                   const std::shared_ptr<List::list<std::pair<T1, T1>>> &g) {
    std::shared_ptr<List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>>
        g_ = make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_->length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static order<T1> topological_sort_graph(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0->length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List::list<std::pair<T1, unsigned int>>>
  topological_rank_list(
      F0 &&eqb_node,
      const std::shared_ptr<
          List::list<std::pair<T1, std::shared_ptr<List::list<T1>>>>> &graph0) {
    std::shared_ptr<List::list<std::shared_ptr<List::list<T1>>>> lorder =
        topological_sort_graph<T1>(eqb_node, graph0);
    return concat<std::pair<T1, unsigned int>>(
        map<std::pair<std::shared_ptr<List::list<T1>>, unsigned int>,
            std::shared_ptr<List::list<std::pair<T1, unsigned int>>>>(
            [&](std::pair<std::shared_ptr<List::list<T1>>, unsigned int> x) {
              std::shared_ptr<List::list<T1>> fs = x.first;
              unsigned int rk = x.second;
              return map<T1, std::pair<T1, unsigned int>>(
                  [&](T1 f) { return std::make_pair(f, rk); }, fs);
            },
            combine<std::shared_ptr<List::list<T1>>, unsigned int>(
                lorder, seq(0, lorder->length()))));
  }
};
