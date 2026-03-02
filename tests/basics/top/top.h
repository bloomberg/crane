#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
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
  template <typename T1, MapsTo<T1, A> F0>
  std::shared_ptr<List<T1>> map(F0 &&f) const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> std::shared_ptr<List<T1>> {
              return List<T1>::ctor::nil_();
            },
            [&](const typename List<A>::cons _args)
                -> std::shared_ptr<List<T1>> {
              A a = _args._a0;
              std::shared_ptr<List<A>> l0 = _args._a1;
              return List<T1>::ctor::cons_(f(a),
                                           std::move(l0)->template map<T1>(f));
            }},
        this->v());
  }
  template <typename T1> std::shared_ptr<List<T1>> concat() const {
    return std::visit(
        Overloaded{
            [](const typename List<std::shared_ptr<List<T1>>>::nil _args)
                -> std::shared_ptr<List<T1>> { return List<T1>::ctor::nil_(); },
            [](const typename List<std::shared_ptr<List<T1>>>::cons _args)
                -> std::shared_ptr<List<T1>> {
              std::shared_ptr<List<T1>> x = _args._a0;
              std::shared_ptr<List<std::shared_ptr<List<T1>>>> l0 = _args._a1;
              return std::move(x)->app(std::move(l0)->template concat<T1>());
            }},
        this->v());
  }
  template <typename T1, MapsTo<T1, A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    return std::visit(
        Overloaded{[&](const typename List<A>::nil _args) -> T1 { return a0; },
                   [&](const typename List<A>::cons _args) -> T1 {
                     A b = _args._a0;
                     std::shared_ptr<List<A>> l0 = _args._a1;
                     return f(b, std::move(l0)->template fold_right<T1>(f, a0));
                   }},
        this->v());
  }
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
  template <MapsTo<bool, A> F0> std::optional<A> find(F0 &&f) const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args) -> std::optional<A> {
                     return std::nullopt;
                   },
                   [&](const typename List<A>::cons _args) -> std::optional<A> {
                     A x = _args._a0;
                     std::shared_ptr<List<A>> tl = _args._a1;
                     if (f(x)) {
                       return std::make_optional<A>(x);
                     } else {
                       return std::move(tl)->find(f);
                     }
                   }},
        this->v());
  }
  template <typename T1>
  std::shared_ptr<List<std::pair<A, T1>>>
  combine(const std::shared_ptr<List<T1>> &l_) const {
    return std::visit(
        Overloaded{[](const typename List<A>::nil _args)
                       -> std::shared_ptr<List<std::pair<A, T1>>> {
                     return List<std::pair<A, T1>>::ctor::nil_();
                   },
                   [&](const typename List<A>::cons _args)
                       -> std::shared_ptr<List<std::pair<A, T1>>> {
                     A x = _args._a0;
                     std::shared_ptr<List<A>> tl = _args._a1;
                     return std::visit(
                         Overloaded{
                             [](const typename List<T1>::nil _args)
                                 -> std::shared_ptr<List<std::pair<A, T1>>> {
                               return List<std::pair<A, T1>>::ctor::nil_();
                             },
                             [&](const typename List<T1>::cons _args)
                                 -> std::shared_ptr<List<std::pair<A, T1>>> {
                               T1 y = _args._a0;
                               std::shared_ptr<List<T1>> tl_ = _args._a1;
                               return List<std::pair<A, T1>>::ctor::cons_(
                                   std::make_pair(x, y),
                                   std::move(tl)->template combine<T1>(
                                       std::move(tl_)));
                             }},
                         l_->v());
                   }},
        this->v());
  }
  unsigned int length() const {
    return std::visit(
        Overloaded{
            [](const typename List<A>::nil _args) -> unsigned int { return 0; },
            [](const typename List<A>::cons _args) -> unsigned int {
              std::shared_ptr<List<A>> l_ = _args._a1;
              return (std::move(l_)->length() + 1);
            }},
        this->v());
  }
  std::shared_ptr<List<A>> app(const std::shared_ptr<List<A>> &m) const {
    return std::visit(Overloaded{[&](const typename List<A>::nil _args)
                                     -> std::shared_ptr<List<A>> { return m; },
                                 [&](const typename List<A>::cons _args)
                                     -> std::shared_ptr<List<A>> {
                                   A a = _args._a0;
                                   std::shared_ptr<List<A>> l1 = _args._a1;
                                   return List<A>::ctor::cons_(
                                       a, std::move(l1)->app(m));
                                 }},
                      this->v());
  }
};

struct ListDef {
  static std::shared_ptr<List<unsigned int>> seq(const unsigned int start,
                                                 const unsigned int len);
};

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
                                 const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::nil _args) -> std::string {
              return "";
            },
            [&](const typename List<T1>::cons _args) -> std::string {
              T1 z = _args._a0;
              std::shared_ptr<List<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::nil _args) -> std::string {
                        return sep + p(z);
                      },
                      [&](const typename List<T1>::cons _args) -> std::string {
                        return sep + p(z) +
                               intersperse<T1>(p, sep, std::move(l_));
                      }},
                  l_->v());
            }},
        l->v());
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string list_to_string(F0 &&p,
                                    const std::shared_ptr<List<T1>> &l) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::nil _args) -> std::string {
              return "[]";
            },
            [&](const typename List<T1>::cons _args) -> std::string {
              T1 y = _args._a0;
              std::shared_ptr<List<T1>> l_ = _args._a1;
              return std::visit(
                  Overloaded{
                      [&](const typename List<T1>::nil _args) -> std::string {
                        return "[" + p(y) + "]";
                      },
                      [&](const typename List<T1>::cons _args) -> std::string {
                        return "[" + p(y) +
                               intersperse<T1>(p, "; ", std::move(l_)) + "]";
                      }},
                  l_->v());
            }},
        l->v());
  }
};

struct TopSort {
  template <typename node>
  using entry = std::pair<node, std::shared_ptr<List<node>>>;

  template <typename node> using graph = std::shared_ptr<List<entry<node>>>;

  template <typename node>
  using order = std::shared_ptr<List<std::shared_ptr<List<node>>>>;

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<T1>>
  get_elems(F0 &&eqb_node, const std::shared_ptr<List<std::pair<T1, T1>>> &l) {
    std::function<std::shared_ptr<List<T1>>(
        std::shared_ptr<List<std::pair<T1, T1>>>, std::shared_ptr<List<T1>>)>
        get_elems_aux;
    get_elems_aux =
        [&](std::shared_ptr<List<std::pair<T1, T1>>> l0,
            std::shared_ptr<List<T1>> h) -> std::shared_ptr<List<T1>> {
      return std::visit(
          Overloaded{[&](const typename List<std::pair<T1, T1>>::nil _args)
                         -> std::shared_ptr<List<T1>> { return std::move(h); },
                     [&](const typename List<std::pair<T1, T1>>::cons _args)
                         -> std::shared_ptr<List<T1>> {
                       std::pair<T1, T1> p = _args._a0;
                       std::shared_ptr<List<std::pair<T1, T1>>> l_ = _args._a1;
                       T1 e1 = p.first;
                       T1 e2 = p.second;
                       std::optional<T1> f1 =
                           h->find([&](T1 x) { return eqb_node(e1, x); });
                       std::optional<T1> f2 =
                           h->find([&](T1 x) { return eqb_node(e2, x); });
                       if (f1.has_value()) {
                         T1 _x = *f1;
                         if (f2.has_value()) {
                           T1 _x0 = *f2;
                           return get_elems_aux(l_, h);
                         } else {
                           return get_elems_aux(
                               l_, List<T1>::ctor::cons_(std::move(e2), h));
                         }
                       } else {
                         if (f2.has_value()) {
                           T1 _x = *f2;
                           return get_elems_aux(
                               l_, List<T1>::ctor::cons_(std::move(e1), h));
                         } else {
                           if (eqb_node(e1, e2)) {
                             return get_elems_aux(
                                 std::move(l_),
                                 List<T1>::ctor::cons_(std::move(e1), h));
                           } else {
                             return get_elems_aux(
                                 std::move(l_),
                                 List<T1>::ctor::cons_(
                                     std::move(e1),
                                     List<T1>::ctor::cons_(std::move(e2), h)));
                           }
                         }
                       }
                     }},
          l0->v());
    };
    return get_elems_aux(l, List<T1>::ctor::nil_());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static entry<T1> make_entry(F0 &&eqb_node,
                              std::shared_ptr<List<std::pair<T1, T1>>> l,
                              const T1 e) {
    return std::make_pair(
        e, std::move(l)->template fold_right<std::shared_ptr<List<T1>>>(
               [&](std::pair<T1, T1> x, std::shared_ptr<List<T1>> ret) {
                 if (eqb_node(e, x.first)) {
                   return List<T1>::ctor::cons_(x.second, ret);
                 } else {
                   return ret;
                 }
               },
               List<T1>::ctor::nil_()));
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static graph<T1> make_graph(F0 &&eqb_node,
                              std::shared_ptr<List<std::pair<T1, T1>>> l) {
    std::shared_ptr<List<T1>> elems = get_elems<T1>(eqb_node, std::move(l));
    return std::move(elems)
        ->template fold_right<std::shared_ptr<List<entry<T1>>>>(
            [&](T1 e,
                std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
                    ret) {
              return List<std::pair<T1, std::shared_ptr<List<T1>>>>::ctor::
                  cons_(make_entry<T1>(eqb_node, l, e), ret);
            },
            List<std::pair<T1, std::shared_ptr<List<T1>>>>::ctor::nil_());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<T1>> graph_lookup(
      F0 &&eqb_node, const T1 elem,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0) {
    if (graph0
            ->find([&](std::pair<T1, std::shared_ptr<List<T1>>> entry0) {
              return eqb_node(elem, entry0.first);
            })
            .has_value()) {
      std::pair<T1, std::shared_ptr<List<T1>>> p =
          *graph0->find([&](std::pair<T1, std::shared_ptr<List<T1>>> entry0) {
            return eqb_node(elem, entry0.first);
          });
      T1 _x = p.first;
      std::shared_ptr<List<T1>> es = p.second;
      return es;
    } else {
      return List<T1>::ctor::nil_();
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bool contains(F0 &&eqb_node, const T1 elem,
                       const std::shared_ptr<List<T1>> &es) {
    if (es->find([&](T1 x) { return eqb_node(elem, x); }).has_value()) {
      T1 _x = *es->find([&](T1 x) { return eqb_node(elem, x); });
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static T1 cycle_entry_aux(
      F0 &&eqb_node,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0,
      std::shared_ptr<List<T1>> seens, const T1 elem,
      const unsigned int counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        unsigned int c = counter - 1;
        std::shared_ptr<List<T1>> l =
            graph_lookup<T1>(eqb_node, std::move(elem), graph0);
        return std::visit(
            Overloaded{[&](const typename List<T1>::nil _args) -> T1 {
                         return std::move(elem);
                       },
                       [&](const typename List<T1>::cons _args) -> T1 {
                         T1 e_ = _args._a0;
                         return cycle_entry_aux<T1>(
                             eqb_node, graph0,
                             List<T1>::ctor::cons_(std::move(elem), seens), e_,
                             c);
                       }},
            std::move(l)->v());
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::optional<T1> cycle_entry(
      F0 &&eqb_node,
      std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>> graph0) {
    return std::visit(
        Overloaded{[](const typename List<
                       std::pair<T1, std::shared_ptr<List<T1>>>>::nil _args)
                       -> std::optional<T1> { return std::nullopt; },
                   [&](const typename List<
                       std::pair<T1, std::shared_ptr<List<T1>>>>::cons _args)
                       -> std::optional<T1> {
                     std::pair<T1, std::shared_ptr<List<T1>>> e0 = _args._a0;
                     T1 e = e0.first;
                     std::shared_ptr<List<T1>> _x0 = e0.second;
                     return std::make_optional<T1>(cycle_entry_aux<T1>(
                         eqb_node, graph0, List<T1>::ctor::nil_(), std::move(e),
                         graph0->length()));
                   }},
        graph0->v());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<T1>> cycle_extract_aux(
      F0 &&eqb_node,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0,
      const unsigned int counter, const T1 elem,
      std::shared_ptr<List<T1>> cycl) {
    if (counter <= 0) {
      return std::move(cycl);
    } else {
      unsigned int c = counter - 1;
      if (contains<T1>(eqb_node, elem, cycl)) {
        return cycl;
      } else {
        return graph_lookup<T1>(eqb_node, elem, graph0)
            ->template fold_right<std::shared_ptr<List<T1>>>(
                [&](const T1 _x0, const std::shared_ptr<List<T1>> _x1) {
                  return cycle_extract_aux<T1>(eqb_node, graph0, std::move(c),
                                               _x0, _x1);
                },
                List<T1>::ctor::cons_(elem, cycl));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<T1>> cycle_extract(
      F0 &&eqb_node,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0) {
    if (cycle_entry<T1>(eqb_node, graph0).has_value()) {
      T1 elem = *cycle_entry<T1>(eqb_node, graph0);
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0->length(), elem,
                                   List<T1>::ctor::nil_());
    } else {
      return List<T1>::ctor::nil_();
    }
  }

  template <typename T1> static bool null(const std::shared_ptr<List<T1>> &xs) {
    return std::visit(
        Overloaded{
            [](const typename List<T1>::nil _args) -> bool { return true; },
            [](const typename List<T1>::cons _args) -> bool { return false; }},
        xs->v());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static order<T1> topological_sort_aux(
      F0 &&eqb_node,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0,
      const unsigned int counter) {
    if (counter <= 0) {
      return List<std::shared_ptr<List<T1>>>::ctor::nil_();
    } else {
      unsigned int c = counter - 1;
      if (null<entry<T1>>(graph0)) {
        return List<std::shared_ptr<List<T1>>>::ctor::nil_();
      } else {
        std::shared_ptr<List<T1>> mins =
            graph0
                ->filter([](std::pair<T1, std::shared_ptr<List<T1>>> p) {
                  return null<T1>(p.second);
                })
                ->template map<T1>(
                    [](const std::pair<T1, std::shared_ptr<List<T1>>> _x0) {
                      return _x0.first;
                    });
        std::shared_ptr<List<T1>> mins_;
        if (null<T1>(mins)) {
          mins_ = cycle_extract<T1>(eqb_node, graph0);
        } else {
          mins_ = std::move(mins);
        }
        std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>> rest =
            graph0->filter(
                [&](std::pair<T1, std::shared_ptr<List<T1>>> entry0) {
                  return !(contains<T1>(eqb_node, entry0.first, mins_));
                });
        std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>> rest_ =
            std::move(rest)
                ->template map<std::pair<T1, std::shared_ptr<List<T1>>>>(
                    [&](std::pair<T1, std::shared_ptr<List<T1>>> entry0) {
                      return std::make_pair(
                          entry0.first, entry0.second->filter([&](T1 e) {
                            return !(contains<T1>(eqb_node, e, mins_));
                          }));
                    });
        return List<std::shared_ptr<List<T1>>>::ctor::cons_(
            std::move(mins_),
            topological_sort_aux<T1>(eqb_node, std::move(rest_), c));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<std::shared_ptr<List<T1>>>>
  topological_sort(F0 &&eqb_node,
                   const std::shared_ptr<List<std::pair<T1, T1>>> &g) {
    std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>> g_ =
        make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_->length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static order<T1> topological_sort_graph(
      F0 &&eqb_node,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0->length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::shared_ptr<List<std::pair<T1, unsigned int>>>
  topological_rank_list(
      F0 &&eqb_node,
      const std::shared_ptr<List<std::pair<T1, std::shared_ptr<List<T1>>>>>
          &graph0) {
    std::shared_ptr<List<std::shared_ptr<List<T1>>>> lorder =
        topological_sort_graph<T1>(eqb_node, graph0);
    return lorder
        ->template combine<unsigned int>(ListDef::seq(0, lorder->length()))
        ->template map<std::shared_ptr<List<std::pair<T1, unsigned int>>>>(
            [](std::pair<std::shared_ptr<List<T1>>, unsigned int> x) {
              std::shared_ptr<List<T1>> fs = x.first;
              unsigned int rk = x.second;
              return fs->template map<std::pair<T1, unsigned int>>(
                  [&](T1 f) { return std::make_pair(f, rk); });
            })
        ->template concat<std::pair<T1, unsigned int>>();
  }
};
