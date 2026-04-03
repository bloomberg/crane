#ifndef INCLUDED_TOPOLOGICAL_SORT_BDE
#define INCLUDED_TOPOLOGICAL_SORT_BDE

#include <bdlf_overloaded.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>

using namespace BloombergLP;
using namespace bsl::string_literals;

template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <class F, class R, class... Args>
concept MapsTo = requires(F &f, Args &...a) {
  {
    bsl::invoke(static_cast<F &>(f), static_cast<Args &>(a)...)
  } -> convertible_to<R>;
};

template <typename t_A> struct List {
  // TYPES
  struct Nil {};
  struct Cons {
    t_A d_a0;
    bsl::shared_ptr<List<t_A>> d_a1;
  };
  using variant_t = bsl::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(bsl::move(_v)) {}
  explicit List(Cons _v) : d_v_(bsl::move(_v)) {}
  static bsl::shared_ptr<List<t_A>> nil() {
    return bsl::make_shared<List<t_A>>(Nil{});
  }
  static bsl::shared_ptr<List<t_A>> cons(t_A a0,
                                         const bsl::shared_ptr<List<t_A>> &a1) {
    return bsl::make_shared<List<t_A>>(Cons{bsl::move(a0), a1});
  }
  static bsl::shared_ptr<List<t_A>> cons(t_A a0,
                                         bsl::shared_ptr<List<t_A>> &&a1) {
    return bsl::make_shared<List<t_A>>(Cons{bsl::move(a0), bsl::move(a1)});
  }
  static bsl::unique_ptr<List<t_A>> nil_uptr() {
    return bsl::make_unique<List<t_A>>(Nil{});
  }
  static bsl::unique_ptr<List<t_A>>
  cons_uptr(t_A a0, const bsl::shared_ptr<List<t_A>> &a1) {
    return bsl::make_unique<List<t_A>>(Cons{bsl::move(a0), a1});
  }
  static bsl::unique_ptr<List<t_A>> cons_uptr(t_A a0,
                                              bsl::shared_ptr<List<t_A>> &&a1) {
    return bsl::make_unique<List<t_A>>(Cons{bsl::move(a0), bsl::move(a1)});
  }
  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
  template <typename T1>
  bsl::shared_ptr<List<bsl::pair<t_A, T1>>>
  combine(const bsl::shared_ptr<List<T1>> &l_) const {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> bsl::shared_ptr<List<bsl::pair<t_A, T1>>> {
              return List<bsl::pair<t_A, T1>>::nil();
            },
            [&](const typename List<t_A>::Cons _args)
                -> bsl::shared_ptr<List<bsl::pair<t_A, T1>>> {
              return bsl::visit(
                  bdlf::Overloaded{
                      [](const typename List<T1>::Nil _args0)
                          -> bsl::shared_ptr<List<bsl::pair<t_A, T1>>> {
                        return List<bsl::pair<t_A, T1>>::nil();
                      },
                      [&](const typename List<T1>::Cons _args0)
                          -> bsl::shared_ptr<List<bsl::pair<t_A, T1>>> {
                        return List<bsl::pair<t_A, T1>>::cons(
                            bsl::make_pair(_args.d_a0, _args0.d_a0),
                            _args.d_a1->template combine<T1>(_args0.d_a1));
                      }},
                  l_->v());
            }},
        this->v());
  }
  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bsl::optional<t_A> find(F0 &&f) const {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<t_A>::Nil _args) -> bsl::optional<t_A> {
              return bsl::optional<t_A>();
            },
            [&](const typename List<t_A>::Cons _args) -> bsl::optional<t_A> {
              if (f(_args.d_a0)) {
                return bsl::make_optional<t_A>(_args.d_a0);
              } else {
                return _args.d_a1->find(f);
              }
            }},
        this->v());
  }
  template <MapsTo<bool, t_A> F0>
  bsl::shared_ptr<List<t_A>> filter(F0 &&f) const {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> bsl::shared_ptr<List<t_A>> { return List<t_A>::nil(); },
            [&](const typename List<t_A>::Cons _args)
                -> bsl::shared_ptr<List<t_A>> {
              if (f(_args.d_a0)) {
                return List<t_A>::cons(_args.d_a0, _args.d_a1->filter(f));
              } else {
                return _args.d_a1->filter(f);
              }
            }},
        this->v());
  }
  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    return bsl::visit(
        bdlf::Overloaded{
            [&](const typename List<t_A>::Nil _args) -> T1 { return a0; },
            [&](const typename List<t_A>::Cons _args) -> T1 {
              return f(_args.d_a0, _args.d_a1->template fold_right<T1>(f, a0));
            }},
        this->v());
  }
  template <typename T1> bsl::shared_ptr<List<T1>> concat() const {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<bsl::shared_ptr<List<T1>>>::Nil _args)
                -> bsl::shared_ptr<List<T1>> { return List<T1>::nil(); },
            [](const typename List<bsl::shared_ptr<List<T1>>>::Cons _args)
                -> bsl::shared_ptr<List<T1>> {
              return _args.d_a0->app(_args.d_a1->template concat<T1>());
            }},
        this->v());
  }
  template <typename T1, MapsTo<T1, t_A> F0>
  bsl::shared_ptr<List<T1>> map(F0 &&f) const {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<t_A>::Nil _args)
                -> bsl::shared_ptr<List<T1>> { return List<T1>::nil(); },
            [&](const typename List<t_A>::Cons _args)
                -> bsl::shared_ptr<List<T1>> {
              return List<T1>::cons(f(_args.d_a0),
                                    _args.d_a1->template map<T1>(f));
            }},
        this->v());
  }
  __attribute__((pure)) unsigned int length() const {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<t_A>::Nil _args) -> unsigned int {
              return 0u;
            },
            [](const typename List<t_A>::Cons _args) -> unsigned int {
              return (_args.d_a1->length() + 1);
            }},
        this->v());
  }
  bsl::shared_ptr<List<t_A>> app(bsl::shared_ptr<List<t_A>> m) const {
    return bsl::visit(
        bdlf::Overloaded{[&](const typename List<t_A>::Nil _args)
                             -> bsl::shared_ptr<List<t_A>> { return m; },
                         [&](const typename List<t_A>::Cons _args)
                             -> bsl::shared_ptr<List<t_A>> {
                           return List<t_A>::cons(_args.d_a0,
                                                  _args.d_a1->app(m));
                         }},
        this->v());
  }
};
struct ListDef {
  static bsl::shared_ptr<List<unsigned int>> seq(const unsigned int start,
                                                 const unsigned int len);
};
struct ToString {
  template <typename T1, typename T2, MapsTo<bsl::string, T1> F0,
            MapsTo<bsl::string, T2> F1>
  __attribute__((pure)) static bsl::string
  pair_to_string(F0 &&p1, F1 &&p2, const bsl::pair<T1, T2> x) {
    T1 a = x.first;
    T2 b = x.second;
    return "("_s + p1(a) + ", "_s + p2(b) + ")"_s;
  }
  template <typename T1, MapsTo<bsl::string, T1> F0>
  __attribute__((pure)) static bsl::string
  intersperse(F0 &&p, const bsl::string sep,
              const bsl::shared_ptr<List<T1>> &l) {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<T1>::Nil _args) -> bsl::string {
              return "";
            },
            [&](const typename List<T1>::Cons _args) -> bsl::string {
              return bsl::visit(
                  bdlf::Overloaded{
                      [&](const typename List<T1>::Nil _args0) -> bsl::string {
                        return sep + p(_args.d_a0);
                      },
                      [&](const typename List<T1>::Cons _args0) -> bsl::string {
                        return sep + p(_args.d_a0) +
                               intersperse<T1>(p, sep, _args.d_a1);
                      }},
                  _args.d_a1->v());
            }},
        l->v());
  }
  template <typename T1, MapsTo<bsl::string, T1> F0>
  __attribute__((pure)) static bsl::string
  list_to_string(F0 &&p, const bsl::shared_ptr<List<T1>> &l) {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<T1>::Nil _args) -> bsl::string {
              return "[]";
            },
            [&](const typename List<T1>::Cons _args) -> bsl::string {
              return bsl::visit(
                  bdlf::Overloaded{
                      [&](const typename List<T1>::Nil _args0) -> bsl::string {
                        return "["_s + p(_args.d_a0) + "]"_s;
                      },
                      [&](const typename List<T1>::Cons _args0) -> bsl::string {
                        return "["_s + p(_args.d_a0) +
                               intersperse<T1>(p, "; ", _args.d_a1) + "]"_s;
                      }},
                  _args.d_a1->v());
            }},
        l->v());
  }
};
struct TopologicalSort {
  template <typename node>
  using entry = bsl::pair<node, bsl::shared_ptr<List<node>>>;
  template <typename node> using graph = bsl::shared_ptr<List<entry<node>>>;
  template <typename node>
  using order = bsl::shared_ptr<List<bsl::shared_ptr<List<node>>>>;
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<T1>>
  get_elems(F0 &&eqb_node, const bsl::shared_ptr<List<bsl::pair<T1, T1>>> &l) {
    bsl::function<bsl::shared_ptr<List<T1>>(
        bsl::shared_ptr<List<bsl::pair<T1, T1>>>, bsl::shared_ptr<List<T1>>)>
        get_elems_aux;
    get_elems_aux =
        [&](bsl::shared_ptr<List<bsl::pair<T1, T1>>> l0,
            bsl::shared_ptr<List<T1>> h) -> bsl::shared_ptr<List<T1>> {
      return bsl::visit(
          bdlf::Overloaded{
              [&](const typename List<bsl::pair<T1, T1>>::Nil _args)
                  -> bsl::shared_ptr<List<T1>> { return bsl::move(h); },
              [&](const typename List<bsl::pair<T1, T1>>::Cons _args)
                  -> bsl::shared_ptr<List<T1>> {
                T1 e1 = _args.d_a0.first;
                T1 e2 = _args.d_a0.second;
                bsl::optional<T1> f1 =
                    h->find([=](T1 x) mutable { return eqb_node(e1, x); });
                bsl::optional<T1> f2 =
                    h->find([=](T1 x) mutable { return eqb_node(e2, x); });
                if (f1.has_value()) {
                  T1 _x = *f1;
                  if (f2.has_value()) {
                    T1 _x0 = *f2;
                    return get_elems_aux(_args.d_a1, h);
                  } else {
                    return get_elems_aux(_args.d_a1, List<T1>::cons(e2, h));
                  }
                } else {
                  if (f2.has_value()) {
                    T1 _x = *f2;
                    return get_elems_aux(_args.d_a1,
                                         List<T1>::cons(bsl::move(e1), h));
                  } else {
                    if (eqb_node(e1, e2)) {
                      return get_elems_aux(bsl::move(_args.d_a1),
                                           List<T1>::cons(e1, h));
                    } else {
                      return get_elems_aux(
                          bsl::move(_args.d_a1),
                          List<T1>::cons(e1, List<T1>::cons(e2, h)));
                    }
                  }
                }
              }},
          l0->v());
    };
    return get_elems_aux(l, List<T1>::nil());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static entry<T1>
  make_entry(F0 &&eqb_node, bsl::shared_ptr<List<bsl::pair<T1, T1>>> l,
             const T1 e) {
    return bsl::make_pair(
        e, bsl::move(l)->template fold_right<bsl::shared_ptr<List<T1>>>(
               [=](bsl::pair<T1, T1> x, bsl::shared_ptr<List<T1>> ret) mutable {
                 if (eqb_node(e, x.first)) {
                   return List<T1>::cons(x.second, ret);
                 } else {
                   return ret;
                 }
               },
               List<T1>::nil()));
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static graph<T1>
  make_graph(F0 &&eqb_node, bsl::shared_ptr<List<bsl::pair<T1, T1>>> l) {
    bsl::shared_ptr<List<T1>> elems = get_elems<T1>(eqb_node, l);
    return bsl::move(elems)
        ->template fold_right<bsl::shared_ptr<List<entry<T1>>>>(
            [=](T1 e,
                bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
                    ret) mutable {
              return List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>::cons(
                  make_entry<T1>(eqb_node, l, e), ret);
            },
            List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>::nil());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<T1>> graph_lookup(
      F0 &&eqb_node, const T1 elem,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0) {
    if (graph0
            ->find(
                [=](bsl::pair<T1, bsl::shared_ptr<List<T1>>> entry0) mutable {
                  return eqb_node(elem, entry0.first);
                })
            .has_value()) {
      bsl::pair<T1, bsl::shared_ptr<List<T1>>> p = *graph0->find(
          [=](bsl::pair<T1, bsl::shared_ptr<List<T1>>> entry0) mutable {
            return eqb_node(elem, entry0.first);
          });
      T1 _x = p.first;
      bsl::shared_ptr<List<T1>> es = p.second;
      return es;
    } else {
      return List<T1>::nil();
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bool
  contains(F0 &&eqb_node, const T1 elem, const bsl::shared_ptr<List<T1>> &es) {
    if (es->find([=](T1 x) mutable { return eqb_node(elem, x); }).has_value()) {
      T1 _x = *es->find([=](T1 x) mutable { return eqb_node(elem, x); });
      return true;
    } else {
      return false;
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static T1 cycle_entry_aux(
      F0 &&eqb_node,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0,
      bsl::shared_ptr<List<T1>> seens, const T1 elem,
      const unsigned int counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        unsigned int c = counter - 1;
        bsl::shared_ptr<List<T1>> l =
            graph_lookup<T1>(eqb_node, bsl::move(elem), graph0);
        return bsl::visit(
            bdlf::Overloaded{[&](const typename List<T1>::Nil _args) -> T1 {
                               return bsl::move(elem);
                             },
                             [&](const typename List<T1>::Cons _args) -> T1 {
                               return cycle_entry_aux<T1>(
                                   eqb_node, graph0,
                                   List<T1>::cons(bsl::move(elem), seens),
                                   _args.d_a0, c);
                             }},
            bsl::move(l)->v());
      }
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::optional<T1> cycle_entry(
      F0 &&eqb_node,
      bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>> graph0) {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<
                bsl::pair<T1, bsl::shared_ptr<List<T1>>>>::Nil _args)
                -> bsl::optional<T1> { return bsl::optional<T1>(); },
            [&](const typename List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>::
                    Cons _args) -> bsl::optional<T1> {
              T1 e = _args.d_a0.first;
              bsl::shared_ptr<List<T1>> _x0 = _args.d_a0.second;
              return bsl::make_optional<T1>(cycle_entry_aux<T1>(
                  eqb_node, graph0, List<T1>::nil(), e, graph0->length()));
            }},
        graph0->v());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<T1>> cycle_extract_aux(
      F0 &&eqb_node,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0,
      const unsigned int counter, const T1 elem,
      bsl::shared_ptr<List<T1>> cycl) {
    if (counter <= 0) {
      return bsl::move(cycl);
    } else {
      unsigned int c = counter - 1;
      if (contains<T1>(eqb_node, elem, cycl)) {
        return cycl;
      } else {
        return graph_lookup<T1>(eqb_node, elem, graph0)
            ->template fold_right<bsl::shared_ptr<List<T1>>>(
                [&](T1 _x0, const bsl::shared_ptr<List<T1>> &_x1)
                    -> bsl::shared_ptr<List<T1>> {
                  return cycle_extract_aux<T1>(eqb_node, graph0, bsl::move(c),
                                               _x0, _x1);
                },
                List<T1>::cons(elem, cycl));
      }
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<T1>> cycle_extract(
      F0 &&eqb_node,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0) {
    if (cycle_entry<T1>(eqb_node, graph0).has_value()) {
      T1 elem = *cycle_entry<T1>(eqb_node, graph0);
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0->length(), elem,
                                   List<T1>::nil());
    } else {
      return List<T1>::nil();
    }
  }
  template <typename T1>
  __attribute__((pure)) static bool null(const bsl::shared_ptr<List<T1>> &xs) {
    return bsl::visit(
        bdlf::Overloaded{
            [](const typename List<T1>::Nil _args) -> bool { return true; },
            [](const typename List<T1>::Cons _args) -> bool { return false; }},
        xs->v());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static order<T1> topological_sort_aux(
      F0 &&eqb_node,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0,
      const unsigned int counter) {
    if (counter <= 0) {
      return List<bsl::shared_ptr<List<T1>>>::nil();
    } else {
      unsigned int c = counter - 1;
      if (null<entry<T1>>(graph0)) {
        return List<bsl::shared_ptr<List<T1>>>::nil();
      } else {
        bsl::shared_ptr<List<T1>> mins =
            graph0
                ->filter([](bsl::pair<T1, bsl::shared_ptr<List<T1>>> p) {
                  return null<T1>(p.second);
                })
                ->template map<T1>(
                    [](bsl::pair<T1, bsl::shared_ptr<List<T1>>> _x0) -> T1 {
                      return _x0.first;
                    });
        bsl::shared_ptr<List<T1>> mins_;
        if (null<T1>(mins)) {
          mins_ = cycle_extract<T1>(eqb_node, graph0);
        } else {
          mins_ = mins;
        }
        bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>> rest =
            graph0->filter(
                [=](bsl::pair<T1, bsl::shared_ptr<List<T1>>> entry0) mutable {
                  return !(contains<T1>(eqb_node, entry0.first, mins_));
                });
        bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>> rest_ =
            bsl::move(rest)
                ->template map<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>(
                    [=](bsl::pair<T1, bsl::shared_ptr<List<T1>>>
                            entry0) mutable {
                      return bsl::make_pair(
                          entry0.first,
                          entry0.second->filter([=](T1 e) mutable {
                            return !(contains<T1>(eqb_node, e, mins_));
                          }));
                    });
        return List<bsl::shared_ptr<List<T1>>>::cons(
            bsl::move(mins_),
            topological_sort_aux<T1>(eqb_node, bsl::move(rest_), c));
      }
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<bsl::shared_ptr<List<T1>>>>
  topological_sort(F0 &&eqb_node,
                   const bsl::shared_ptr<List<bsl::pair<T1, T1>>> &g) {
    bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>> g_ =
        make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_->length());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static order<T1> topological_sort_graph(
      F0 &&eqb_node,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0->length());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bsl::shared_ptr<List<bsl::pair<T1, unsigned int>>>
  topological_rank_list(
      F0 &&eqb_node,
      const bsl::shared_ptr<List<bsl::pair<T1, bsl::shared_ptr<List<T1>>>>>
          &graph0) {
    bsl::shared_ptr<List<bsl::shared_ptr<List<T1>>>> lorder =
        topological_sort_graph<T1>(eqb_node, graph0);
    return lorder
        ->template combine<unsigned int>(ListDef::seq(0u, lorder->length()))
        ->template map<bsl::shared_ptr<List<bsl::pair<T1, unsigned int>>>>(
            [](bsl::pair<bsl::shared_ptr<List<T1>>, unsigned int> x) {
              bsl::shared_ptr<List<T1>> fs = x.first;
              unsigned int rk = x.second;
              return fs->template map<bsl::pair<T1, unsigned int>>(
                  [=](T1 f) mutable { return bsl::make_pair(f, rk); });
            })
        ->template concat<bsl::pair<T1, unsigned int>>();
  }
};

#endif // INCLUDED_TOPOLOGICAL_SORT_BDE
