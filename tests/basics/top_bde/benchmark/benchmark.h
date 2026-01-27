#include <bdlf_overloaded.h>
#include <bsl_algorithm.h>
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_optional.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_utility.h>
#include <bsl_variant.h>

using namespace BloombergLP;

template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <class F, class R, class... Args>
concept MapsTo = requires(F& f, Args&... a) {
    {
        bsl::invoke(static_cast<F&>(f), static_cast<Args&>(a)...)
    } -> convertible_to<R>;
};

struct Unit {
    struct unit {
      public:
        struct tt {
        };
        using variant_t = bsl::variant<tt>;
      private:
        variant_t v_;
        explicit unit(tt x)
        : v_(bsl::move(x))
        {
        }
      public:
        struct ctor {
            ctor() = delete;
            static bsl::shared_ptr<Unit::unit> tt_()
            {
                return bsl::shared_ptr<Unit::unit>(new Unit::unit(tt{}));
            }
        };
        const variant_t& v() const { return v_; }
    };
};

struct List {
    template <typename A>
    struct list {
      public:
        struct nil {
        };
        struct cons {
            A                               _a0;
            bsl::shared_ptr<List::list<A> > _a1;
        };
        using variant_t = bsl::variant<nil, cons>;
      private:
        variant_t v_;
        explicit list(nil x)
        : v_(bsl::move(x))
        {
        }
        explicit list(cons x)
        : v_(bsl::move(x))
        {
        }
      public:
        struct ctor {
            ctor() = delete;
            static bsl::shared_ptr<List::list<A> > nil_()
            {
                return bsl::shared_ptr<List::list<A> >(
                                                     new List::list<A>(nil{}));
            }
            static bsl::shared_ptr<List::list<A> > cons_(
                                     A                                      a0,
                                     const bsl::shared_ptr<List::list<A> >& a1)
            {
                return bsl::shared_ptr<List::list<A> >(
                                              new List::list<A>(cons{a0, a1}));
            }
        };
        const variant_t& v() const { return v_; }
        unsigned int     length() const
        {
            return bsl::visit(
                        bdlf::Overloaded{
                            [&](const typename List::list<A>::nil _args)
                                -> unsigned int {
                                return 0;
                            },
                            [&](const typename List::list<A>::cons _args)
                                -> unsigned int {
                                bsl::shared_ptr<List::list<A> > l_ = _args._a1;
                                return (l_->length() + 1);
                            }},
                        this->v());
        }
    };
};

template <typename T1, typename T2, MapsTo<T2, T1> F0>
bsl::shared_ptr<List::list<T2> > map(F0&&                                    f,
                                     const bsl::shared_ptr<List::list<T1> >& l)
{
    return bsl::visit(
          bdlf::Overloaded{
              [&](const typename List::list<T1>::nil _args)
                  -> bsl::shared_ptr<List::list<T2> > {
                  return List::list<T2>::ctor::nil_();
              },
              [&](const typename List::list<T1>::cons _args)
                  -> bsl::shared_ptr<List::list<T2> > {
                  T1                               a  = _args._a0;
                  bsl::shared_ptr<List::list<T1> > l0 = _args._a1;
                  return List::list<T2>::ctor::cons_(f(a), map<T1, T2>(f, l0));
              }},
          l->v());
}

template <typename T1, typename T2, MapsTo<T1, T2, T1> F0>
T1 fold_right(F0&& f, const T1 a0, const bsl::shared_ptr<List::list<T2> >& l)
{
    return bsl::visit(
        bdlf::Overloaded{[&](const typename List::list<T2>::nil _args) -> T1 {
                             return a0;
                         },
                         [&](const typename List::list<T2>::cons _args) -> T1 {
                             T2                               b  = _args._a0;
                             bsl::shared_ptr<List::list<T2> > l0 = _args._a1;
                             return f(b, fold_right<T1, T2>(f, a0, l0));
                         }},
        l->v());
}

template <typename T1, MapsTo<bool, T1> F0>
bsl::shared_ptr<List::list<T1> > filter(
                                     F0&&                                    f,
                                     const bsl::shared_ptr<List::list<T1> >& l)
{
    return bsl::visit(
          bdlf::Overloaded{
              [&](const typename List::list<T1>::nil _args)
                  -> bsl::shared_ptr<List::list<T1> > {
                  return List::list<T1>::ctor::nil_();
              },
              [&](const typename List::list<T1>::cons _args)
                  -> bsl::shared_ptr<List::list<T1> > {
                  T1                               x  = _args._a0;
                  bsl::shared_ptr<List::list<T1> > l0 = _args._a1;
                  if (f(x)) {
                      return List::list<T1>::ctor::cons_(x, filter<T1>(f, l0));
                  }
                  else {
                      return filter<T1>(f, l0);
                  }
              }},
          l->v());
}

template <typename T1, MapsTo<bool, T1> F0>
bsl::optional<T1> find(F0&& f, const bsl::shared_ptr<List::list<T1> >& l)
{
    return bsl::visit(
          bdlf::Overloaded{[&](const typename List::list<T1>::nil _args)
                               -> bsl::optional<T1> {
                               return bsl::nullopt;
                           },
                           [&](const typename List::list<T1>::cons _args)
                               -> bsl::optional<T1> {
                               T1                               x  = _args._a0;
                               bsl::shared_ptr<List::list<T1> > tl = _args._a1;
                               if (f(x)) {
                                   return bsl::make_optional<T1>(x);
                               }
                               else {
                                   return find<T1>(f, tl);
                               }
                           }},
          l->v());
}

struct ToString {
    template <typename T1, MapsTo<std::string, T1> F0>
    static std::string intersperse(F0&&                                    p,
                                   const std::string                       sep,
                                   const bsl::shared_ptr<List::list<T1> >& l)
    {
        return bsl::visit(
            bdlf::Overloaded{
                [&](const typename List::list<T1>::nil _args) -> std::string {
                    return "";
                },
                [&](const typename List::list<T1>::cons _args) -> std::string {
                    T1                               z  = _args._a0;
                    bsl::shared_ptr<List::list<T1> > l_ = _args._a1;
                    return bsl::visit(
                        bdlf::Overloaded{
                            [&](const typename List::list<T1>::nil _args)
                                -> std::string {
                                return sep + p(z);
                            },
                            [&](const typename List::list<T1>::cons _args)
                                -> std::string {
                                return sep + p(z) +
                                       intersperse<T1>(p, sep, l_);
                            }},
                        l_->v());
                }},
            l->v());
    }

    template <typename T1, MapsTo<std::string, T1> F0>
    static std::string list_to_string(
                                     F0&&                                    p,
                                     const bsl::shared_ptr<List::list<T1> >& l)
    {
        return bsl::visit(
            bdlf::Overloaded{
                [&](const typename List::list<T1>::nil _args) -> std::string {
                    return "[]";
                },
                [&](const typename List::list<T1>::cons _args) -> std::string {
                    T1                               y  = _args._a0;
                    bsl::shared_ptr<List::list<T1> > l_ = _args._a1;
                    return bsl::visit(
                        bdlf::Overloaded{
                            [&](const typename List::list<T1>::nil _args)
                                -> std::string {
                                return "[" + p(y) + "]";
                            },
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
    using entry = bsl::pair<node, bsl::shared_ptr<List::list<node> > >;

    template <typename node>
    using graph = bsl::shared_ptr<List::list<entry<node> > >;

    template <typename node>
    using order =
             bsl::shared_ptr<List::list<bsl::shared_ptr<List::list<node> > > >;

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static bsl::shared_ptr<List::list<T1> > graph_lookup(
           F0&&     eqb_node,
           const T1 elem,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
               graph)
    {
        if (find<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >(
                 [&](bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > entry0) {
                     return eqb_node(elem, entry0.first);
                 },
                 graph0)
                .has_value()) {
            bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > p = *find<
                bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >(
                 [&](bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > entry0) {
                     return eqb_node(elem, entry0.first);
                 },
                 graph0);
            T1                               _x = p.first;
            bsl::shared_ptr<List::list<T1> > es = p.second;
            return es;
        }
        else {
            return List::list<T1>::ctor::nil_();
        }
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static bool contains(F0&&                                    eqb_node,
                         const T1                                elem,
                         const bsl::shared_ptr<List::list<T1> >& es)
    {
        if (find<T1>(
                [&](T1 x) {
                    return eqb_node(elem, x);
                },
                es)
                .has_value()) {
            T1 _x = *find<T1>(
                [&](T1 x) {
                    return eqb_node(elem, x);
                },
                es);
            return true;
        }
        else {
            return false;
        }
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static T1 cycle_entry_aux(
           F0&& eqb_node,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
                                                   graph,
           const bsl::shared_ptr<List::list<T1> >& seens,
           const T1                                elem,
           const unsigned int                      counter)
    {
        if (contains<T1>(eqb_node, elem, seens)) {
            return elem;
        }
        else {
            if (counter <= 0) {
                return elem;
            }
            else {
                unsigned int                     c = counter - 1;
                bsl::shared_ptr<List::list<T1> > l = graph_lookup<T1>(eqb_node,
                                                                      elem,
                                                                      graph0);
                return bsl::visit(
                     bdlf::Overloaded{
                         [&](const typename List::list<T1>::nil _args) -> T1 {
                             return elem;
                         },
                         [&](const typename List::list<T1>::cons _args) -> T1 {
                             T1 e_ = _args._a0;
                             return cycle_entry_aux<T1>(
                                 eqb_node,
                                 graph0,
                                 List::list<T1>::ctor::cons_(elem, seens),
                                 e_,
                                 c);
                         }},
                     l->v());
            }
        }
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static bsl::optional<T1> cycle_entry(
           F0&& eqb_node,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
               graph)
    {
        return bsl::visit(
               bdlf::Overloaded{
                   [&](const typename List::list<
                       bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >::nil
                           _args) -> bsl::optional<T1> {
                       return bsl::nullopt;
                   },
                   [&](const typename List::list<
                       bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >::cons
                           _args) -> bsl::optional<T1> {
                       bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > e0 =
                           _args._a0;
                       T1                               e   = e0.first;
                       bsl::shared_ptr<List::list<T1> > _x0 = e0.second;
                       return bsl::make_optional<T1>(cycle_entry_aux<T1>(
                           eqb_node,
                           graph0,
                           List::list<T1>::ctor::nil_(),
                           e,
                           graph0->length()));
                   }},
               graph0->v());
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static bsl::shared_ptr<List::list<T1> > cycle_extract_aux(
           F0&& eqb_node,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
                                                   graph,
           const unsigned int                      counter,
           const T1                                elem,
           const bsl::shared_ptr<List::list<T1> >& cycl)
    {
        if (counter <= 0) {
            return cycl;
        }
        else {
            unsigned int c = counter - 1;
            if (contains<T1>(eqb_node, elem, cycl)) {
                return cycl;
            }
            else {
                return fold_right<bsl::shared_ptr<List::list<T1> >, T1>(
                              [&](const T1                               _x0,
                                  const bsl::shared_ptr<List::list<T1> > _x1) {
                                  return cycle_extract_aux<T1>(eqb_node,
                                                               graph0,
                                                               c,
                                                               _x0,
                                                               _x1);
                              },
                              List::list<T1>::ctor::cons_(elem, cycl),
                              graph_lookup<T1>(eqb_node, elem, graph0));
            }
        }
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static bsl::shared_ptr<List::list<T1> > cycle_extract(
           F0&& eqb_node,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
               graph)
    {
        if (cycle_entry<T1>(eqb_node, graph0).has_value()) {
            T1 elem = *cycle_entry<T1>(eqb_node, graph0);
            return cycle_extract_aux<T1>(eqb_node,
                                         graph0,
                                         graph0->length(),
                                         elem,
                                         List::list<T1>::ctor::nil_());
        }
        else {
            return List::list<T1>::ctor::nil_();
        }
    }

    template <typename T1>
    static bool null(const bsl::shared_ptr<List::list<T1> >& xs)
    {
        return bsl::visit(
                   bdlf::Overloaded{
                       [&](const typename List::list<T1>::nil _args) -> bool {
                           return true;
                       },
                       [&](const typename List::list<T1>::cons _args) -> bool {
                           return false;
                       }},
                   xs->v());
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static order<T1> topological_sort_aux(
           F0&& eqb_node,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
                              graph,
           const unsigned int counter)
    {
        if (counter <= 0) {
            return List::list<bsl::shared_ptr<List::list<T1> > >::ctor::nil_();
        }
        else {
            unsigned int c = counter - 1;
            if (null<entry<T1> >(graph0)) {
                return List::list<
                    bsl::shared_ptr<List::list<T1> > >::ctor::nil_();
            }
            else {
                bsl::shared_ptr<List::list<T1> > mins = map<
                    bsl::pair<T1, bsl::shared_ptr<List::list<T1> > >,
                    T1>(
                     [&](const bsl::pair<T1, bsl::shared_ptr<List::list<T1> > >
                             _x0) {
                         return _x0.first;
                     },
                     filter<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >(
                         [&](bsl::pair<T1, bsl::shared_ptr<List::list<T1> > >
                                 p) {
                             return null<T1>(p.second);
                         },
                         graph0));
                bsl::shared_ptr<List::list<T1> > mins_;
                if (null<T1>(mins)) {
                    mins_ = cycle_extract<T1>(eqb_node, graph0);
                }
                else {
                    mins_ = mins;
                }
                bsl::shared_ptr<List::list<
                    bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >
                    rest = filter<
                        bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >(
                           [&](bsl::pair<T1, bsl::shared_ptr<List::list<T1> > >
                                   entry0) {
                               return !(contains<T1>(eqb_node,
                                                     entry0.first,
                                                     mins_));
                           },
                           graph0);
                bsl::shared_ptr<List::list<
                    bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >
                    rest_ = map<
                        bsl::pair<T1, bsl::shared_ptr<List::list<T1> > >,
                        bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > >(
                           [&](bsl::pair<T1, bsl::shared_ptr<List::list<T1> > >
                                   entry0) {
                               return bsl::make_pair(
                                   entry0.first,
                                   filter<T1>(
                                       [&](T1 e) {
                                           return !(contains<T1>(eqb_node,
                                                                 e,
                                                                 mins_));
                                       },
                                       entry0.second));
                           },
                           rest);
                return List::list<bsl::shared_ptr<List::list<T1> > >::ctor::
                    cons_(mins_, topological_sort_aux<T1>(eqb_node, rest_, c));
            }
        }
    }

    template <typename T1, MapsTo<bool, T1, T1> F0>
    static order<T1> topological_sort_graph(
           F0&& eqb_node,
           const bsl::shared_ptr<
               List::list<bsl::pair<T1, bsl::shared_ptr<List::list<T1> > > > >&
               graph)
    {
        return topological_sort_aux<T1>(eqb_node, graph0, graph0->length());
    }
};

const bsl::shared_ptr<List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>> bigDAG = List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(1u, List::list<unsigned int>::ctor::cons_(2u, List::list<unsigned int>::ctor::cons_(3u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(2u, List::list<unsigned int>::ctor::cons_(3u, List::list<unsigned int>::ctor::cons_(4u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(3u, List::list<unsigned int>::ctor::cons_(4u, List::list<unsigned int>::ctor::cons_(5u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(4u, List::list<unsigned int>::ctor::cons_(5u, List::list<unsigned int>::ctor::cons_(6u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(5u, List::list<unsigned int>::ctor::cons_(6u, List::list<unsigned int>::ctor::cons_(7u, List::list<unsigned int>::ctor::cons_(10u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(6u, List::list<unsigned int>::ctor::cons_(7u, List::list<unsigned int>::ctor::cons_(8u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(7u, List::list<unsigned int>::ctor::cons_(8u, List::list<unsigned int>::ctor::cons_(9u, List::list<unsigned int>::ctor::cons_(14u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(8u, List::list<unsigned int>::ctor::cons_(9u, List::list<unsigned int>::ctor::cons_(10u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(9u, List::list<unsigned int>::ctor::cons_(10u, List::list<unsigned int>::ctor::cons_(11u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(10u, List::list<unsigned int>::ctor::cons_(11u, List::list<unsigned int>::ctor::cons_(12u, List::list<unsigned int>::ctor::cons_(15u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(11u, List::list<unsigned int>::ctor::cons_(12u, List::list<unsigned int>::ctor::cons_(13u, List::list<unsigned int>::ctor::cons_(22u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(12u, List::list<unsigned int>::ctor::cons_(13u, List::list<unsigned int>::ctor::cons_(14u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(13u, List::list<unsigned int>::ctor::cons_(14u, List::list<unsigned int>::ctor::cons_(15u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(14u, List::list<unsigned int>::ctor::cons_(15u, List::list<unsigned int>::ctor::cons_(16u, List::list<unsigned int>::ctor::cons_(21u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(15u, List::list<unsigned int>::ctor::cons_(16u, List::list<unsigned int>::ctor::cons_(17u, List::list<unsigned int>::ctor::cons_(20u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(16u, List::list<unsigned int>::ctor::cons_(17u, List::list<unsigned int>::ctor::cons_(18u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(17u, List::list<unsigned int>::ctor::cons_(18u, List::list<unsigned int>::ctor::cons_(19u, List::list<unsigned int>::ctor::cons_(24u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(18u, List::list<unsigned int>::ctor::cons_(19u, List::list<unsigned int>::ctor::cons_(20u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(19u, List::list<unsigned int>::ctor::cons_(20u, List::list<unsigned int>::ctor::cons_(21u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(20u, List::list<unsigned int>::ctor::cons_(21u, List::list<unsigned int>::ctor::cons_(22u, List::list<unsigned int>::ctor::cons_(25u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(21u, List::list<unsigned int>::ctor::cons_(22u, List::list<unsigned int>::ctor::cons_(23u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(22u, List::list<unsigned int>::ctor::cons_(23u, List::list<unsigned int>::ctor::cons_(24u, List::list<unsigned int>::ctor::cons_(33u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(23u, List::list<unsigned int>::ctor::cons_(24u, List::list<unsigned int>::ctor::cons_(25u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(24u, List::list<unsigned int>::ctor::cons_(25u, List::list<unsigned int>::ctor::cons_(26u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(25u, List::list<unsigned int>::ctor::cons_(26u, List::list<unsigned int>::ctor::cons_(27u, List::list<unsigned int>::ctor::cons_(30u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(26u, List::list<unsigned int>::ctor::cons_(27u, List::list<unsigned int>::ctor::cons_(28u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(27u, List::list<unsigned int>::ctor::cons_(28u, List::list<unsigned int>::ctor::cons_(29u, List::list<unsigned int>::ctor::cons_(34u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(28u, List::list<unsigned int>::ctor::cons_(29u, List::list<unsigned int>::ctor::cons_(30u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(29u, List::list<unsigned int>::ctor::cons_(30u, List::list<unsigned int>::ctor::cons_(31u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(30u, List::list<unsigned int>::ctor::cons_(31u, List::list<unsigned int>::ctor::cons_(32u, List::list<unsigned int>::ctor::cons_(35u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(31u, List::list<unsigned int>::ctor::cons_(32u, List::list<unsigned int>::ctor::cons_(33u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(32u, List::list<unsigned int>::ctor::cons_(33u, List::list<unsigned int>::ctor::cons_(34u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(33u, List::list<unsigned int>::ctor::cons_(34u, List::list<unsigned int>::ctor::cons_(35u, List::list<unsigned int>::ctor::cons_(44u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(34u, List::list<unsigned int>::ctor::cons_(35u, List::list<unsigned int>::ctor::cons_(36u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(35u, List::list<unsigned int>::ctor::cons_(36u, List::list<unsigned int>::ctor::cons_(37u, List::list<unsigned int>::ctor::cons_(40u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(36u, List::list<unsigned int>::ctor::cons_(37u, List::list<unsigned int>::ctor::cons_(38u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(37u, List::list<unsigned int>::ctor::cons_(38u, List::list<unsigned int>::ctor::cons_(39u, List::list<unsigned int>::ctor::cons_(46u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(38u, List::list<unsigned int>::ctor::cons_(39u, List::list<unsigned int>::ctor::cons_(40u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(39u, List::list<unsigned int>::ctor::cons_(40u, List::list<unsigned int>::ctor::cons_(41u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(40u, List::list<unsigned int>::ctor::cons_(41u, List::list<unsigned int>::ctor::cons_(42u, List::list<unsigned int>::ctor::cons_(45u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(41u, List::list<unsigned int>::ctor::cons_(42u, List::list<unsigned int>::ctor::cons_(43u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(42u, List::list<unsigned int>::ctor::cons_(43u, List::list<unsigned int>::ctor::cons_(44u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(43u, List::list<unsigned int>::ctor::cons_(44u, List::list<unsigned int>::ctor::cons_(45u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(44u, List::list<unsigned int>::ctor::cons_(45u, List::list<unsigned int>::ctor::cons_(46u, List::list<unsigned int>::ctor::cons_(55u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(45u, List::list<unsigned int>::ctor::cons_(46u, List::list<unsigned int>::ctor::cons_(47u, List::list<unsigned int>::ctor::cons_(50u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(46u, List::list<unsigned int>::ctor::cons_(47u, List::list<unsigned int>::ctor::cons_(48u, List::list<unsigned int>::ctor::cons_(53u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(47u, List::list<unsigned int>::ctor::cons_(48u, List::list<unsigned int>::ctor::cons_(49u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(48u, List::list<unsigned int>::ctor::cons_(49u, List::list<unsigned int>::ctor::cons_(50u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(49u, List::list<unsigned int>::ctor::cons_(50u, List::list<unsigned int>::ctor::cons_(51u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(50u, List::list<unsigned int>::ctor::cons_(51u, List::list<unsigned int>::ctor::cons_(52u, List::list<unsigned int>::ctor::cons_(55u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(51u, List::list<unsigned int>::ctor::cons_(52u, List::list<unsigned int>::ctor::cons_(53u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(52u, List::list<unsigned int>::ctor::cons_(53u, List::list<unsigned int>::ctor::cons_(54u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(53u, List::list<unsigned int>::ctor::cons_(54u, List::list<unsigned int>::ctor::cons_(55u, List::list<unsigned int>::ctor::cons_(64u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(54u, List::list<unsigned int>::ctor::cons_(55u, List::list<unsigned int>::ctor::cons_(56u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(55u, List::list<unsigned int>::ctor::cons_(56u, List::list<unsigned int>::ctor::cons_(57u, List::list<unsigned int>::ctor::cons_(60u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(56u, List::list<unsigned int>::ctor::cons_(57u, List::list<unsigned int>::ctor::cons_(58u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(57u, List::list<unsigned int>::ctor::cons_(58u, List::list<unsigned int>::ctor::cons_(59u, List::list<unsigned int>::ctor::cons_(66u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(58u, List::list<unsigned int>::ctor::cons_(59u, List::list<unsigned int>::ctor::cons_(60u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(59u, List::list<unsigned int>::ctor::cons_(60u, List::list<unsigned int>::ctor::cons_(61u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(60u, List::list<unsigned int>::ctor::cons_(61u, List::list<unsigned int>::ctor::cons_(62u, List::list<unsigned int>::ctor::cons_(65u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(61u, List::list<unsigned int>::ctor::cons_(62u, List::list<unsigned int>::ctor::cons_(63u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(62u, List::list<unsigned int>::ctor::cons_(63u, List::list<unsigned int>::ctor::cons_(64u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(63u, List::list<unsigned int>::ctor::cons_(64u, List::list<unsigned int>::ctor::cons_(65u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(64u, List::list<unsigned int>::ctor::cons_(65u, List::list<unsigned int>::ctor::cons_(66u, List::list<unsigned int>::ctor::cons_(75u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(65u, List::list<unsigned int>::ctor::cons_(66u, List::list<unsigned int>::ctor::cons_(67u, List::list<unsigned int>::ctor::cons_(70u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(66u, List::list<unsigned int>::ctor::cons_(67u, List::list<unsigned int>::ctor::cons_(68u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(67u, List::list<unsigned int>::ctor::cons_(68u, List::list<unsigned int>::ctor::cons_(69u, List::list<unsigned int>::ctor::cons_(74u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(68u, List::list<unsigned int>::ctor::cons_(69u, List::list<unsigned int>::ctor::cons_(70u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(69u, List::list<unsigned int>::ctor::cons_(70u, List::list<unsigned int>::ctor::cons_(71u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(70u, List::list<unsigned int>::ctor::cons_(71u, List::list<unsigned int>::ctor::cons_(72u, List::list<unsigned int>::ctor::cons_(75u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(71u, List::list<unsigned int>::ctor::cons_(72u, List::list<unsigned int>::ctor::cons_(73u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(72u, List::list<unsigned int>::ctor::cons_(73u, List::list<unsigned int>::ctor::cons_(74u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(73u, List::list<unsigned int>::ctor::cons_(74u, List::list<unsigned int>::ctor::cons_(75u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(74u, List::list<unsigned int>::ctor::cons_(75u, List::list<unsigned int>::ctor::cons_(76u, List::list<unsigned int>::ctor::cons_(85u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(75u, List::list<unsigned int>::ctor::cons_(76u, List::list<unsigned int>::ctor::cons_(77u, List::list<unsigned int>::ctor::cons_(80u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(76u, List::list<unsigned int>::ctor::cons_(77u, List::list<unsigned int>::ctor::cons_(78u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(77u, List::list<unsigned int>::ctor::cons_(78u, List::list<unsigned int>::ctor::cons_(79u, List::list<unsigned int>::ctor::cons_(84u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(78u, List::list<unsigned int>::ctor::cons_(79u, List::list<unsigned int>::ctor::cons_(80u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(79u, List::list<unsigned int>::ctor::cons_(80u, List::list<unsigned int>::ctor::cons_(81u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(80u, List::list<unsigned int>::ctor::cons_(81u, List::list<unsigned int>::ctor::cons_(82u, List::list<unsigned int>::ctor::cons_(85u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(81u, List::list<unsigned int>::ctor::cons_(82u, List::list<unsigned int>::ctor::cons_(83u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(82u, List::list<unsigned int>::ctor::cons_(83u, List::list<unsigned int>::ctor::cons_(84u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(83u, List::list<unsigned int>::ctor::cons_(84u, List::list<unsigned int>::ctor::cons_(85u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(84u, List::list<unsigned int>::ctor::cons_(85u, List::list<unsigned int>::ctor::cons_(86u, List::list<unsigned int>::ctor::cons_(95u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(85u, List::list<unsigned int>::ctor::cons_(86u, List::list<unsigned int>::ctor::cons_(87u, List::list<unsigned int>::ctor::cons_(90u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(86u, List::list<unsigned int>::ctor::cons_(87u, List::list<unsigned int>::ctor::cons_(88u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(87u, List::list<unsigned int>::ctor::cons_(88u, List::list<unsigned int>::ctor::cons_(89u, List::list<unsigned int>::ctor::cons_(94u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(88u, List::list<unsigned int>::ctor::cons_(89u, List::list<unsigned int>::ctor::cons_(90u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(89u, List::list<unsigned int>::ctor::cons_(90u, List::list<unsigned int>::ctor::cons_(91u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(90u, List::list<unsigned int>::ctor::cons_(91u, List::list<unsigned int>::ctor::cons_(92u, List::list<unsigned int>::ctor::cons_(95u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(91u, List::list<unsigned int>::ctor::cons_(92u, List::list<unsigned int>::ctor::cons_(93u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(92u, List::list<unsigned int>::ctor::cons_(93u, List::list<unsigned int>::ctor::cons_(94u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(93u, List::list<unsigned int>::ctor::cons_(94u, List::list<unsigned int>::ctor::cons_(95u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(94u, List::list<unsigned int>::ctor::cons_(95u, List::list<unsigned int>::ctor::cons_(96u, List::list<unsigned int>::ctor::cons_(105u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(95u, List::list<unsigned int>::ctor::cons_(96u, List::list<unsigned int>::ctor::cons_(97u, List::list<unsigned int>::ctor::cons_(100u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(96u, List::list<unsigned int>::ctor::cons_(97u, List::list<unsigned int>::ctor::cons_(98u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(97u, List::list<unsigned int>::ctor::cons_(98u, List::list<unsigned int>::ctor::cons_(99u, List::list<unsigned int>::ctor::cons_(104u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(98u, List::list<unsigned int>::ctor::cons_(99u, List::list<unsigned int>::ctor::cons_(100u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(99u, List::list<unsigned int>::ctor::cons_(100u, List::list<unsigned int>::ctor::cons_(101u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(100u, List::list<unsigned int>::ctor::cons_(101u, List::list<unsigned int>::ctor::cons_(102u, List::list<unsigned int>::ctor::cons_(105u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(101u, List::list<unsigned int>::ctor::cons_(102u, List::list<unsigned int>::ctor::cons_(103u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(102u, List::list<unsigned int>::ctor::cons_(103u, List::list<unsigned int>::ctor::cons_(104u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(103u, List::list<unsigned int>::ctor::cons_(104u, List::list<unsigned int>::ctor::cons_(105u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(104u, List::list<unsigned int>::ctor::cons_(105u, List::list<unsigned int>::ctor::cons_(106u, List::list<unsigned int>::ctor::cons_(115u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(105u, List::list<unsigned int>::ctor::cons_(106u, List::list<unsigned int>::ctor::cons_(107u, List::list<unsigned int>::ctor::cons_(110u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(106u, List::list<unsigned int>::ctor::cons_(107u, List::list<unsigned int>::ctor::cons_(108u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(107u, List::list<unsigned int>::ctor::cons_(108u, List::list<unsigned int>::ctor::cons_(109u, List::list<unsigned int>::ctor::cons_(114u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(108u, List::list<unsigned int>::ctor::cons_(109u, List::list<unsigned int>::ctor::cons_(110u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(109u, List::list<unsigned int>::ctor::cons_(110u, List::list<unsigned int>::ctor::cons_(111u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(110u, List::list<unsigned int>::ctor::cons_(111u, List::list<unsigned int>::ctor::cons_(112u, List::list<unsigned int>::ctor::cons_(115u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(111u, List::list<unsigned int>::ctor::cons_(112u, List::list<unsigned int>::ctor::cons_(113u, List::list<unsigned int>::ctor::cons_(122u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(112u, List::list<unsigned int>::ctor::cons_(113u, List::list<unsigned int>::ctor::cons_(114u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(113u, List::list<unsigned int>::ctor::cons_(114u, List::list<unsigned int>::ctor::cons_(115u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(114u, List::list<unsigned int>::ctor::cons_(115u, List::list<unsigned int>::ctor::cons_(116u, List::list<unsigned int>::ctor::cons_(121u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(115u, List::list<unsigned int>::ctor::cons_(116u, List::list<unsigned int>::ctor::cons_(117u, List::list<unsigned int>::ctor::cons_(120u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(116u, List::list<unsigned int>::ctor::cons_(117u, List::list<unsigned int>::ctor::cons_(118u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(117u, List::list<unsigned int>::ctor::cons_(118u, List::list<unsigned int>::ctor::cons_(119u, List::list<unsigned int>::ctor::cons_(124u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(118u, List::list<unsigned int>::ctor::cons_(119u, List::list<unsigned int>::ctor::cons_(120u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(119u, List::list<unsigned int>::ctor::cons_(120u, List::list<unsigned int>::ctor::cons_(121u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(120u, List::list<unsigned int>::ctor::cons_(121u, List::list<unsigned int>::ctor::cons_(122u, List::list<unsigned int>::ctor::cons_(125u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(121u, List::list<unsigned int>::ctor::cons_(122u, List::list<unsigned int>::ctor::cons_(123u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(122u, List::list<unsigned int>::ctor::cons_(123u, List::list<unsigned int>::ctor::cons_(124u, List::list<unsigned int>::ctor::cons_(133u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(123u, List::list<unsigned int>::ctor::cons_(124u, List::list<unsigned int>::ctor::cons_(125u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(124u, List::list<unsigned int>::ctor::cons_(125u, List::list<unsigned int>::ctor::cons_(126u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(125u, List::list<unsigned int>::ctor::cons_(126u, List::list<unsigned int>::ctor::cons_(127u, List::list<unsigned int>::ctor::cons_(130u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(126u, List::list<unsigned int>::ctor::cons_(127u, List::list<unsigned int>::ctor::cons_(128u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(127u, List::list<unsigned int>::ctor::cons_(128u, List::list<unsigned int>::ctor::cons_(129u, List::list<unsigned int>::ctor::cons_(134u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(128u, List::list<unsigned int>::ctor::cons_(129u, List::list<unsigned int>::ctor::cons_(130u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(129u, List::list<unsigned int>::ctor::cons_(130u, List::list<unsigned int>::ctor::cons_(131u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(130u, List::list<unsigned int>::ctor::cons_(131u, List::list<unsigned int>::ctor::cons_(132u, List::list<unsigned int>::ctor::cons_(135u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(131u, List::list<unsigned int>::ctor::cons_(132u, List::list<unsigned int>::ctor::cons_(133u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(132u, List::list<unsigned int>::ctor::cons_(133u, List::list<unsigned int>::ctor::cons_(134u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(133u, List::list<unsigned int>::ctor::cons_(134u, List::list<unsigned int>::ctor::cons_(135u, List::list<unsigned int>::ctor::cons_(144u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(134u, List::list<unsigned int>::ctor::cons_(135u, List::list<unsigned int>::ctor::cons_(136u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(135u, List::list<unsigned int>::ctor::cons_(136u, List::list<unsigned int>::ctor::cons_(137u, List::list<unsigned int>::ctor::cons_(140u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(136u, List::list<unsigned int>::ctor::cons_(137u, List::list<unsigned int>::ctor::cons_(138u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(137u, List::list<unsigned int>::ctor::cons_(138u, List::list<unsigned int>::ctor::cons_(139u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(138u, List::list<unsigned int>::ctor::cons_(139u, List::list<unsigned int>::ctor::cons_(140u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(139u, List::list<unsigned int>::ctor::cons_(140u, List::list<unsigned int>::ctor::cons_(141u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(140u, List::list<unsigned int>::ctor::cons_(141u, List::list<unsigned int>::ctor::cons_(142u, List::list<unsigned int>::ctor::cons_(145u, List::list<unsigned int>::ctor::cons_(147u, List::list<unsigned int>::ctor::nil_()))))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(141u, List::list<unsigned int>::ctor::cons_(142u, List::list<unsigned int>::ctor::cons_(143u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(142u, List::list<unsigned int>::ctor::cons_(143u, List::list<unsigned int>::ctor::cons_(144u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(143u, List::list<unsigned int>::ctor::cons_(144u, List::list<unsigned int>::ctor::cons_(145u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(144u, List::list<unsigned int>::ctor::cons_(145u, List::list<unsigned int>::ctor::cons_(146u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(145u, List::list<unsigned int>::ctor::cons_(146u, List::list<unsigned int>::ctor::cons_(147u, List::list<unsigned int>::ctor::cons_(150u, List::list<unsigned int>::ctor::nil_())))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(146u, List::list<unsigned int>::ctor::cons_(147u, List::list<unsigned int>::ctor::cons_(148u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(147u, List::list<unsigned int>::ctor::cons_(148u, List::list<unsigned int>::ctor::cons_(149u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(148u, List::list<unsigned int>::ctor::cons_(149u, List::list<unsigned int>::ctor::cons_(150u, List::list<unsigned int>::ctor::nil_()))), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(149u, List::list<unsigned int>::ctor::cons_(150u, List::list<unsigned int>::ctor::nil_())), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::cons_(bsl::make_pair(150u, List::list<unsigned int>::ctor::nil_()), List::list<bsl::pair<unsigned int, bsl::shared_ptr<List::list<unsigned int>>>>::ctor::nil_()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));

std::string benchmark(const bsl::shared_ptr<Unit::unit>& _x);
