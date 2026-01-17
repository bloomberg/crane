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

template <class F, class R, class... Args>
concept MapsTo = requires(F& f, Args&... a) {
    {
        bsl::invoke(static_cast<F&>(f), static_cast<Args&>(a)...)
    } -> convertible_to<R>;
};

namespace unit {
struct tt;
using unit = bsl::variant<tt>;
struct tt {
    static bsl::shared_ptr<unit> make();
};
};

namespace list {
template <typename A>
struct nil;
template <typename A>
struct cons;
template <typename A>
using list = bsl::variant<nil<A>, cons<A> >;
template <typename A>
struct nil {
    static bsl::shared_ptr<list<A> > make()
    {
        return bsl::make_shared<list<A> >(nil<A>{});
    }
};
template <typename A>
struct cons {
    A                         _a0;
    bsl::shared_ptr<list<A> > _a1;
    static bsl::shared_ptr<list<A> > make(A _a0, bsl::shared_ptr<list<A> > _a1)
    {
        return bsl::make_shared<list<A> >(cons<A>{_a0, _a1});
    }
};
};

template <typename T1>
unsigned int length(const bsl::shared_ptr<list::list<T1> > l)
{
    return bsl::visit(
          bdlf::Overloaded{[&](const list::nil<T1> _args) -> unsigned int {
                               return 0;
                           },
                           [&](const list::cons<T1> _args) -> unsigned int {
                               bsl::shared_ptr<list::list<T1> > l_ = _args._a1;
                               return (length<T1>(l_) + 1);
                           }},
          *l);
}

template <typename T1, typename T2, MapsTo<T2, T1> F0>
bsl::shared_ptr<list::list<T2> > map(F0&&                                   f,
                                     const bsl::shared_ptr<list::list<T1> > l)
{
    return bsl::visit(
          bdlf::Overloaded{[&](const list::nil<T1> _args)
                               -> bsl::shared_ptr<list::list<T2> > {
                               return list::nil<T2>::make();
                           },
                           [&](const list::cons<T1> _args)
                               -> bsl::shared_ptr<list::list<T2> > {
                               T1                               a  = _args._a0;
                               bsl::shared_ptr<list::list<T1> > l0 = _args._a1;
                               return list::cons<T2>::make(f(a),
                                                           map<T1, T2>(f, l0));
                           }},
          *l);
}

template <typename T1, typename T2, MapsTo<T1, T2, T1> F0>
T1 fold_right(F0&& f, const T1 a0, const bsl::shared_ptr<list::list<T2> > l)
{
    return bsl::visit(
          bdlf::Overloaded{[&](const list::nil<T2> _args) -> T1 {
                               return a0;
                           },
                           [&](const list::cons<T2> _args) -> T1 {
                               T2                               b  = _args._a0;
                               bsl::shared_ptr<list::list<T2> > l0 = _args._a1;
                               return f(b, fold_right<T1, T2>(f, a0, l0));
                           }},
          *l);
}

template <typename T1, MapsTo<bool, T1> F0>
bsl::shared_ptr<list::list<T1> > filter(
                                      F0&&                                   f,
                                      const bsl::shared_ptr<list::list<T1> > l)
{
    return bsl::visit(
                 bdlf::Overloaded{
                     [&](const list::nil<T1> _args)
                         -> bsl::shared_ptr<list::list<T1> > {
                         return list::nil<T1>::make();
                     },
                     [&](const list::cons<T1> _args)
                         -> bsl::shared_ptr<list::list<T1> > {
                         T1                               x  = _args._a0;
                         bsl::shared_ptr<list::list<T1> > l0 = _args._a1;
                         if (f(x)) {
                             return list::cons<T1>::make(x, filter<T1>(f, l0));
                         }
                         else {
                             return filter<T1>(f, l0);
                         }
                     }},
                 *l);
}

template <typename T1, MapsTo<bool, T1> F0>
bsl::optional<T1> find(F0&& f, const bsl::shared_ptr<list::list<T1> > l)
{
    return bsl::visit(
        bdlf::Overloaded{[&](const list::nil<T1> _args) -> bsl::optional<T1> {
                             return bsl::nullopt;
                         },
                         [&](const list::cons<T1> _args) -> bsl::optional<T1> {
                             T1                               x  = _args._a0;
                             bsl::shared_ptr<list::list<T1> > tl = _args._a1;
                             if (f(x)) {
                                 return bsl::make_optional<T1>(x);
                             }
                             else {
                                 return find<T1>(f, tl);
                             }
                         }},
        *l);
}

namespace ToString {
template <typename T1, MapsTo<std::string, T1> F0>
std::string intersperse(F0&&                                   p,
                        const std::string                      sep,
                        const bsl::shared_ptr<list::list<T1> > l)
{
    return bsl::visit(
           bdlf::Overloaded{
               [&](const list::nil<T1> _args) -> std::string {
                   return "";
               },
               [&](const list::cons<T1> _args) -> std::string {
                   T1                               z  = _args._a0;
                   bsl::shared_ptr<list::list<T1> > l_ = _args._a1;
                   return bsl::visit(
                       bdlf::Overloaded{
                           [&](const list::nil<T1> _args) -> std::string {
                               return sep + p(z);
                           },
                           [&](const list::cons<T1> _args) -> std::string {
                               return sep + p(z) + intersperse<T1>(p, sep, l_);
                           }},
                       *l_);
               }},
           *l);
}

template <typename T1, MapsTo<std::string, T1> F0>
std::string list_to_string(F0&& p, const bsl::shared_ptr<list::list<T1> > l)
{
    return bsl::visit(
         bdlf::Overloaded{
             [&](const list::nil<T1> _args) -> std::string {
                 return "[]";
             },
             [&](const list::cons<T1> _args) -> std::string {
                 T1                               y  = _args._a0;
                 bsl::shared_ptr<list::list<T1> > l_ = _args._a1;
                 return bsl::visit(
                     bdlf::Overloaded{
                         [&](const list::nil<T1> _args) -> std::string {
                             return "[" + p(y) + "]";
                         },
                         [&](const list::cons<T1> _args) -> std::string {
                             return "[" + p(y) + intersperse<T1>(p, "; ", l_) +
                                    "]";
                         }},
                     *l_);
             }},
         *l);
}

};

namespace TopSort {
template <typename node>
using entry = bsl::pair<node, bsl::shared_ptr<list::list<node> > >;

template <typename node>
using graph = bsl::shared_ptr<list::list<entry<node> > >;

template <typename node>
using order =
             bsl::shared_ptr<list::list<bsl::shared_ptr<list::list<node> > > >;

template <typename T1, MapsTo<bool, T1, T1> F0>
bsl::shared_ptr<list::list<T1> > graph_lookup(
    F0&&     eqb_node,
    const T1 elem,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0)
{
    if (find<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > >(
                 [&](bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > entry0) {
                     return eqb_node(elem, entry0.first);
                 },
                 graph0)
            .has_value()) {
        bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > p =
             *find<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > >(
                 [&](bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > entry0) {
                     return eqb_node(elem, entry0.first);
                },
                graph0);
        T1                               _x = p.first;
        bsl::shared_ptr<list::list<T1> > es = p.second;
        return es;
    }
    else {
        return list::nil<T1>::make();
    }
}

template <typename T1, MapsTo<bool, T1, T1> F0>
bool contains(F0&&                                   eqb_node,
              const T1                               elem,
              const bsl::shared_ptr<list::list<T1> > es)
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
T1 cycle_entry_aux(
    F0&& eqb_node,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0,
    const bsl::shared_ptr<list::list<T1> >                              seens,
    const T1                                                            elem,
    const unsigned int counter)
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
            bsl::shared_ptr<list::list<T1> > l = graph_lookup<T1>(eqb_node,
                                                                  elem,
                                                                  graph0);
            return bsl::visit(
                    bdlf::Overloaded{[&](const list::nil<T1> _args) -> T1 {
                                         return elem;
                                     },
                                     [&](const list::cons<T1> _args) -> T1 {
                                         T1 e_ = _args._a0;
                                         return cycle_entry_aux<T1>(
                                             eqb_node,
                                             graph0,
                                             list::cons<T1>::make(elem, seens),
                                             e_,
                                             c);
                                     }},
                    *l);
        }
    }
}

template <typename T1, MapsTo<bool, T1, T1> F0>
bsl::optional<T1> cycle_entry(
    F0&& eqb_node,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0)
{
    return bsl::visit(
              bdlf::Overloaded{
                  [&](const list::nil<
                      bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > _args)
                      -> bsl::optional<T1> {
                      return bsl::nullopt;
                  },
                  [&](const list::cons<
                      bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > _args)
                      -> bsl::optional<T1> {
                      bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > e0 =
                          _args._a0;
                      T1                               e   = e0.first;
                      bsl::shared_ptr<list::list<T1> > _x0 = e0.second;
                      return bsl::make_optional<T1>(cycle_entry_aux<T1>(
                          eqb_node,
                          graph0,
                          list::nil<T1>::make(),
                          e,
                          length<entry<T1> >(graph0)));
                  }},
              *graph0);
}

template <typename T1, MapsTo<bool, T1, T1> F0>
bsl::shared_ptr<list::list<T1> > cycle_extract_aux(
    F0&& eqb_node,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0,
    const unsigned int                     counter,
    const T1                               elem,
    const bsl::shared_ptr<list::list<T1> > cycl)
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
            return fold_right<bsl::shared_ptr<list::list<T1> >, T1>(
                [&](const T1 _x0, const bsl::shared_ptr<list::list<T1> > _x1) {
                    return cycle_extract_aux<T1>(eqb_node,
                                                 graph0,
                                                 c,
                                                 _x0,
                                                 _x1);
                },
                list::cons<T1>::make(elem, cycl),
                graph_lookup<T1>(eqb_node, elem, graph0));
        }
    }
}

template <typename T1, MapsTo<bool, T1, T1> F0>
bsl::shared_ptr<list::list<T1> > cycle_extract(
    F0&& eqb_node,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0)
{
    if (cycle_entry<T1>(eqb_node, graph0).has_value()) {
        T1 elem = *cycle_entry<T1>(eqb_node, graph0);
        return cycle_extract_aux<T1>(eqb_node,
                                     graph0,
                                     length<entry<T1> >(graph0),
                                     elem,
                                     list::nil<T1>::make());
    }
    else {
        return list::nil<T1>::make();
    }
}

template <typename T1>
bool null(const bsl::shared_ptr<list::list<T1> > xs)
{
    return bsl::visit(
                     bdlf::Overloaded{[&](const list::nil<T1> _args) -> bool {
                                          return true;
                                      },
                                      [&](const list::cons<T1> _args) -> bool {
                                          return false;
                                      }},
                     *xs);
}

template <typename T1, MapsTo<bool, T1, T1> F0>
order<T1> topological_sort_aux(
    F0&& eqb_node,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0,
    const unsigned int counter)
{
    if (counter <= 0) {
        return list::nil<bsl::shared_ptr<list::list<T1> > >::make();
    }
    else {
        unsigned int c = counter - 1;
        if (null<entry<T1> >(graph0)) {
            return list::nil<bsl::shared_ptr<list::list<T1> > >::make();
        }
        else {
            bsl::shared_ptr<list::list<T1> > mins =
                 map<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > >, T1>(
                     [&](const bsl::pair<T1, bsl::shared_ptr<list::list<T1> > >
                             _x0) {
                         return _x0.first;
                    },
                    filter<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > >(
                           [&](bsl::pair<T1, bsl::shared_ptr<list::list<T1> > >
                                   p) {
                               return null<T1>(p.second);
                           },
                           graph0));
            bsl::shared_ptr<list::list<T1> > mins_;
            if (null<T1>(mins)) {
                mins_ = cycle_extract<T1>(eqb_node, graph0);
            }
            else {
                mins_ = mins;
            }
            bsl::shared_ptr<
                list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > >
                rest =
                     filter<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > >(
                         [&](bsl::pair<T1, bsl::shared_ptr<list::list<T1> > >
                                 entry0) {
                             return !contains<T1>(eqb_node,
                                                  entry0.first,
                                                  mins_);
                        },
                        graph0);
            bsl::shared_ptr<
                list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > >
                rest_ = map<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > >,
                            bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > >(
                      [&](bsl::pair<T1, bsl::shared_ptr<list::list<T1> > >
                              entry0) {
                          return bsl::make_pair(
                              entry0.first,
                              filter<T1>(
                                  [&](T1 e) {
                                      return !contains<T1>(eqb_node, e, mins_);
                                  },
                                  entry0.second));
                      },
                      rest);
            return list::cons<bsl::shared_ptr<list::list<T1> > >::make(
                                 mins_,
                                 topological_sort_aux<T1>(eqb_node, rest_, c));
        }
    }
}

template <typename T1, MapsTo<bool, T1, T1> F0>
order<T1> topological_sort_graph(
    F0&& eqb_node,
    const bsl::shared_ptr<
        list::list<bsl::pair<T1, bsl::shared_ptr<list::list<T1> > > > > graph0)
{
    return topological_sort_aux<T1>(eqb_node,
                                    graph0,
                                    length<entry<T1> >(graph0));
}

};

const bsl::shared_ptr<list::list<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>> bigDAG = list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(1u, list::cons<unsigned int>::make(2u, list::cons<unsigned int>::make(3u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(2u, list::cons<unsigned int>::make(3u, list::cons<unsigned int>::make(4u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(3u, list::cons<unsigned int>::make(4u, list::cons<unsigned int>::make(5u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(4u, list::cons<unsigned int>::make(5u, list::cons<unsigned int>::make(6u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(5u, list::cons<unsigned int>::make(6u, list::cons<unsigned int>::make(7u, list::cons<unsigned int>::make(10u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(6u, list::cons<unsigned int>::make(7u, list::cons<unsigned int>::make(8u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(7u, list::cons<unsigned int>::make(8u, list::cons<unsigned int>::make(9u, list::cons<unsigned int>::make(14u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(8u, list::cons<unsigned int>::make(9u, list::cons<unsigned int>::make(10u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(9u, list::cons<unsigned int>::make(10u, list::cons<unsigned int>::make(11u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(10u, list::cons<unsigned int>::make(11u, list::cons<unsigned int>::make(12u, list::cons<unsigned int>::make(15u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(11u, list::cons<unsigned int>::make(12u, list::cons<unsigned int>::make(13u, list::cons<unsigned int>::make(22u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(12u, list::cons<unsigned int>::make(13u, list::cons<unsigned int>::make(14u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(13u, list::cons<unsigned int>::make(14u, list::cons<unsigned int>::make(15u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(14u, list::cons<unsigned int>::make(15u, list::cons<unsigned int>::make(16u, list::cons<unsigned int>::make(21u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(15u, list::cons<unsigned int>::make(16u, list::cons<unsigned int>::make(17u, list::cons<unsigned int>::make(20u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(16u, list::cons<unsigned int>::make(17u, list::cons<unsigned int>::make(18u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(17u, list::cons<unsigned int>::make(18u, list::cons<unsigned int>::make(19u, list::cons<unsigned int>::make(24u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(18u, list::cons<unsigned int>::make(19u, list::cons<unsigned int>::make(20u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(19u, list::cons<unsigned int>::make(20u, list::cons<unsigned int>::make(21u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(20u, list::cons<unsigned int>::make(21u, list::cons<unsigned int>::make(22u, list::cons<unsigned int>::make(25u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(21u, list::cons<unsigned int>::make(22u, list::cons<unsigned int>::make(23u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(22u, list::cons<unsigned int>::make(23u, list::cons<unsigned int>::make(24u, list::cons<unsigned int>::make(33u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(23u, list::cons<unsigned int>::make(24u, list::cons<unsigned int>::make(25u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(24u, list::cons<unsigned int>::make(25u, list::cons<unsigned int>::make(26u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(25u, list::cons<unsigned int>::make(26u, list::cons<unsigned int>::make(27u, list::cons<unsigned int>::make(30u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(26u, list::cons<unsigned int>::make(27u, list::cons<unsigned int>::make(28u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(27u, list::cons<unsigned int>::make(28u, list::cons<unsigned int>::make(29u, list::cons<unsigned int>::make(34u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(28u, list::cons<unsigned int>::make(29u, list::cons<unsigned int>::make(30u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(29u, list::cons<unsigned int>::make(30u, list::cons<unsigned int>::make(31u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(30u, list::cons<unsigned int>::make(31u, list::cons<unsigned int>::make(32u, list::cons<unsigned int>::make(35u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(31u, list::cons<unsigned int>::make(32u, list::cons<unsigned int>::make(33u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(32u, list::cons<unsigned int>::make(33u, list::cons<unsigned int>::make(34u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(33u, list::cons<unsigned int>::make(34u, list::cons<unsigned int>::make(35u, list::cons<unsigned int>::make(44u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(34u, list::cons<unsigned int>::make(35u, list::cons<unsigned int>::make(36u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(35u, list::cons<unsigned int>::make(36u, list::cons<unsigned int>::make(37u, list::cons<unsigned int>::make(40u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(36u, list::cons<unsigned int>::make(37u, list::cons<unsigned int>::make(38u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(37u, list::cons<unsigned int>::make(38u, list::cons<unsigned int>::make(39u, list::cons<unsigned int>::make(46u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(38u, list::cons<unsigned int>::make(39u, list::cons<unsigned int>::make(40u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(39u, list::cons<unsigned int>::make(40u, list::cons<unsigned int>::make(41u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(40u, list::cons<unsigned int>::make(41u, list::cons<unsigned int>::make(42u, list::cons<unsigned int>::make(45u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(41u, list::cons<unsigned int>::make(42u, list::cons<unsigned int>::make(43u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(42u, list::cons<unsigned int>::make(43u, list::cons<unsigned int>::make(44u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(43u, list::cons<unsigned int>::make(44u, list::cons<unsigned int>::make(45u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(44u, list::cons<unsigned int>::make(45u, list::cons<unsigned int>::make(46u, list::cons<unsigned int>::make(55u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(45u, list::cons<unsigned int>::make(46u, list::cons<unsigned int>::make(47u, list::cons<unsigned int>::make(50u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(46u, list::cons<unsigned int>::make(47u, list::cons<unsigned int>::make(48u, list::cons<unsigned int>::make(53u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(47u, list::cons<unsigned int>::make(48u, list::cons<unsigned int>::make(49u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(48u, list::cons<unsigned int>::make(49u, list::cons<unsigned int>::make(50u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(49u, list::cons<unsigned int>::make(50u, list::cons<unsigned int>::make(51u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(50u, list::cons<unsigned int>::make(51u, list::cons<unsigned int>::make(52u, list::cons<unsigned int>::make(55u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(51u, list::cons<unsigned int>::make(52u, list::cons<unsigned int>::make(53u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(52u, list::cons<unsigned int>::make(53u, list::cons<unsigned int>::make(54u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(53u, list::cons<unsigned int>::make(54u, list::cons<unsigned int>::make(55u, list::cons<unsigned int>::make(64u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(54u, list::cons<unsigned int>::make(55u, list::cons<unsigned int>::make(56u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(55u, list::cons<unsigned int>::make(56u, list::cons<unsigned int>::make(57u, list::cons<unsigned int>::make(60u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(56u, list::cons<unsigned int>::make(57u, list::cons<unsigned int>::make(58u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(57u, list::cons<unsigned int>::make(58u, list::cons<unsigned int>::make(59u, list::cons<unsigned int>::make(66u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(58u, list::cons<unsigned int>::make(59u, list::cons<unsigned int>::make(60u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(59u, list::cons<unsigned int>::make(60u, list::cons<unsigned int>::make(61u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(60u, list::cons<unsigned int>::make(61u, list::cons<unsigned int>::make(62u, list::cons<unsigned int>::make(65u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(61u, list::cons<unsigned int>::make(62u, list::cons<unsigned int>::make(63u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(62u, list::cons<unsigned int>::make(63u, list::cons<unsigned int>::make(64u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(63u, list::cons<unsigned int>::make(64u, list::cons<unsigned int>::make(65u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(64u, list::cons<unsigned int>::make(65u, list::cons<unsigned int>::make(66u, list::cons<unsigned int>::make(75u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(65u, list::cons<unsigned int>::make(66u, list::cons<unsigned int>::make(67u, list::cons<unsigned int>::make(70u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(66u, list::cons<unsigned int>::make(67u, list::cons<unsigned int>::make(68u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(67u, list::cons<unsigned int>::make(68u, list::cons<unsigned int>::make(69u, list::cons<unsigned int>::make(74u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(68u, list::cons<unsigned int>::make(69u, list::cons<unsigned int>::make(70u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(69u, list::cons<unsigned int>::make(70u, list::cons<unsigned int>::make(71u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(70u, list::cons<unsigned int>::make(71u, list::cons<unsigned int>::make(72u, list::cons<unsigned int>::make(75u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(71u, list::cons<unsigned int>::make(72u, list::cons<unsigned int>::make(73u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(72u, list::cons<unsigned int>::make(73u, list::cons<unsigned int>::make(74u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(73u, list::cons<unsigned int>::make(74u, list::cons<unsigned int>::make(75u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(74u, list::cons<unsigned int>::make(75u, list::cons<unsigned int>::make(76u, list::cons<unsigned int>::make(85u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(75u, list::cons<unsigned int>::make(76u, list::cons<unsigned int>::make(77u, list::cons<unsigned int>::make(80u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(76u, list::cons<unsigned int>::make(77u, list::cons<unsigned int>::make(78u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(77u, list::cons<unsigned int>::make(78u, list::cons<unsigned int>::make(79u, list::cons<unsigned int>::make(84u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(78u, list::cons<unsigned int>::make(79u, list::cons<unsigned int>::make(80u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(79u, list::cons<unsigned int>::make(80u, list::cons<unsigned int>::make(81u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(80u, list::cons<unsigned int>::make(81u, list::cons<unsigned int>::make(82u, list::cons<unsigned int>::make(85u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(81u, list::cons<unsigned int>::make(82u, list::cons<unsigned int>::make(83u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(82u, list::cons<unsigned int>::make(83u, list::cons<unsigned int>::make(84u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(83u, list::cons<unsigned int>::make(84u, list::cons<unsigned int>::make(85u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(84u, list::cons<unsigned int>::make(85u, list::cons<unsigned int>::make(86u, list::cons<unsigned int>::make(95u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(85u, list::cons<unsigned int>::make(86u, list::cons<unsigned int>::make(87u, list::cons<unsigned int>::make(90u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(86u, list::cons<unsigned int>::make(87u, list::cons<unsigned int>::make(88u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(87u, list::cons<unsigned int>::make(88u, list::cons<unsigned int>::make(89u, list::cons<unsigned int>::make(94u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(88u, list::cons<unsigned int>::make(89u, list::cons<unsigned int>::make(90u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(89u, list::cons<unsigned int>::make(90u, list::cons<unsigned int>::make(91u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(90u, list::cons<unsigned int>::make(91u, list::cons<unsigned int>::make(92u, list::cons<unsigned int>::make(95u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(91u, list::cons<unsigned int>::make(92u, list::cons<unsigned int>::make(93u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(92u, list::cons<unsigned int>::make(93u, list::cons<unsigned int>::make(94u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(93u, list::cons<unsigned int>::make(94u, list::cons<unsigned int>::make(95u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(94u, list::cons<unsigned int>::make(95u, list::cons<unsigned int>::make(96u, list::cons<unsigned int>::make(105u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(95u, list::cons<unsigned int>::make(96u, list::cons<unsigned int>::make(97u, list::cons<unsigned int>::make(100u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(96u, list::cons<unsigned int>::make(97u, list::cons<unsigned int>::make(98u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(97u, list::cons<unsigned int>::make(98u, list::cons<unsigned int>::make(99u, list::cons<unsigned int>::make(104u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(98u, list::cons<unsigned int>::make(99u, list::cons<unsigned int>::make(100u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(99u, list::cons<unsigned int>::make(100u, list::cons<unsigned int>::make(101u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(100u, list::cons<unsigned int>::make(101u, list::cons<unsigned int>::make(102u, list::cons<unsigned int>::make(105u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(101u, list::cons<unsigned int>::make(102u, list::cons<unsigned int>::make(103u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(102u, list::cons<unsigned int>::make(103u, list::cons<unsigned int>::make(104u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(103u, list::cons<unsigned int>::make(104u, list::cons<unsigned int>::make(105u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(104u, list::cons<unsigned int>::make(105u, list::cons<unsigned int>::make(106u, list::cons<unsigned int>::make(115u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(105u, list::cons<unsigned int>::make(106u, list::cons<unsigned int>::make(107u, list::cons<unsigned int>::make(110u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(106u, list::cons<unsigned int>::make(107u, list::cons<unsigned int>::make(108u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(107u, list::cons<unsigned int>::make(108u, list::cons<unsigned int>::make(109u, list::cons<unsigned int>::make(114u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(108u, list::cons<unsigned int>::make(109u, list::cons<unsigned int>::make(110u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(109u, list::cons<unsigned int>::make(110u, list::cons<unsigned int>::make(111u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(110u, list::cons<unsigned int>::make(111u, list::cons<unsigned int>::make(112u, list::cons<unsigned int>::make(115u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(111u, list::cons<unsigned int>::make(112u, list::cons<unsigned int>::make(113u, list::cons<unsigned int>::make(122u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(112u, list::cons<unsigned int>::make(113u, list::cons<unsigned int>::make(114u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(113u, list::cons<unsigned int>::make(114u, list::cons<unsigned int>::make(115u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(114u, list::cons<unsigned int>::make(115u, list::cons<unsigned int>::make(116u, list::cons<unsigned int>::make(121u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(115u, list::cons<unsigned int>::make(116u, list::cons<unsigned int>::make(117u, list::cons<unsigned int>::make(120u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(116u, list::cons<unsigned int>::make(117u, list::cons<unsigned int>::make(118u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(117u, list::cons<unsigned int>::make(118u, list::cons<unsigned int>::make(119u, list::cons<unsigned int>::make(124u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(118u, list::cons<unsigned int>::make(119u, list::cons<unsigned int>::make(120u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(119u, list::cons<unsigned int>::make(120u, list::cons<unsigned int>::make(121u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(120u, list::cons<unsigned int>::make(121u, list::cons<unsigned int>::make(122u, list::cons<unsigned int>::make(125u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(121u, list::cons<unsigned int>::make(122u, list::cons<unsigned int>::make(123u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(122u, list::cons<unsigned int>::make(123u, list::cons<unsigned int>::make(124u, list::cons<unsigned int>::make(133u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(123u, list::cons<unsigned int>::make(124u, list::cons<unsigned int>::make(125u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(124u, list::cons<unsigned int>::make(125u, list::cons<unsigned int>::make(126u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(125u, list::cons<unsigned int>::make(126u, list::cons<unsigned int>::make(127u, list::cons<unsigned int>::make(130u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(126u, list::cons<unsigned int>::make(127u, list::cons<unsigned int>::make(128u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(127u, list::cons<unsigned int>::make(128u, list::cons<unsigned int>::make(129u, list::cons<unsigned int>::make(134u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(128u, list::cons<unsigned int>::make(129u, list::cons<unsigned int>::make(130u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(129u, list::cons<unsigned int>::make(130u, list::cons<unsigned int>::make(131u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(130u, list::cons<unsigned int>::make(131u, list::cons<unsigned int>::make(132u, list::cons<unsigned int>::make(135u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(131u, list::cons<unsigned int>::make(132u, list::cons<unsigned int>::make(133u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(132u, list::cons<unsigned int>::make(133u, list::cons<unsigned int>::make(134u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(133u, list::cons<unsigned int>::make(134u, list::cons<unsigned int>::make(135u, list::cons<unsigned int>::make(144u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(134u, list::cons<unsigned int>::make(135u, list::cons<unsigned int>::make(136u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(135u, list::cons<unsigned int>::make(136u, list::cons<unsigned int>::make(137u, list::cons<unsigned int>::make(140u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(136u, list::cons<unsigned int>::make(137u, list::cons<unsigned int>::make(138u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(137u, list::cons<unsigned int>::make(138u, list::cons<unsigned int>::make(139u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(138u, list::cons<unsigned int>::make(139u, list::cons<unsigned int>::make(140u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(139u, list::cons<unsigned int>::make(140u, list::cons<unsigned int>::make(141u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(140u, list::cons<unsigned int>::make(141u, list::cons<unsigned int>::make(142u, list::cons<unsigned int>::make(145u, list::cons<unsigned int>::make(147u, list::nil<unsigned int>::make()))))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(141u, list::cons<unsigned int>::make(142u, list::cons<unsigned int>::make(143u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(142u, list::cons<unsigned int>::make(143u, list::cons<unsigned int>::make(144u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(143u, list::cons<unsigned int>::make(144u, list::cons<unsigned int>::make(145u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(144u, list::cons<unsigned int>::make(145u, list::cons<unsigned int>::make(146u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(145u, list::cons<unsigned int>::make(146u, list::cons<unsigned int>::make(147u, list::cons<unsigned int>::make(150u, list::nil<unsigned int>::make())))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(146u, list::cons<unsigned int>::make(147u, list::cons<unsigned int>::make(148u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(147u, list::cons<unsigned int>::make(148u, list::cons<unsigned int>::make(149u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(148u, list::cons<unsigned int>::make(149u, list::cons<unsigned int>::make(150u, list::nil<unsigned int>::make()))), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(149u, list::cons<unsigned int>::make(150u, list::nil<unsigned int>::make())), list::cons<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make(bsl::make_pair(150u, list::nil<unsigned int>::make()), list::nil<bsl::pair<unsigned int, bsl::shared_ptr<list::list<unsigned int>>>>::make()))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))));

std::string benchmark(const bsl::shared_ptr<unit::unit> _x);
