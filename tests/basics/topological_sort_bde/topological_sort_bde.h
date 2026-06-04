#ifndef INCLUDED_TOPOLOGICAL_SORT_BDE
#define INCLUDED_TOPOLOGICAL_SORT_BDE

#include <any>
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
#include <utility>

using namespace BloombergLP;
using namespace bsl::string_literals;

template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};
  struct Cons {
    t_A d_a;
    bsl::shared_ptr<List<t_A>> d_l;
  };
  using variant_t = bsl::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}
  explicit List(Nil _v) : d_v_(_v) {}
  explicit List(Cons _v) : d_v_(bsl::move(_v)) {}
  template <typename _U> explicit List(const List<_U> &_other) {
    if (bsl::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->d_v_ = Nil{};
    } else {
      const auto &[d_a, d_l] = std::get<typename List<_U>::Cons>(_other.v());
      this->d_v_ = Cons{
          [&]() -> t_A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (d_a.type() == typeid(t_A))
                return std::any_cast<t_A>(d_a);
              if constexpr (requires {
                              typename t_A::first_type;
                              typename t_A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(d_a);
                return t_A{
                    [&]() -> typename t_A::first_type {
                      if constexpr (std::is_same_v<typename t_A::first_type,
                                                   std::any>)
                        return _k;
                      else
                        return std::any_cast<typename t_A::first_type>(_k);
                    }(),
                    [&]() -> typename t_A::second_type {
                      if constexpr (std::is_same_v<typename t_A::second_type,
                                                   std::any>)
                        return _v;
                      else
                        return std::any_cast<typename t_A::second_type>(_v);
                    }()};
              }
              return std::any_cast<t_A>(d_a);
            } else
              return t_A(d_a);
          }(),
          d_l ? std::make_shared<List<t_A>>(*d_l) : nullptr};
    }
  }
  static List<t_A> nil() { return List(Nil{}); }
  static List<t_A> cons(t_A a, List<t_A> l) {
    return List(Cons{bsl::move(a), bsl::make_shared<List<t_A>>(bsl::move(l))});
  }
  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  const variant_t &v() const { return d_v_; }
  template <typename T1>
  List<bsl::pair<t_A, T1>> combine(const List<T1> &l_) const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<bsl::pair<t_A, T1>>::nil();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      if (bsl::holds_alternative<typename List<T1>::Nil>(l_.v())) {
        return List<bsl::pair<t_A, T1>>::nil();
      } else {
        const auto &[d_a00, d_a10] = bsl::get<typename List<T1>::Cons>(l_.v());
        return List<bsl::pair<t_A, T1>>::cons(
            bsl::make_pair(d_a0, d_a00), d_a1->template combine<T1>(*d_a10));
      }
    }
  }
  template <typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, t_A &>
  bsl::optional<t_A> find(F0 &&f) const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return bsl::optional<t_A>();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      if (f(d_a0)) {
        return bsl::make_optional<t_A>(d_a0);
      } else {
        return d_a1->find(f);
      }
    }
  }
  template <typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, t_A &>
  List<t_A> filter(F0 &&f) const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      if (f(d_a0)) {
        return List<t_A>::cons(d_a0, d_a1->filter(f));
      } else {
        return d_a1->filter(f);
      }
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<T1, F0 &, t_A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      return f(d_a0, d_a1->template fold_right<T1>(f, a0));
    }
  }
  template <typename T1> List<T1> concat() const {
    if (bsl::holds_alternative<typename List<List<T1>>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<List<T1>>::Cons>(this->v());
      return d_a0.app(d_a1->template concat<T1>());
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<T1, F0 &, t_A &>
  List<T1> map(F0 &&f) const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      return List<T1>::cons(f(d_a0), d_a1->template map<T1>(f));
    }
  }
  unsigned int length() const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      return (d_a1->length() + 1);
    }
  }
  List<t_A> app(List<t_A> m) const {
    if (bsl::holds_alternative<typename List<t_A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(this->v());
      return List<t_A>::cons(d_a0, d_a1->app(bsl::move(m)));
    }
  }
};
struct ListDef {
  static List<unsigned int> seq(unsigned int start, unsigned int len);
};
struct ToString {
  template <typename T1, typename T2, typename F0, typename F1>
    requires bsl::is_invocable_r_v<bsl::string, F0 &, T1 &> &&
             bsl::is_invocable_r_v<bsl::string, F1 &, T2 &>
  static bsl::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const bsl::pair<T1, T2> &x) {
    T1 a = x.first;
    T2 b = x.second;
    return "("_s + p1(a) + ", "_s + p2(b) + ")"_s;
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bsl::string, F0 &, T1 &>
  static bsl::string intersperse(F0 &&p, bsl::string sep, const List<T1> &l) {
    if (bsl::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *d_a1;
      if (bsl::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return sep + p(d_a0);
      } else {
        return sep + p(d_a0) + intersperse<T1>(p, sep, *d_a1);
      }
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bsl::string, F0 &, T1 &>
  static bsl::string list_to_string(F0 &&p, const List<T1> &l) {
    if (bsl::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *d_a1;
      if (bsl::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return "["_s + p(d_a0) + "]"_s;
      } else {
        return "["_s + p(d_a0) + intersperse<T1>(p, "; ", *d_a1) + "]"_s;
      }
    }
  }
};
struct TopologicalSort {
  template <typename node> using entry = bsl::pair<node, List<node>>;
  template <typename node> using graph = List<entry<node>>;
  template <typename node> using order = List<List<node>>;
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> get_elems(F0 &&eqb_node, const List<bsl::pair<T1, T1>> &l) {
    auto get_elems_aux_impl = [&](auto &_self_get_elems_aux,
                                  const List<bsl::pair<T1, T1>> &l0,
                                  List<T1> h) -> List<T1> {
      if (bsl::holds_alternative<typename List<bsl::pair<T1, T1>>::Nil>(
              l0.v())) {
        return h;
      } else {
        const auto &[d_a0, d_a1] =
            bsl::get<typename List<bsl::pair<T1, T1>>::Cons>(l0.v());
        const List<bsl::pair<T1, T1>> &d_a1_value = *d_a1;
        T1 e1 = d_a0.first;
        T1 e2 = d_a0.second;
        bsl::optional<T1> f1 =
            h.find([=](const T1 &x) mutable { return eqb_node(e1, x); });
        bsl::optional<T1> f2 =
            h.find([=](const T1 &x) mutable { return eqb_node(e2, x); });
        if (f1.has_value()) {
          T1 _x = *f1;
          if (f2.has_value()) {
            T1 _x0 = *f2;
            return _self_get_elems_aux(_self_get_elems_aux, d_a1_value,
                                       bsl::move(h));
          } else {
            return _self_get_elems_aux(_self_get_elems_aux, d_a1_value,
                                       List<T1>::cons(e2, bsl::move(h)));
          }
        } else {
          if (f2.has_value()) {
            T1 _x = *f2;
            return _self_get_elems_aux(_self_get_elems_aux, d_a1_value,
                                       List<T1>::cons(e1, bsl::move(h)));
          } else {
            if (eqb_node(e1, e2)) {
              return _self_get_elems_aux(_self_get_elems_aux, d_a1_value,
                                         List<T1>::cons(e1, bsl::move(h)));
            } else {
              return _self_get_elems_aux(
                  _self_get_elems_aux, d_a1_value,
                  List<T1>::cons(e1, List<T1>::cons(e2, bsl::move(h))));
            }
          }
        }
      }
    };
    auto get_elems_aux = [&](const List<bsl::pair<T1, T1>> &l0,
                             List<T1> h) -> List<T1> {
      return get_elems_aux_impl(get_elems_aux_impl, l0, h);
    };
    return get_elems_aux(l, List<T1>::nil());
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static entry<T1> make_entry(F0 &&eqb_node, const List<bsl::pair<T1, T1>> &l,
                              T1 e) {
    return bsl::make_pair(
        e, l.template fold_right<List<T1>>(
               [=](const bsl::pair<T1, T1> &x, List<T1> ret) mutable {
                 if (eqb_node(e, x.first)) {
                   return List<T1>::cons(x.second, ret);
                 } else {
                   return ret;
                 }
               },
               List<T1>::nil()));
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static graph<T1> make_graph(F0 &&eqb_node, List<bsl::pair<T1, T1>> l) {
    List<T1> elems = get_elems<T1>(eqb_node, l);
    return bsl::move(elems).template fold_right<List<entry<T1>>>(
        [=](const T1 &e, List<bsl::pair<T1, List<T1>>> ret) mutable {
          return List<bsl::pair<T1, List<T1>>>::cons(
              make_entry<T1>(eqb_node, l, e), ret);
        },
        List<bsl::pair<T1, List<T1>>>::nil());
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> graph_lookup(F0 &&eqb_node, const T1 &elem,
                               const List<bsl::pair<T1, List<T1>>> &graph0) {
    auto _cs = graph0.find([=](const bsl::pair<T1, List<T1>> &entry0) mutable {
      return eqb_node(elem, entry0.first);
    });
    if (_cs.has_value()) {
      bsl::pair<T1, List<T1>> p = *_cs;
      T1 _x = p.first;
      List<T1> es = p.second;
      return es;
    } else {
      return List<T1>::nil();
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool contains(F0 &&eqb_node, const T1 &elem, const List<T1> &es) {
    auto _cs = es.find([=](const T1 &x) mutable { return eqb_node(elem, x); });
    if (_cs.has_value()) {
      T1 _x = *_cs;
      return true;
    } else {
      return false;
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static T1 cycle_entry_aux(F0 &&eqb_node,
                            const List<bsl::pair<T1, List<T1>>> &graph0,
                            List<T1> seens, T1 elem, unsigned int counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        unsigned int c = counter - 1;
        List<T1> l = graph_lookup<T1>(eqb_node, elem, graph0);
        if (bsl::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
          return elem;
        } else {
          auto &[d_a0, d_a1] = bsl::get<typename List<T1>::Cons>(l.v_mut());
          return cycle_entry_aux<T1>(eqb_node, graph0,
                                     List<T1>::cons(elem, bsl::move(seens)),
                                     bsl::move(d_a0), c);
        }
      }
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bsl::optional<T1>
  cycle_entry(F0 &&eqb_node, const List<bsl::pair<T1, List<T1>>> &graph0) {
    if (bsl::holds_alternative<typename List<bsl::pair<T1, List<T1>>>::Nil>(
            graph0.v())) {
      return bsl::optional<T1>();
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<bsl::pair<T1, List<T1>>>::Cons>(graph0.v());
      T1 e = bsl::make_pair(d_a0.first, (*d_a0.second)).first;
      List<T1> _x0 = bsl::make_pair(d_a0.first, (*d_a0.second)).second;
      return bsl::make_optional<T1>(cycle_entry_aux<T1>(
          eqb_node, graph0, List<T1>::nil(), e, graph0.length()));
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1>
  cycle_extract_aux(F0 &&eqb_node, const List<bsl::pair<T1, List<T1>>> &graph0,
                    unsigned int counter, T1 elem, List<T1> cycl) {
    if (counter <= 0) {
      return cycl;
    } else {
      unsigned int c = counter - 1;
      if (contains<T1>(eqb_node, elem, cycl)) {
        return cycl;
      } else {
        return graph_lookup<T1>(eqb_node, elem, graph0)
            .template fold_right<List<T1>>(
                [=](T1 _x0, List<T1> _x1) mutable -> List<T1> {
                  return cycle_extract_aux<T1>(eqb_node, graph0, c, _x0, _x1);
                },
                List<T1>::cons(elem, bsl::move(cycl)));
      }
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> cycle_extract(F0 &&eqb_node,
                                const List<bsl::pair<T1, List<T1>>> &graph0) {
    auto _cs = cycle_entry<T1>(eqb_node, graph0);
    if (_cs.has_value()) {
      T1 elem = *_cs;
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0.length(), elem,
                                   List<T1>::nil());
    } else {
      return List<T1>::nil();
    }
  }
  template <typename T1> static bool null(const List<T1> &xs) {
    if (bsl::holds_alternative<typename List<T1>::Nil>(xs.v())) {
      return true;
    } else {
      return false;
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static order<T1>
  topological_sort_aux(F0 &&eqb_node,
                       const List<bsl::pair<T1, List<T1>>> &graph0,
                       unsigned int counter) {
    if (counter <= 0) {
      return List<List<T1>>::nil();
    } else {
      unsigned int c = counter - 1;
      if (null<entry<T1>>(graph0)) {
        return List<List<T1>>::nil();
      } else {
        List<T1> mins =
            graph0
                .filter([](const bsl::pair<T1, List<T1>> &p) {
                  return null<T1>(p.second);
                })
                .template map<T1>([](bsl::pair<T1, List<T1>> _x0) -> T1 {
                  return _x0.first;
                });
        List<T1> mins_;
        if (null<T1>(mins)) {
          mins_ = cycle_extract<T1>(eqb_node, graph0);
        } else {
          mins_ = mins;
        }
        List<bsl::pair<T1, List<T1>>> rest =
            graph0.filter([=](const bsl::pair<T1, List<T1>> &entry0) mutable {
              return !(contains<T1>(eqb_node, entry0.first, mins_));
            });
        List<bsl::pair<T1, List<T1>>> rest_ =
            bsl::move(rest).template map<bsl::pair<T1, List<T1>>>(
                [=](const bsl::pair<T1, List<T1>> &entry0) mutable {
                  return bsl::make_pair(
                      entry0.first,
                      entry0.second.filter([=](const T1 &e) mutable {
                        return !(contains<T1>(eqb_node, e, mins_));
                      }));
                });
        return List<List<T1>>::cons(
            bsl::move(mins_),
            topological_sort_aux<T1>(eqb_node, bsl::move(rest_), c));
      }
    }
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<List<T1>> topological_sort(F0 &&eqb_node,
                                         const List<bsl::pair<T1, T1>> &g) {
    List<bsl::pair<T1, List<T1>>> g_ = make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_.length());
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static order<T1>
  topological_sort_graph(F0 &&eqb_node,
                         const List<bsl::pair<T1, List<T1>>> &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0.length());
  }
  template <typename T1, typename F0>
    requires bsl::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<bsl::pair<T1, unsigned int>>
  topological_rank_list(F0 &&eqb_node,
                        const List<bsl::pair<T1, List<T1>>> &graph0) {
    List<List<T1>> lorder = topological_sort_graph<T1>(eqb_node, graph0);
    return lorder
        .template combine<unsigned int>(ListDef::seq(0u, lorder.length()))
        .template map<List<bsl::pair<T1, unsigned int>>>(
            [](bsl::pair<List<T1>, unsigned int> x) {
              List<T1> fs = x.first;
              unsigned int rk = x.second;
              return fs.template map<bsl::pair<T1, unsigned int>>(
                  [=](T1 f) mutable { return bsl::make_pair(f, rk); });
            })
        .template concat<bsl::pair<T1, unsigned int>>();
  }
};

#endif // INCLUDED_TOPOLOGICAL_SORT_BDE
