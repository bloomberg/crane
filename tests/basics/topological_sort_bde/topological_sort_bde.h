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
    bsl::unique_ptr<List<t_A>> d_a1;
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
  List(const List<t_A> &_other) : d_v_(bsl::move(_other.clone().d_v_)) {}
  List(List<t_A> &&_other) : d_v_(bsl::move(_other.d_v_)) {}
  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }
  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }
  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = bsl::get<Cons>(_sv.v());
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }
  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }
  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{bsl::move(a0), bsl::make_unique<List<t_A>>(a1)});
  }
  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }
  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }
  __attribute__((pure)) const List<t_A> *operator->() const { return this; }
  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }
  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }
  // MANIPULATORS
  void reset() { *this = List<t_A>(); }
  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
  template <typename T1>
  __attribute__((pure)) List<bsl::pair<t_A, T1>>
  combine(const List<T1> &l_) const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<bsl::pair<t_A, T1>>::nil();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      if (bsl::holds_alternative<typename List<T1>::Nil>(l_.v())) {
        return List<bsl::pair<t_A, T1>>::nil();
      } else {
        const auto &[d_a00, d_a10] = bsl::get<typename List<T1>::Cons>(l_.v());
        return List<bsl::pair<t_A, T1>>::cons(
            bsl::make_pair(d_a0, d_a00),
            (*(d_a1)).template combine<T1>(*(d_a10)));
      }
    }
  }
  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) bsl::optional<t_A> find(F0 &&f) const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return bsl::optional<t_A>();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      if (f(d_a0)) {
        return bsl::make_optional<t_A>(d_a0);
      } else {
        return (*(d_a1)).find(f);
      }
    }
  }
  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) List<t_A> filter(F0 &&f) const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      if (f(d_a0)) {
        return List<t_A>::cons(d_a0, (*(d_a1)).filter(f));
      } else {
        return (*(d_a1)).filter(f);
      }
    }
  }
  template <typename T1, MapsTo<T1, t_A, T1> F0>
  T1 fold_right(F0 &&f, const T1 a0) const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      return f(d_a0, (*(d_a1)).template fold_right<T1>(f, a0));
    }
  }
  template <typename T1> __attribute__((pure)) List<T1> concat() const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<List<T1>>::Cons>(_sv.v());
      return d_a0.app((*(d_a1)).template concat<T1>());
    }
  }
  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }
  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }
  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (bsl::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};
struct ListDef {
  __attribute__((pure)) static List<unsigned int> seq(unsigned int start,
                                                      const unsigned int &len);
};
struct ToString {
  template <typename T1, typename T2, MapsTo<bsl::string, T1> F0,
            MapsTo<bsl::string, T2> F1>
  __attribute__((pure)) static bsl::string
  pair_to_string(F0 &&p1, F1 &&p2, const bsl::pair<T1, T2> &x) {
    T1 a = x.first;
    T2 b = x.second;
    return "("_s + p1(a) + ", "_s + p2(b) + ")"_s;
  }
  template <typename T1, MapsTo<bsl::string, T1> F0>
  __attribute__((pure)) static bsl::string
  intersperse(F0 &&p, const bsl::string sep, const List<T1> &l) {
    if (bsl::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (bsl::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return sep + p(d_a0);
      } else {
        return sep + p(d_a0) + intersperse<T1>(p, sep, *(d_a1));
      }
    }
  }
  template <typename T1, MapsTo<bsl::string, T1> F0>
  __attribute__((pure)) static bsl::string list_to_string(F0 &&p,
                                                          const List<T1> &l) {
    if (bsl::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[d_a0, d_a1] = bsl::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (bsl::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return "["_s + p(d_a0) + "]"_s;
      } else {
        return "["_s + p(d_a0) + intersperse<T1>(p, "; ", *(d_a1)) + "]"_s;
      }
    }
  }
};
struct TopologicalSort {
  template <typename node> using entry = bsl::pair<node, List<node>>;
  template <typename node> using graph = List<entry<node>>;
  template <typename node> using order = List<List<node>>;
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
  get_elems(F0 &&eqb_node, const List<bsl::pair<T1, T1>> &l) {
    bsl::function<List<T1>(List<bsl::pair<T1, T1>>, List<T1>)> get_elems_aux;
    get_elems_aux = [&](List<bsl::pair<T1, T1>> l0, List<T1> h) -> List<T1> {
      if (bsl::holds_alternative<typename List<bsl::pair<T1, T1>>::Nil>(
              l0.v())) {
        return h;
      } else {
        const auto &[d_a0, d_a1] =
            bsl::get<typename List<bsl::pair<T1, T1>>::Cons>(l0.v());
        List<bsl::pair<T1, T1>> d_a1_value = List<std::pair<T1, T1>>(*(d_a1));
        T1 e1 = d_a0.first;
        T1 e2 = d_a0.second;
        bsl::optional<T1> f1 =
            h.find([=](const T1 x) mutable { return eqb_node(e1, x); });
        bsl::optional<T1> f2 =
            h.find([=](const T1 x) mutable { return eqb_node(e2, x); });
        if (f1.has_value()) {
          T1 _x = *f1;
          if (f2.has_value()) {
            T1 _x0 = *f2;
            return get_elems_aux(d_a1_value, h);
          } else {
            return get_elems_aux(d_a1_value, List<T1>::cons(e2, h));
          }
        } else {
          if (f2.has_value()) {
            T1 _x = *f2;
            return get_elems_aux(d_a1_value, List<T1>::cons(e1, h));
          } else {
            if (eqb_node(e1, e2)) {
              return get_elems_aux(d_a1_value, List<T1>::cons(e1, h));
            } else {
              return get_elems_aux(d_a1_value,
                                   List<T1>::cons(e1, List<T1>::cons(e2, h)));
            }
          }
        }
      }
    };
    return get_elems_aux(l, List<T1>::nil());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static entry<T1>
  make_entry(F0 &&eqb_node, const List<bsl::pair<T1, T1>> &l, const T1 e) {
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
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static graph<T1> make_graph(F0 &&eqb_node,
                                                    List<bsl::pair<T1, T1>> l) {
    List<T1> elems = get_elems<T1>(eqb_node, l);
    return elems.template fold_right<List<entry<T1>>>(
        [=](const T1 e, List<bsl::pair<T1, List<T1>>> ret) mutable {
          return List<bsl::pair<T1, List<T1>>>::cons(
              make_entry<T1>(eqb_node, l, e), ret);
        },
        List<bsl::pair<T1, List<T1>>>::nil());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
  graph_lookup(F0 &&eqb_node, const T1 elem,
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
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bool contains(F0 &&eqb_node, const T1 elem,
                                             const List<T1> &es) {
    auto _cs = es.find([=](const T1 x) mutable { return eqb_node(elem, x); });
    if (_cs.has_value()) {
      T1 _x = *_cs;
      return true;
    } else {
      return false;
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  static T1
  cycle_entry_aux(F0 &&eqb_node, const List<bsl::pair<T1, List<T1>>> &graph0,
                  List<T1> seens, const T1 elem, const unsigned int &counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        unsigned int c = counter - 1;
        List<T1> l = graph_lookup<T1>(eqb_node, elem, graph0);
        if (bsl::holds_alternative<typename List<T1>::Nil>(l.v())) {
          return elem;
        } else {
          const auto &[d_a0, d_a1] = bsl::get<typename List<T1>::Cons>(l.v());
          return cycle_entry_aux<T1>(eqb_node, graph0,
                                     List<T1>::cons(elem, seens), d_a0, c);
        }
      }
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static bsl::optional<T1>
  cycle_entry(F0 &&eqb_node, const List<bsl::pair<T1, List<T1>>> &graph0) {
    if (bsl::holds_alternative<typename List<bsl::pair<T1, List<T1>>>::Nil>(
            graph0.v())) {
      return bsl::optional<T1>();
    } else {
      const auto &[d_a0, d_a1] =
          bsl::get<typename List<bsl::pair<T1, List<T1>>>::Cons>(graph0.v());
      T1 e = std::pair<T1, List<T1>>(d_a0).first;
      List<T1> _x0 = std::pair<T1, List<T1>>(d_a0).second;
      return bsl::make_optional<T1>(cycle_entry_aux<T1>(
          eqb_node, graph0, List<T1>::nil(), e, graph0.length()));
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
  cycle_extract_aux(F0 &&eqb_node, List<bsl::pair<T1, List<T1>>> graph0,
                    const unsigned int &counter, const T1 elem, List<T1> cycl) {
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
                List<T1>::cons(elem, cycl));
      }
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
  cycle_extract(F0 &&eqb_node, const List<bsl::pair<T1, List<T1>>> &graph0) {
    auto _cs = cycle_entry<T1>(eqb_node, graph0);
    if (_cs.has_value()) {
      T1 elem = *_cs;
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0.length(), elem,
                                   List<T1>::nil());
    } else {
      return List<T1>::nil();
    }
  }
  template <typename T1>
  __attribute__((pure)) static bool null(const List<T1> &xs) {
    if (bsl::holds_alternative<typename List<T1>::Nil>(xs.v())) {
      return true;
    } else {
      return false;
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static order<T1>
  topological_sort_aux(F0 &&eqb_node,
                       const List<bsl::pair<T1, List<T1>>> &graph0,
                       const unsigned int &counter) {
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
            rest.template map<bsl::pair<T1, List<T1>>>(
                [=](const bsl::pair<T1, List<T1>> &entry0) mutable {
                  return bsl::make_pair(
                      entry0.first,
                      entry0.second.filter([=](const T1 e) mutable {
                        return !(contains<T1>(eqb_node, e, mins_));
                      }));
                });
        return List<List<T1>>::cons(
            mins_, topological_sort_aux<T1>(eqb_node, rest_, c));
      }
    }
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<List<T1>>
  topological_sort(F0 &&eqb_node, const List<bsl::pair<T1, T1>> &g) {
    List<bsl::pair<T1, List<T1>>> g_ = make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_.length());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static order<T1>
  topological_sort_graph(F0 &&eqb_node,
                         const List<bsl::pair<T1, List<T1>>> &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0.length());
  }
  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<bsl::pair<T1, unsigned int>>
  topological_rank_list(F0 &&eqb_node,
                        const List<bsl::pair<T1, List<T1>>> &graph0) {
    List<List<T1>> lorder = topological_sort_graph<T1>(eqb_node, graph0);
    return lorder
        .template combine<unsigned int>(ListDef::seq(0u, lorder.length()))
        .template map<List<bsl::pair<T1, unsigned int>>>(
            [](const bsl::pair<List<T1>, unsigned int> &x) {
              List<T1> fs = x.first;
              unsigned int rk = x.second;
              return fs.template map<bsl::pair<T1, unsigned int>>(
                  [=](const T1 f) mutable { return bsl::make_pair(f, rk); });
            })
        .template concat<bsl::pair<T1, unsigned int>>();
  }
};

#endif // INCLUDED_TOPOLOGICAL_SORT_BDE
