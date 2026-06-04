#ifndef INCLUDED_TOPOLOGICAL_SORT
#define INCLUDED_TOPOLOGICAL_SORT

#include <any>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1>
  List<std::pair<A, T1>> combine(const List<T1> &l_) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<std::pair<A, T1>>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      if (std::holds_alternative<typename List<T1>::Nil>(l_.v())) {
        return List<std::pair<A, T1>>::nil();
      } else {
        const auto &[a00, a10] = std::get<typename List<T1>::Cons>(l_.v());
        return List<std::pair<A, T1>>::cons(std::make_pair(a0, a00),
                                            a1->template combine<T1>(*a10));
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  std::optional<A> find(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return std::optional<A>();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      if (f(a0)) {
        return std::make_optional<A>(a0);
      } else {
        return a1->find(f);
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      if (f(a0)) {
        return List<A>::cons(a0, a1->filter(f));
      } else {
        return a1->filter(f);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return a0;
    } else {
      const auto &[a1, a2] = std::get<typename List<A>::Cons>(this->v());
      return f(a1, a2->template fold_right<T1>(f, a0));
    }
  }

  template <typename T1> List<T1> concat() const {
    if (std::holds_alternative<typename List<List<T1>>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<List<T1>>::Cons>(this->v());
      return a0.app(a1->template concat<T1>());
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }

  uint64_t length() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return (a1->length() + 1);
    }
  }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct ToString {
  template <typename T1, typename T2, typename F0, typename F1>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &> &&
             std::is_invocable_r_v<std::string, F1 &, T2 &>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> &x) {
    const T1 &a = x.first;
    const T2 &b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &>
  static std::string intersperse(F0 &&p, std::string sep, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return sep + p(a0);
      } else {
        return sep + p(a0) + intersperse<T1>(p, sep, *a1);
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<std::string, F0 &, T1 &>
  static std::string list_to_string(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *a1;
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return "["s + p(a0) + "]"s;
      } else {
        return "["s + p(a0) + intersperse<T1>(p, "; ", *a1) + "]"s;
      }
    }
  }
};

struct TopologicalSort {
  template <typename node> using entry = std::pair<node, List<node>>;
  template <typename node> using graph = List<entry<node>>;
  template <typename node> using order = List<List<node>>;

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> get_elems(F0 &&eqb_node, const List<std::pair<T1, T1>> &l) {
    auto get_elems_aux_impl = [&](auto &_self_get_elems_aux,
                                  const List<std::pair<T1, T1>> &l0,
                                  List<T1> h) -> List<T1> {
      if (std::holds_alternative<typename List<std::pair<T1, T1>>::Nil>(
              l0.v())) {
        return h;
      } else {
        const auto &[a0, a1] =
            std::get<typename List<std::pair<T1, T1>>::Cons>(l0.v());
        const List<std::pair<T1, T1>> &a1_value = *a1;
        const T1 &e1 = a0.first;
        const T1 &e2 = a0.second;
        std::optional<T1> f1 =
            h.find([=](const T1 &x) mutable { return eqb_node(e1, x); });
        std::optional<T1> f2 =
            h.find([=](const T1 &x) mutable { return eqb_node(e2, x); });
        if (f1.has_value()) {
          const T1 &_x = *f1;
          if (f2.has_value()) {
            const T1 &_x0 = *f2;
            return _self_get_elems_aux(_self_get_elems_aux, a1_value,
                                       std::move(h));
          } else {
            return _self_get_elems_aux(_self_get_elems_aux, a1_value,
                                       List<T1>::cons(e2, std::move(h)));
          }
        } else {
          if (f2.has_value()) {
            const T1 &_x = *f2;
            return _self_get_elems_aux(_self_get_elems_aux, a1_value,
                                       List<T1>::cons(e1, std::move(h)));
          } else {
            if (eqb_node(e1, e2)) {
              return _self_get_elems_aux(_self_get_elems_aux, a1_value,
                                         List<T1>::cons(e1, std::move(h)));
            } else {
              return _self_get_elems_aux(
                  _self_get_elems_aux, a1_value,
                  List<T1>::cons(e1, List<T1>::cons(e2, std::move(h))));
            }
          }
        }
      }
    };
    auto get_elems_aux = [&](const List<std::pair<T1, T1>> &l0,
                             List<T1> h) -> List<T1> {
      return get_elems_aux_impl(get_elems_aux_impl, l0, h);
    };
    return get_elems_aux(l, List<T1>::nil());
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static entry<T1> make_entry(F0 &&eqb_node, const List<std::pair<T1, T1>> &l,
                              T1 e) {
    return std::make_pair(
        e, l.template fold_right<List<T1>>(
               [=](const std::pair<T1, T1> &x, List<T1> ret) mutable {
                 if (eqb_node(e, x.first)) {
                   return List<T1>::cons(x.second, ret);
                 } else {
                   return ret;
                 }
               },
               List<T1>::nil()));
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static graph<T1> make_graph(F0 &&eqb_node, List<std::pair<T1, T1>> l) {
    List<T1> elems = get_elems<T1>(eqb_node, l);
    return std::move(elems).template fold_right<List<entry<T1>>>(
        [=](const T1 &e, List<std::pair<T1, List<T1>>> ret) mutable {
          return List<std::pair<T1, List<T1>>>::cons(
              make_entry<T1>(eqb_node, l, e), ret);
        },
        List<std::pair<T1, List<T1>>>::nil());
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> graph_lookup(F0 &&eqb_node, const T1 &elem,
                               const List<std::pair<T1, List<T1>>> &graph0) {
    auto _cs = graph0.find([=](const std::pair<T1, List<T1>> &entry0) mutable {
      return eqb_node(elem, entry0.first);
    });
    if (_cs.has_value()) {
      const std::pair<T1, List<T1>> &p = *_cs;
      const T1 &_x = p.first;
      const List<T1> &es = p.second;
      return es;
    } else {
      return List<T1>::nil();
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static bool contains(F0 &&eqb_node, const T1 &elem, const List<T1> &es) {
    auto _cs = es.find([=](const T1 &x) mutable { return eqb_node(elem, x); });
    if (_cs.has_value()) {
      const T1 &_x = *_cs;
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static T1 cycle_entry_aux(F0 &&eqb_node,
                            const List<std::pair<T1, List<T1>>> &graph0,
                            List<T1> seens, T1 elem, uint64_t counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        uint64_t c = counter - 1;
        List<T1> l = graph_lookup<T1>(eqb_node, elem, graph0);
        if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
          return elem;
        } else {
          auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v_mut());
          return cycle_entry_aux<T1>(eqb_node, graph0,
                                     List<T1>::cons(elem, std::move(seens)),
                                     std::move(a0), c);
        }
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static std::optional<T1>
  cycle_entry(F0 &&eqb_node, const List<std::pair<T1, List<T1>>> &graph0) {
    if (std::holds_alternative<typename List<std::pair<T1, List<T1>>>::Nil>(
            graph0.v())) {
      return std::optional<T1>();
    } else {
      const auto &[a0, a1] =
          std::get<typename List<std::pair<T1, List<T1>>>::Cons>(graph0.v());
      const T1 &e = std::make_pair(a0.first, (*a0.second)).first;
      const List<T1> &_x0 = std::make_pair(a0.first, (*a0.second)).second;
      return std::make_optional<T1>(cycle_entry_aux<T1>(
          eqb_node, graph0, List<T1>::nil(), e, graph0.length()));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> cycle_extract_aux(F0 &&eqb_node,
                                    const List<std::pair<T1, List<T1>>> &graph0,
                                    uint64_t counter, T1 elem, List<T1> cycl) {
    if (counter <= 0) {
      return cycl;
    } else {
      uint64_t c = counter - 1;
      if (contains<T1>(eqb_node, elem, cycl)) {
        return cycl;
      } else {
        return graph_lookup<T1>(eqb_node, elem, graph0)
            .template fold_right<List<T1>>(
                [=](T1 _x0, List<T1> _x1) mutable -> List<T1> {
                  return cycle_extract_aux<T1>(eqb_node, graph0, c, _x0, _x1);
                },
                List<T1>::cons(elem, std::move(cycl)));
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<T1> cycle_extract(F0 &&eqb_node,
                                const List<std::pair<T1, List<T1>>> &graph0) {
    auto _cs = cycle_entry<T1>(eqb_node, graph0);
    if (_cs.has_value()) {
      const T1 &elem = *_cs;
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0.length(), elem,
                                   List<T1>::nil());
    } else {
      return List<T1>::nil();
    }
  }

  template <typename T1> static bool null(const List<T1> &xs) {
    if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static order<T1>
  topological_sort_aux(F0 &&eqb_node,
                       const List<std::pair<T1, List<T1>>> &graph0,
                       uint64_t counter) {
    if (counter <= 0) {
      return List<List<T1>>::nil();
    } else {
      uint64_t c = counter - 1;
      if (null<entry<T1>>(graph0)) {
        return List<List<T1>>::nil();
      } else {
        List<T1> mins =
            graph0
                .filter([](const std::pair<T1, List<T1>> &p) {
                  return null<T1>(p.second);
                })
                .template map<T1>([](std::pair<T1, List<T1>> _x0) -> T1 {
                  return _x0.first;
                });
        List<T1> mins_;
        if (null<T1>(mins)) {
          mins_ = cycle_extract<T1>(eqb_node, graph0);
        } else {
          mins_ = mins;
        }
        List<std::pair<T1, List<T1>>> rest =
            graph0.filter([=](const std::pair<T1, List<T1>> &entry0) mutable {
              return !(contains<T1>(eqb_node, entry0.first, mins_));
            });
        List<std::pair<T1, List<T1>>> rest_ =
            std::move(rest).template map<std::pair<T1, List<T1>>>(
                [=](const std::pair<T1, List<T1>> &entry0) mutable {
                  return std::make_pair(
                      entry0.first,
                      entry0.second.filter([=](const T1 &e) mutable {
                        return !(contains<T1>(eqb_node, e, mins_));
                      }));
                });
        return List<List<T1>>::cons(
            std::move(mins_),
            topological_sort_aux<T1>(eqb_node, std::move(rest_), c));
      }
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<List<T1>> topological_sort(F0 &&eqb_node,
                                         const List<std::pair<T1, T1>> &g) {
    List<std::pair<T1, List<T1>>> g_ = make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_.length());
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static order<T1>
  topological_sort_graph(F0 &&eqb_node,
                         const List<std::pair<T1, List<T1>>> &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0.length());
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<bool, F0 &, T1 &, T1 &>
  static List<std::pair<T1, uint64_t>>
  topological_rank_list(F0 &&eqb_node,
                        const List<std::pair<T1, List<T1>>> &graph0) {
    List<List<T1>> lorder = topological_sort_graph<T1>(eqb_node, graph0);
    return lorder
        .template combine<uint64_t>(ListDef::seq(UINT64_C(0), lorder.length()))
        .template map<List<std::pair<T1, uint64_t>>>(
            [](std::pair<List<T1>, uint64_t> x) {
              const List<T1> &fs = x.first;
              const uint64_t &rk = x.second;
              return fs.template map<std::pair<T1, uint64_t>>(
                  [=](T1 f) mutable { return std::make_pair(f, rk); });
            })
        .template concat<std::pair<T1, uint64_t>>();
  }
};

#endif // INCLUDED_TOPOLOGICAL_SORT
