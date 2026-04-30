#ifndef INCLUDED_TOPOLOGICAL_SORT
#define INCLUDED_TOPOLOGICAL_SORT

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  List clone() const {
    List _out{};

    struct _CloneFrame {
      const List *_src;
      List *_dst;
    };

    std::vector<_CloneFrame> _stack;
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List *_src = _frame._src;
      List *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        const auto &_alt = std::get<Nil>(_src->v());
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ =
            Cons{_alt.d_a0, _alt.d_a1 ? std::make_unique<List>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1)
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List>> _stack;
    auto _drain = [&](List &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1)
          _stack.push_back(std::move(_alt.d_a1));
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node)
        _drain(*_node);
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }

  template <typename T1>
  List<std::pair<t_A, T1>> combine(const List<T1> &l_) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<std::pair<t_A, T1>>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      if (std::holds_alternative<typename List<T1>::Nil>(l_.v())) {
        return List<std::pair<t_A, T1>>::nil();
      } else {
        const auto &[d_a00, d_a10] = std::get<typename List<T1>::Cons>(l_.v());
        return List<std::pair<t_A, T1>>::cons(
            std::make_pair(d_a0, d_a00),
            (*(d_a1)).template combine<T1>(*(d_a10)));
      }
    }
  }

  template <MapsTo<bool, t_A> F0> std::optional<t_A> find(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return std::optional<t_A>();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      if (f(d_a0)) {
        return std::make_optional<t_A>(d_a0);
      } else {
        return (*(d_a1)).find(f);
      }
    }
  }

  template <MapsTo<bool, t_A> F0> List<t_A> filter(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<t_A>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
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
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return a0;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return f(d_a0, (*(d_a1)).template fold_right<T1>(f, a0));
    }
  }

  template <typename T1> List<T1> concat() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<T1>>::Cons>(_sv.v());
      return d_a0.app((*(d_a1)).template concat<T1>());
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0> List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }

  unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(std::move(m)));
    }
  }
};

struct ListDef {
  static List<unsigned int> seq(unsigned int start, const unsigned int &len);
};

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  static std::string pair_to_string(F0 &&p1, F1 &&p2,
                                    const std::pair<T1, T2> &x) {
    const T1 &a = x.first;
    const T2 &b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string intersperse(F0 &&p, const std::string sep,
                                 const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "";
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return sep + p(d_a0);
      } else {
        return sep + p(d_a0) + intersperse<T1>(p, sep, *(d_a1));
      }
    }
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  static std::string list_to_string(F0 &&p, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return "[]";
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
      auto &&_sv = *(d_a1);
      if (std::holds_alternative<typename List<T1>::Nil>(_sv.v())) {
        return "["s + p(d_a0) + "]"s;
      } else {
        return "["s + p(d_a0) + intersperse<T1>(p, "; ", *(d_a1)) + "]"s;
      }
    }
  }
};

struct TopologicalSort {
  template <typename node> using entry = std::pair<node, List<node>>;
  template <typename node> using graph = List<entry<node>>;
  template <typename node> using order = List<List<node>>;

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static List<T1> get_elems(F0 &&eqb_node, const List<std::pair<T1, T1>> &l) {
    std::function<List<T1>(List<std::pair<T1, T1>>, List<T1>)> get_elems_aux;
    get_elems_aux = [&](List<std::pair<T1, T1>> l0, List<T1> h) -> List<T1> {
      if (std::holds_alternative<typename List<std::pair<T1, T1>>::Nil>(
              l0.v())) {
        return h;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::pair<T1, T1>>::Cons>(l0.v());
        List<std::pair<T1, T1>> d_a1_value = List<std::pair<T1, T1>>(*(d_a1));
        const T1 &e1 = d_a0.first;
        const T1 &e2 = d_a0.second;
        std::optional<T1> f1 =
            h.find([=](const T1 x) mutable { return eqb_node(e1, x); });
        std::optional<T1> f2 =
            h.find([=](const T1 x) mutable { return eqb_node(e2, x); });
        if (f1.has_value()) {
          const T1 &_x = *f1;
          if (f2.has_value()) {
            const T1 &_x0 = *f2;
            return get_elems_aux(d_a1_value, std::move(h));
          } else {
            return get_elems_aux(d_a1_value, List<T1>::cons(e2, std::move(h)));
          }
        } else {
          if (f2.has_value()) {
            const T1 &_x = *f2;
            return get_elems_aux(d_a1_value, List<T1>::cons(e1, std::move(h)));
          } else {
            if (eqb_node(e1, e2)) {
              return get_elems_aux(d_a1_value,
                                   List<T1>::cons(e1, std::move(h)));
            } else {
              return get_elems_aux(
                  d_a1_value,
                  List<T1>::cons(e1, List<T1>::cons(e2, std::move(h))));
            }
          }
        }
      }
    };
    return get_elems_aux(l, List<T1>::nil());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static entry<T1> make_entry(F0 &&eqb_node, const List<std::pair<T1, T1>> &l,
                              const T1 e) {
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

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static graph<T1> make_graph(F0 &&eqb_node, List<std::pair<T1, T1>> l) {
    List<T1> elems = get_elems<T1>(eqb_node, l);
    return std::move(elems).template fold_right<List<entry<T1>>>(
        [=](const T1 e, List<std::pair<T1, List<T1>>> ret) mutable {
          return List<std::pair<T1, List<T1>>>::cons(
              make_entry<T1>(eqb_node, l, e), ret);
        },
        List<std::pair<T1, List<T1>>>::nil());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static List<T1> graph_lookup(F0 &&eqb_node, const T1 elem,
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

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static bool contains(F0 &&eqb_node, const T1 elem, const List<T1> &es) {
    auto _cs = es.find([=](const T1 x) mutable { return eqb_node(elem, x); });
    if (_cs.has_value()) {
      const T1 &_x = *_cs;
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static T1
  cycle_entry_aux(F0 &&eqb_node, const List<std::pair<T1, List<T1>>> &graph0,
                  List<T1> seens, const T1 elem, const unsigned int &counter) {
    if (contains<T1>(eqb_node, elem, seens)) {
      return elem;
    } else {
      if (counter <= 0) {
        return elem;
      } else {
        unsigned int c = counter - 1;
        List<T1> l = graph_lookup<T1>(eqb_node, elem, graph0);
        if (std::holds_alternative<typename List<T1>::Nil>(l.v_mut())) {
          return elem;
        } else {
          auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v_mut());
          return cycle_entry_aux<T1>(eqb_node, graph0,
                                     List<T1>::cons(elem, std::move(seens)),
                                     d_a0, c);
        }
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static std::optional<T1>
  cycle_entry(F0 &&eqb_node, const List<std::pair<T1, List<T1>>> &graph0) {
    if (std::holds_alternative<typename List<std::pair<T1, List<T1>>>::Nil>(
            graph0.v())) {
      return std::optional<T1>();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<T1, List<T1>>>::Cons>(graph0.v());
      const T1 &e = std::pair<T1, List<T1>>(d_a0).first;
      const List<T1> &_x0 = std::pair<T1, List<T1>>(d_a0).second;
      return std::make_optional<T1>(cycle_entry_aux<T1>(
          eqb_node, graph0, List<T1>::nil(), e, graph0.length()));
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static List<T1>
  cycle_extract_aux(F0 &&eqb_node, List<std::pair<T1, List<T1>>> graph0,
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
                List<T1>::cons(elem, std::move(cycl)));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
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

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static order<T1>
  topological_sort_aux(F0 &&eqb_node,
                       const List<std::pair<T1, List<T1>>> &graph0,
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
                      entry0.second.filter([=](const T1 e) mutable {
                        return !(contains<T1>(eqb_node, e, mins_));
                      }));
                });
        return List<List<T1>>::cons(
            std::move(mins_),
            topological_sort_aux<T1>(eqb_node, std::move(rest_), c));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static List<List<T1>> topological_sort(F0 &&eqb_node,
                                         const List<std::pair<T1, T1>> &g) {
    List<std::pair<T1, List<T1>>> g_ = make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_.length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static order<T1>
  topological_sort_graph(F0 &&eqb_node,
                         const List<std::pair<T1, List<T1>>> &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0.length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  static List<std::pair<T1, unsigned int>>
  topological_rank_list(F0 &&eqb_node,
                        const List<std::pair<T1, List<T1>>> &graph0) {
    List<List<T1>> lorder = topological_sort_graph<T1>(eqb_node, graph0);
    return lorder
        .template combine<unsigned int>(ListDef::seq(0u, lorder.length()))
        .template map<List<std::pair<T1, unsigned int>>>(
            [](const std::pair<List<T1>, unsigned int> &x) {
              const List<T1> &fs = x.first;
              const unsigned int &rk = x.second;
              return fs.template map<std::pair<T1, unsigned int>>(
                  [=](const T1 f) mutable { return std::make_pair(f, rk); });
            })
        .template concat<std::pair<T1, unsigned int>>();
  }
};

#endif // INCLUDED_TOPOLOGICAL_SORT
