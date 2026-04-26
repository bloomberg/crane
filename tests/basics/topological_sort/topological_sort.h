#ifndef INCLUDED_TOPOLOGICAL_SORT
#define INCLUDED_TOPOLOGICAL_SORT

#include <functional>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_shared_ptr : std::false_type {};

template <typename T>
struct is_shared_ptr<std::shared_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> struct is_optional : std::false_type {};

template <typename T> struct is_optional<std::optional<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  return x ? std::make_unique<T>(x->clone()) : nullptr;
}

template <typename T>
std::shared_ptr<T> clone_value(const std::shared_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_shared<T>(x->clone()) : nullptr;
  } else {
    return x;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using TargetBare = std::remove_cvref_t<Target>;
  using SourceBare = std::remove_cvref_t<Source>;
  if constexpr (is_unique_ptr<TargetBare>::value) {
    using Inner = typename is_unique_ptr<TargetBare>::element_type;
    if constexpr (is_unique_ptr<SourceBare>::value) {
      using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires {
                             typename Inner::crane_element_type;
                             x->template clone_as<
                                 typename Inner::crane_element_type>();
                           }) {
        return std::make_unique<Inner>(
            x->template clone_as<typename Inner::crane_element_type>());
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_unique<Inner>(x->clone());
      }
    } else {
      if constexpr (requires { x.clone(); }) {
        return std::make_unique<Inner>(x.clone());
      } else if constexpr (std::is_same_v<Inner, SourceBare>) {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_unique<Inner>(x.template clone_as<Inner>());
      } else {
        if constexpr (requires { x.clone(); }) {
          return std::make_unique<Inner>(x.clone());
        } else {
          return std::make_unique<Inner>(x);
        }
      }
    }
  } else if constexpr (is_optional<TargetBare>::value) {
    using Inner = typename is_optional<TargetBare>::element_type;
    if constexpr (is_optional<SourceBare>::value) {
      if (!x)
        return std::nullopt;
      return Target{clone_as_value<Inner>(*x)};
    } else {
      return Target{clone_as_value<Inner>(x)};
    }
  } else if constexpr (is_shared_ptr<TargetBare>::value) {
    using Inner = typename is_shared_ptr<TargetBare>::element_type;
    if constexpr (is_shared_ptr<SourceBare>::value) {
      using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
      if (!x)
        return nullptr;
      if constexpr (std::is_same_v<Inner, SourceInner>) {
        return clone_value(x);
      } else if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else if constexpr (is_unique_ptr<SourceBare>::value) {
      if (!x)
        return nullptr;
      if constexpr (requires { x->template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x->template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x->clone());
      }
    } else {
      if constexpr (std::is_same_v<Inner, SourceBare>) {
        return std::make_shared<Inner>(x.clone());
      } else if constexpr (requires { x.template clone_as<Inner>(); }) {
        return std::make_shared<Inner>(x.template clone_as<Inner>());
      } else {
        return std::make_shared<Inner>(x.clone());
      }
    }
  } else if constexpr (std::is_same_v<TargetBare, SourceBare>) {
    return clone_value(x);
  } else if constexpr (is_unique_ptr<SourceBare>::value) {
    using SourceInner = typename is_unique_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      if (!x)
        return Target{};
      if constexpr (requires { x->clone(); }) {
        return x->clone();
      } else {
        return *x;
      }
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else if constexpr (requires { x->clone(); }) {
      return x->clone();
    } else {
      return Target(*x);
    }
  } else if constexpr (is_shared_ptr<SourceBare>::value) {
    using SourceInner = typename is_shared_ptr<SourceBare>::element_type;
    if constexpr (std::is_same_v<TargetBare, SourceInner>) {
      return x ? x->clone() : Target{};
    } else if constexpr (requires { x->template clone_as<TargetBare>(); }) {
      return x->template clone_as<TargetBare>();
    } else {
      return Target(*x);
    }
  } else if constexpr (requires {
                         typename TargetBare::crane_element_type;
                         x.template clone_as<
                             typename TargetBare::crane_element_type>();
                       }) {
    return x.template clone_as<typename TargetBare::crane_element_type>();
  } else if constexpr (requires { x.template clone_as<TargetBare>(); }) {
    return x.template clone_as<TargetBare>();
  } else {
    return Target(x);
  }
}

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

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

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<t_A>(Cons{clone_as_value<t_A>(d_a0),
                            clone_as_value<std::unique_ptr<List<t_A>>>(d_a1)});
    }
  }

  template <typename _CloneT0>
  __attribute__((pure)) List<_CloneT0> clone_as() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<_CloneT0>(typename List<_CloneT0>::Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      return List<_CloneT0>(typename List<_CloneT0>::Cons{
          clone_as_value<_CloneT0>(d_a0),
          clone_as_value<std::unique_ptr<List<_CloneT0>>>(d_a1)});
    }
  }

  // CREATORS
  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1.clone())});
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
  __attribute__((pure)) List<std::pair<t_A, T1>>
  combine(const List<T1> &l_) const {
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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) std::optional<t_A> find(F0 &&f) const {
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

  template <MapsTo<bool, t_A> F0>
  __attribute__((pure)) List<t_A> filter(F0 &&f) const {
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

  template <typename T1> __attribute__((pure)) List<T1> concat() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<List<T1>>::Cons>(_sv.v());
      return clone_as_value<List<T1>>(d_a0).app(
          (*(d_a1)).template concat<T1>());
    }
  }

  template <typename T1, MapsTo<T1, t_A> F0>
  __attribute__((pure)) List<T1> map(F0 &&f) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return List<T1>::nil();
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<T1>::cons(f(d_a0), (*(d_a1)).template map<T1>(f));
    }
  }

  __attribute__((pure)) unsigned int length() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return ((*(d_a1)).length() + 1);
    }
  }

  __attribute__((pure)) List<t_A> app(List<t_A> m) const {
    auto &&_sv = *(this);
    if (std::holds_alternative<typename List<t_A>::Nil>(_sv.v())) {
      return m;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<t_A>::Cons>(_sv.v());
      return List<t_A>::cons(d_a0, (*(d_a1)).app(m));
    }
  }
};

struct ListDef {
  __attribute__((pure)) static List<unsigned int> seq(unsigned int start,
                                                      const unsigned int &len);
};

struct ToString {
  template <typename T1, typename T2, MapsTo<std::string, T1> F0,
            MapsTo<std::string, T2> F1>
  __attribute__((pure)) static std::string
  pair_to_string(F0 &&p1, F1 &&p2, const std::pair<T1, T2> &x) {
    const T1 &a = x.first;
    const T2 &b = x.second;
    return "("s + p1(a) + ", "s + p2(b) + ")"s;
  }

  template <typename T1, MapsTo<std::string, T1> F0>
  __attribute__((pure)) static std::string
  intersperse(F0 &&p, const std::string sep, const List<T1> &l) {
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
  __attribute__((pure)) static std::string list_to_string(F0 &&p,
                                                          const List<T1> &l) {
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
  __attribute__((pure)) static List<T1>
  get_elems(F0 &&eqb_node, const List<std::pair<T1, T1>> &l) {
    std::function<List<T1>(List<std::pair<T1, T1>>, List<T1>)> get_elems_aux;
    get_elems_aux = [&](List<std::pair<T1, T1>> l0, List<T1> h) -> List<T1> {
      if (std::holds_alternative<typename List<std::pair<T1, T1>>::Nil>(
              l0.v())) {
        return h;
      } else {
        const auto &[d_a0, d_a1] =
            std::get<typename List<std::pair<T1, T1>>::Cons>(l0.v());
        List<std::pair<T1, T1>> d_a1_value =
            clone_as_value<List<std::pair<T1, T1>>>(d_a1);
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
            return get_elems_aux(d_a1_value, h);
          } else {
            return get_elems_aux(d_a1_value, List<T1>::cons(e2, h));
          }
        } else {
          if (f2.has_value()) {
            const T1 &_x = *f2;
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
  make_entry(F0 &&eqb_node, const List<std::pair<T1, T1>> &l, const T1 e) {
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
  __attribute__((pure)) static graph<T1> make_graph(F0 &&eqb_node,
                                                    List<std::pair<T1, T1>> l) {
    List<T1> elems = get_elems<T1>(eqb_node, l);
    return elems.template fold_right<List<entry<T1>>>(
        [=](const T1 e, List<std::pair<T1, List<T1>>> ret) mutable {
          return List<std::pair<T1, List<T1>>>::cons(
              make_entry<T1>(eqb_node, l, e), ret);
        },
        List<std::pair<T1, List<T1>>>::nil());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
  graph_lookup(F0 &&eqb_node, const T1 elem,
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
  __attribute__((pure)) static bool contains(F0 &&eqb_node, const T1 elem,
                                             const List<T1> &es) {
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
        if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
          return elem;
        } else {
          const auto &[d_a0, d_a1] = std::get<typename List<T1>::Cons>(l.v());
          return cycle_entry_aux<T1>(eqb_node, graph0,
                                     List<T1>::cons(elem, seens), d_a0, c);
        }
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static std::optional<T1>
  cycle_entry(F0 &&eqb_node, const List<std::pair<T1, List<T1>>> &graph0) {
    if (std::holds_alternative<typename List<std::pair<T1, List<T1>>>::Nil>(
            graph0.v())) {
      return std::optional<T1>();
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::pair<T1, List<T1>>>::Cons>(graph0.v());
      const T1 &e = clone_as_value<std::pair<T1, List<T1>>>(d_a0).first;
      const List<T1> &_x0 =
          clone_as_value<std::pair<T1, List<T1>>>(d_a0).second;
      return std::make_optional<T1>(cycle_entry_aux<T1>(
          eqb_node, graph0, List<T1>::nil(), e, graph0.length()));
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
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
                List<T1>::cons(elem, cycl));
      }
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<T1>
  cycle_extract(F0 &&eqb_node, const List<std::pair<T1, List<T1>>> &graph0) {
    auto _cs = cycle_entry<T1>(eqb_node, graph0);
    if (_cs.has_value()) {
      const T1 &elem = *_cs;
      return cycle_extract_aux<T1>(eqb_node, graph0, graph0.length(), elem,
                                   List<T1>::nil());
    } else {
      return List<T1>::nil();
    }
  }

  template <typename T1>
  __attribute__((pure)) static bool null(const List<T1> &xs) {
    if (std::holds_alternative<typename List<T1>::Nil>(xs.v())) {
      return true;
    } else {
      return false;
    }
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static order<T1>
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
            rest.template map<std::pair<T1, List<T1>>>(
                [=](const std::pair<T1, List<T1>> &entry0) mutable {
                  return std::make_pair(
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
  topological_sort(F0 &&eqb_node, const List<std::pair<T1, T1>> &g) {
    List<std::pair<T1, List<T1>>> g_ = make_graph<T1>(eqb_node, g);
    return topological_sort_aux<T1>(eqb_node, g_, g_.length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static order<T1>
  topological_sort_graph(F0 &&eqb_node,
                         const List<std::pair<T1, List<T1>>> &graph0) {
    return topological_sort_aux<T1>(eqb_node, graph0, graph0.length());
  }

  template <typename T1, MapsTo<bool, T1, T1> F0>
  __attribute__((pure)) static List<std::pair<T1, unsigned int>>
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
