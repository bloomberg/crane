#ifndef INCLUDED_TOPOLOGICAL_SORT
#define INCLUDED_TOPOLOGICAL_SORT

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

template <typename A> struct List;

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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>)
                          return crane_any_cast<A>(a);
                        else
                          return A(a);
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1>
  List<std::pair<A, T1>> combine(const List<T1> &l_) const {
    std::shared_ptr<List<std::pair<A, T1>>> _head{};
    std::shared_ptr<List<std::pair<A, T1>>> *_write = &_head;
    const List<A> *_loop_self = this;
    const List<T1> *_loop_l_ = &l_;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<std::pair<A, T1>>>(
            List<std::pair<A, T1>>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (std::holds_alternative<typename List<T1>::Nil>(_loop_l_->v())) {
          *_write = std::make_shared<List<std::pair<A, T1>>>(
              List<std::pair<A, T1>>::nil());
          break;
        } else {
          const auto &[a00, a10] =
              std::get<typename List<T1>::Cons>(_loop_l_->v());
          auto _cell = std::make_shared<List<std::pair<A, T1>>>(
              typename List<std::pair<A, T1>>::Cons(std::make_pair(a0, a00),
                                                    nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<std::pair<A, T1>>::Cons>(
                        (*_write)->v_mut())
                        .l;
          _loop_self = crane_raw(a1);
          _loop_l_ = crane_raw(a10);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  std::optional<A> find(F0 &&f) const {
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return std::optional<A>();
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          return std::make_optional<A>(a0);
        } else {
          _loop_self = crane_raw(a1);
        }
      }
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, A &>
  List<A> filter(F0 &&f) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(List<A>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell =
              std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
          *_write = std::move(_cell);
          _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_head);
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a1], resumes after recursive call with _result.
    struct _Resume_Cons {
      std::decay_t<A> a1;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    T1 _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified fold_right: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{a1});
          _stack.emplace_back(_Enter{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = f(std::move(_f.a1), std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1> List<T1> concat() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: saves [a0], resumes after recursive call with _result.
    struct _Resume_Cons {
      List<T1> a0;
    };

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    List<T1> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified concat: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<List<T1>>::Nil>(_sv.v())) {
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] =
              std::get<typename List<List<T1>>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{a0});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = std::move(_f.a0).app(std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, A &>
  List<T1> map(F0 &&f) const {
    std::shared_ptr<List<T1>> _head{};
    std::shared_ptr<List<T1>> *_write = &_head;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<T1>>(List<T1>::nil());
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<T1>>(typename List<T1>::Cons(f(a0), nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<T1>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }

  List<A> app(List<A> m) const {
    std::shared_ptr<List<A>> _head{};
    std::shared_ptr<List<A>> *_write = &_head;
    const List<A> *_loop_self = this;
    List<A> _loop_m = std::move(m);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        *_write = std::make_shared<List<A>>(std::move(_loop_m));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell =
            std::make_shared<List<A>>(typename List<A>::Cons(a0, nullptr));
        *_write = std::move(_cell);
        _write = &std::get<typename List<A>::Cons>((*_write)->v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_head);
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
    const auto &[a, b] = x;
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
        const auto &[e1, e2] = a0;
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
      const auto &[_x, es] = p;
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
      const auto &[e, _x0] = a0;
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
              const auto &[fs, rk] = x;
              return fs.template map<std::pair<T1, uint64_t>>(
                  [=](T1 f) mutable { return std::make_pair(f, rk); });
            })
        .template concat<std::pair<T1, uint64_t>>();
  }
};

#endif // INCLUDED_TOPOLOGICAL_SORT
