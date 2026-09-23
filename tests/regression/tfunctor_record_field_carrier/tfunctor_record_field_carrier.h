#ifndef INCLUDED_TFUNCTOR_RECORD_FIELD_CARRIER
#define INCLUDED_TFUNCTOR_RECORD_FIELD_CARRIER

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename t> struct Exp;
template <typename t> struct glob;

struct Nat {
  // TYPES
  struct O {};

  struct S {
    std::shared_ptr<Nat> a0;
  };

  using variant_t = std::variant<O, S>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Nat() {}

  explicit Nat(O _v) : v_(_v) {}

  explicit Nat(S _v) : v_(std::move(_v)) {}

  static Nat o() { return Nat(O{}); }

  static Nat s(Nat a0) { return Nat(S{std::make_shared<Nat>(std::move(a0))}); }

  // MANIPULATORS
  ~Nat() {
    crane::small_vector<std::shared_ptr<Nat>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
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

  Nat(const Nat &) = default;
  Nat &operator=(const Nat &) = default;
  Nat(Nat &&) noexcept = default;
  Nat &operator=(Nat &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

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
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (crane_convertible<A, const _U &>) {
                   return crane_convert<A>(a);
                 } else {
                   throw std::logic_error("unreachable: inactive constructor "
                                          "field at this instantiation");
                 }
               }(),
               (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                  : nullptr)};
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
};

/// A higher-kinded class whose carrier is a {e composition} -- fun t =>
/// option (Exp t) -- is recovered correctly at a top-level call, where the
/// emitter writes the synthesised alias:
///
/// Tv::template tfmap<_crane_carrier_tc>(...)   // option (Exp t)
///
/// but the same carrier reached through a {e record field}, in the traversal
/// Crane generates for the record, is written as the bare head:
///
/// Tv::template tfmap<std::optional>(...)       // WRONG
///
/// TFunctor<std::optional> wants std::optional<std::any>, while the
/// adapter lambda emitted beside it takes std::optional<Exp<std::any>>:
///
/// error: no matching function for call to 'tfmap'
/// note: no known conversion from '(lambda ...)' to
/// 'std::type_identity_t<TFunctor<std::optional>>' (aka
/// 'std::function<std::optional<std::any>(..., std::optional<std::any>)>')
///
/// The g_anns : list (Exp t) field is the control: it takes the same wrong
/// path and is emitted as the bare tfmap<List>, but it compiles, because
/// List is Crane's own type and its element-wise converting constructor
/// absorbs the mismatch. Ownership of the carrier decides whether the defect
/// is visible, not whether it is present -- so a repair that special-cases
/// std-mapped carriers would silence the error and leave the wrong carrier at
/// every Crane-owned field.
///
/// TFunctor must stay a single-method class: a braces-and-fields class is
/// emitted as a concept with a member carrier alias, which spells every
/// carrier and reproduces nothing. Nothing here is inside a Module, because
/// the synthesised alias is emitted at namespace scope while its body names
/// Exp from inside the module -- a second, unrelated defect that would be
/// reported by the same test.
template <typename t> struct Exp {
  // TYPES
  struct E_leaf {
    t a0;
  };

  struct E_node {
    std::shared_ptr<Exp<t>> a0;
    std::shared_ptr<Exp<t>> a1;
  };

  using variant_t = std::variant<E_leaf, E_node>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Exp() {}

  explicit Exp(E_leaf _v) : v_(std::move(_v)) {}

  explicit Exp(E_node _v) : v_(std::move(_v)) {}

  template <typename _U> Exp(const Exp<_U> &_other) {
    if (std::holds_alternative<typename Exp<_U>::E_leaf>(_other.v())) {
      const auto &[a0] = std::get<typename Exp<_U>::E_leaf>(_other.v());
      this->v_ = E_leaf{[&]() -> t {
        if constexpr (crane_convertible<t, const _U &>) {
          return crane_convert<t>(a0);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    } else {
      const auto &[a0, a1] = std::get<typename Exp<_U>::E_node>(_other.v());
      this->v_ = E_node{
          (a0 ? std::make_shared<Exp<t>>(crane_convert<Exp<t>>(*a0)) : nullptr),
          (a1 ? std::make_shared<Exp<t>>(crane_convert<Exp<t>>(*a1))
              : nullptr)};
    }
  }

  static Exp<t> e_leaf(t a0) { return Exp<t>(E_leaf{std::move(a0)}); }

  static Exp<t> e_node(Exp<t> a0, Exp<t> a1) {
    return Exp<t>(E_node{std::make_shared<Exp<t>>(std::move(a0)),
                         std::make_shared<Exp<t>>(std::move(a1))});
  }

  // MANIPULATORS
  ~Exp() {
    crane::small_vector<std::shared_ptr<Exp<t>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<E_node>(&_v)) {
        if (_alt->a0) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1) {
          _stack.push_back(std::move(_alt->a1));
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

  Exp(const Exp &) = default;
  Exp &operator=(const Exp &) = default;
  Exp(Exp &&) noexcept = default;
  Exp &operator=(Exp &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, t &>
  Exp<T1> exp_map(F0 &&f) const {
    const Exp<t> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const Exp<t> *_self;
    };

    /// _After_E_node: saves [a0], dispatches next recursive call.
    struct _After_E_node {
      Exp<t> *a0;
    };

    /// _Combine_E_node: receives partial results, combines with _result from
    /// final call.
    struct _Combine_E_node {
      Exp<T1> _result;
    };

    using _Frame = std::variant<_Enter, _After_E_node, _Combine_E_node>;
    Exp<T1> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified exp_map: _Enter -> _After_E_node -> _Combine_E_node.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const Exp<t> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Exp<t>::E_leaf>(_sv.v())) {
          const auto &[a0] = std::get<typename Exp<t>::E_leaf>(_sv.v());
          _result = Exp<T1>::e_leaf(f(a0));
        } else {
          const auto &[a0, a1] = std::get<typename Exp<t>::E_node>(_sv.v());
          _stack.emplace_back(_After_E_node{crane_raw(a0)});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else if (std::holds_alternative<_After_E_node>(_frame)) {
        auto _f = std::move(std::get<_After_E_node>(_frame));
        _stack.emplace_back(_Combine_E_node{std::move(_result)});
        _stack.emplace_back(_Enter{_f.a0});
      } else {
        auto _f = std::move(std::get<_Combine_E_node>(_frame));
        _result = Exp<T1>::e_node(std::move(_result), std::move(_f._result));
      }
    }
    return _result;
  }

  template <typename F0> Exp<std::any> TFunctor_exp(F0 &&x0_) const {
    return this->template exp_map<std::any>(x0_);
  }
};
template <template <typename> class t>
using TFunctor =
    std::function<t<std::any>(std::function<std::any(std::any)>, t<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&x, T1<T2> x0) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1<std::any>>(std::move(x0))));
}

template <template <typename> class T1, typename F1>
std::optional<T1<std::any>>
TFunctor_option(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                const std::optional<T1<std::any>> &o) {
  if (o.has_value()) {
    const auto &x = *o;
    return std::make_optional<T1<std::any>>(tfmap<T1, std::any>(h, f, x));
  } else {
    return std::optional<T1<std::any>>();
  }
}

template <template <typename> class T1, typename F1>
List<T1<std::any>> TFunctor_list(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                                 const List<T1<std::any>> &l) {
  return l.template map<std::any>(
      [=]<typename T2>(T1<T2> _x0) mutable -> T1<std::any> {
        return tfmap<T1, std::any>(h, f, _x0);
      });
}

template <typename t> struct glob {
  t g_name;
  std::optional<Exp<t>> g_exp;
  List<Exp<t>> g_anns;

  // ACCESSORS
  template <typename _U> operator glob<_U>() const {
    return {[&]() -> _U {
              if constexpr (crane_convertible<_U, const t &>) {
                return crane_convert<_U>(g_name);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            std::optional<Exp<_U>>(g_exp),
            crane_convert<List<Exp<_U>>>(g_anns)};
  }
};

glob<std::any> TFunctor_glob(std::function<std::any(std::any)> f,
                             const glob<std::any> &g);
template <typename _CraneTcArg>
using _crane_carrier_tc_6170063419090647 = std::optional<Exp<_CraneTcArg>>;

/// The composed carrier at a top-level argument: this one is already correct,
/// and is kept as the control that says the emitter can do it.
template <typename F0>
  requires std::is_invocable_r_v<Nat, F0 &, Nat &>
std::optional<Exp<Nat>> use_option(F0 &&f, const std::optional<Exp<Nat>> &o) {
  return tfmap<_crane_carrier_tc_6170063419090647>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  std::optional<Exp<std::any>> _x1)
                   -> std::optional<Exp<std::any>> {
          return TFunctor_option<Exp>(
              [](auto &&_ec0, Exp<std::any> _ec1) {
                return _ec1.TFunctor_exp(_ec0);
              },
              _x0, _x1);
        };
      }(),
      f, o);
}

/// The same carrier through a record field.
template <typename F0>
  requires std::is_invocable_r_v<Nat, F0 &, Nat &>
glob<Nat> use_glob(F0 &&f, const glob<Nat> &g) {
  return tfmap<glob>(
      [](auto &&_ec0, glob<std::any> _ec1) {
        return TFunctor_glob(_ec0, _ec1);
      },
      f, g);
}

#endif // INCLUDED_TFUNCTOR_RECORD_FIELD_CARRIER
