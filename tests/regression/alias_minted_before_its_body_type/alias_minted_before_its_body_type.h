#ifndef INCLUDED_ALIAS_MINTED_BEFORE_ITS_BODY_TYPE
#define INCLUDED_ALIAS_MINTED_BEFORE_ITS_BODY_TYPE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename t> struct Exp;

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
    auto _next = [&](variant_t &_v) -> std::shared_ptr<Nat> {
      if (auto *_alt = std::get_if<S>(&_v)) {
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a0);
        }
      }
      return nullptr;
    };
    std::shared_ptr<Nat> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
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
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
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

/// A synthesised carrier alias whose body names a type defined later.
///
/// Alias templates were collected into the file's prologue, immediately after
/// the forward struct declarations. That is sound for a body naming top-level
/// class templates, which can be forward-declared. boxed is emitted as an
/// {e alias template}, and C++ has no syntax for forward-declaring one, so
/// there was nothing the prologue could have declared:
///
/// template <typename _CraneTcArg>
/// using _crane_carrier_tc_... = List<boxed<_CraneTcArg>>;   // early
/// ...
/// template <typename t> using boxed = std::pair<Nat, Exp<t>>;
///
/// boxed is deliberately not higher-kinded. A Set -> Set parameter is
/// emitted as a plain typename against a use that wants
/// template <typename> class, which is a separate live defect; a test that
/// fails for two unrelated reasons cannot say which one a change broke.
///
/// Reduced by the Vellvm session from that development's four errors of this
/// shape. The obstruction there is a {e nested member template} rather than an
/// alias template -- List::list, a member of the struct a module became --
/// which cannot be forward-declared for a different reason. So this test
/// exercises the argument the fix rests on, that an alias placed in front of
/// the element that minted it is after everything that element names, and not
/// the particular form of the obstruction.
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

  template <typename _U>
  Exp(const Exp<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Exp<_U>::E_leaf>(_other.v())) {
            const auto &[a0] = std::get<typename Exp<_U>::E_leaf>(_other.v());
            return E_leaf{[&]() -> t {
              if constexpr (crane_convertible<t, const _U &>) {
                return crane_convert<t>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0, a1] =
                std::get<typename Exp<_U>::E_node>(_other.v());
            return E_node{
                (a0 ? std::make_shared<Exp<t>>(crane_convert<Exp<t>>(*a0))
                    : nullptr),
                (a1 ? std::make_shared<Exp<t>>(crane_convert<Exp<t>>(*a1))
                    : nullptr)};
          }
        }()) {}

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
        if (_alt->a0 && _alt->a0.use_count() == 1) {
          _stack.push_back(std::move(_alt->a0));
        }
        if (_alt->a1 && _alt->a1.use_count() == 1) {
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

    /// _Cont_E_node: saves [a1], resumes after recursive call, then processes
    /// rest.
    struct _Cont_E_node {
      std::shared_ptr<Exp<t>> a1;
    };

    /// _Cont_E_node_1: saves [_tmp2], resumes after recursive call, then
    /// processes rest.
    struct _Cont_E_node_1 {
      Exp<T1> _tmp2;
    };

    using _Frame = std::variant<_Enter, _Cont_E_node, _Cont_E_node_1>;
    Exp<T1> _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified exp_map: _Enter -> _Cont_E_node -> _Cont_E_node_1.
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
          _stack.emplace_back(_Cont_E_node{a1});
          _stack.emplace_back(_Enter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<_Cont_E_node>(_frame)) {
        auto _f = std::move(std::get<_Cont_E_node>(_frame));
        std::shared_ptr<Exp<t>> a1 = std::move(_f.a1);
        _stack.emplace_back(_Cont_E_node_1{std::move(_result)});
        _stack.emplace_back(_Enter{crane_raw(a1)});
      } else {
        auto _f = std::move(std::get<_Cont_E_node_1>(_frame));
        _result = Exp<T1>::e_node(std::move(_f._tmp2), std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0> Exp<crane::obj> TFunctor_exp(F0 &&x0_) const {
    return this->template exp_map<crane::obj>(x0_);
  }
};

template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&x, crane::rebind_t<T1, T2> x0) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1>(std::move(x0))));
}

template <typename t> using boxed = std::pair<Nat, Exp<t>>;

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
boxed<T2> bump(F0 &&f, std::pair<Nat, Exp<T1>> p) {
  auto [n, e] = std::move(p);
  return std::make_pair(std::move(n),
                        tfmap<Exp<crane::obj>, T1, T2>(
                            [](auto &&_ec0, Exp<crane::obj> _ec1) {
                              return _ec1.TFunctor_exp(_ec0);
                            },
                            f, std::move(e)));
}

List<boxed<crane::obj>>
TFunctor_boxedlist(crane::fn<crane::obj(crane::obj)> f,
                   const List<std::pair<Nat, Exp<crane::obj>>> &l);

template <typename F0>
  requires std::is_invocable_r_v<bool, F0 &, Nat &>
List<boxed<bool>> use_boxedlist(F0 &&f,
                                const List<std::pair<Nat, Exp<Nat>>> &l) {
  return tfmap<List<boxed<crane::obj>>, Nat, bool>(
      [](auto &&_ec0, List<boxed<crane::obj>> _ec1) {
        return TFunctor_boxedlist(_ec0, _ec1);
      },
      f, l);
}

#endif // INCLUDED_ALIAS_MINTED_BEFORE_ITS_BODY_TYPE
