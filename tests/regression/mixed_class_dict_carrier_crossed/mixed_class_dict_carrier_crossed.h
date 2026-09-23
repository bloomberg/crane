#ifndef INCLUDED_MIXED_CLASS_DICT_CARRIER_CROSSED
#define INCLUDED_MIXED_CLASS_DICT_CARRIER_CROSSED

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename t> struct Exp;
template <typename t> struct Decl;
template <typename t> struct modu;

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

/// Reduced from Vellvm's TFunctor_modul (rocq/Syntax/Traversal.v:859).
///
/// Three adjacent tfmap calls in one instance body came out with each
/// other's carriers -- m_globals and m_declarations both got the carrier
/// of a sibling Endo dictionary, and m_definitions got m_globals's. The
/// distinguishing feature of that context is that the dictionary list is
/// {e mixed-class}: a non-higher-kinded Endo parameter sits between the
/// higher-kinded TFunctor ones. Every context the carrier recovery had been
/// exercised on before was pure TFunctor.
///
/// dict_carrier_type_args finds the class parameter by scanning the
/// callee's domains for the first one whose argument is a Tapp -- a carrier
/// of arrow kind -- and then takes the {e argument} at that position. A
/// dictionary whose class parameter is an ordinary type has the same outer
/// shape and a non-Tapp argument, so whether it is counted decides whether
/// every later position is off by one.
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

template <typename t> struct Decl {
  // DATA
  t a0;

  // ACCESSORS
  Decl<t> clone() const { return {a0}; }

  template <typename _U> operator Decl<_U>() const {
    return {[&]() -> _U {
      if constexpr (crane_convertible<_U, const t &>) {
        return crane_convert<_U>(a0);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Decl<t> d_mk(t a0) { return {std::move(a0)}; }

  template <typename F0> Decl<std::any> TFunctor_decl(F0 &&f) const {
    const auto &[a0] = *this;
    return Decl<std::any>::d_mk(crane_call_erased(f, a0));
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

/// Not higher-kinded: its parameter is an ordinary type, so it has no carrier
/// at all. This is the entry that sits between the two that do.
template <typename t> using Endo = std::function<t(t)>;

template <typename T1> T1 endo(Endo<T1> endo0, T1 x0_) {
  return endo0(std::move(x0_));
}

template <template <typename> class T1, typename F1>
List<T1<std::any>> TFunctor_list(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                                 const List<T1<std::any>> &l) {
  return l.template map<std::any>(
      [=]<typename T2>(T1<T2> _x0) mutable -> T1<std::any> {
        return tfmap<T1, std::any>(h, f, _x0);
      });
}

const Endo<Nat> Endo_nat = [](Nat n) { return n; };

template <typename t> struct modu {
  Nat m_tag;
  List<Exp<t>> m_exps;
  List<Decl<t>> m_decls;

  // ACCESSORS
  template <typename _U> operator modu<_U>() const {
    return {m_tag, crane_convert<List<Exp<_U>>>(m_exps),
            crane_convert<List<Decl<_U>>>(m_decls)};
  }
};

modu<std::any> TFunctor_modu(std::type_identity_t<TFunctor<Exp>> h,
                             Endo<Nat> h0,
                             std::type_identity_t<TFunctor<Decl>> h1,
                             std::function<std::any(std::any)> f,
                             const modu<std::any> &m);

template <typename F0>
  requires std::is_invocable_r_v<bool, F0 &, Nat &>
modu<bool> use_modu(F0 &&f, const modu<Nat> &m) {
  return tfmap<modu>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  modu<std::any> _x1) -> modu<std::any> {
          return TFunctor_modu(
              [](auto &&_ec0, Exp<std::any> _ec1) {
                return _ec1.TFunctor_exp(_ec0);
              },
              Endo_nat,
              [](auto &&_ec0, Decl<std::any> _ec1) {
                return _ec1.TFunctor_decl(_ec0);
              },
              _x0, _x1);
        };
      }(),
      f, m);
}

#endif // INCLUDED_MIXED_CLASS_DICT_CARRIER_CROSSED
