#ifndef INCLUDED_MIXED_CLASS_DICT_CARRIER_CROSSED
#define INCLUDED_MIXED_CLASS_DICT_CARRIER_CROSSED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
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
  Nat(Nat &&) = default;
  Nat &operator=(Nat &&) = default;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
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
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
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

  template <typename CraneU>
  Exp(const Exp<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Exp<CraneU>::E_leaf>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Exp<CraneU>::E_leaf>(_other.v());
            return E_leaf{[&]() -> t {
              if constexpr (crane_convertible<t, const CraneU &>) {
                return crane_convert<t>(a0);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
          } else {
            const auto &[a0, a1] =
                std::get<typename Exp<CraneU>::E_node>(_other.v());
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
  Exp(Exp &&) = default;
  Exp &operator=(Exp &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const t &>
  Exp<T1> exp_map(F0 &&f) const {
    const Exp<t> *_self = this;

    /// CraneEnter: captures varying parameters for each recursive call.
    struct CraneEnter {
      const Exp<t> *_self;
    };

    /// CraneCont_E_node: saves [a1], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_E_node {
      std::shared_ptr<Exp<t>> a1;
    };

    /// CraneCont_E_node_1: saves [_tmp2], resumes after recursive call, then
    /// processes rest.
    struct CraneCont_E_node_1 {
      Exp<T1> _tmp2;
    };

    using CraneFrame =
        std::variant<CraneEnter, CraneCont_E_node, CraneCont_E_node_1>;
    Exp<T1> _result{};
    crane::small_vector<CraneFrame> _stack;
    _stack.emplace_back(CraneEnter{_self});
    /// Loopified exp_map: CraneEnter -> CraneCont_E_node -> CraneCont_E_node_1.
    while (!_stack.empty()) {
      CraneFrame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<CraneEnter>(_frame)) {
        auto _f = std::move(std::get<CraneEnter>(_frame));
        const Exp<t> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename Exp<t>::E_leaf>(_sv.v())) {
          const auto &[a0] = std::get<typename Exp<t>::E_leaf>(_sv.v());
          _result = Exp<T1>::e_leaf(f(a0));
        } else {
          const auto &[a0, a1] = std::get<typename Exp<t>::E_node>(_sv.v());
          _stack.emplace_back(CraneCont_E_node{a1});
          _stack.emplace_back(CraneEnter{crane_raw(a0)});
        }
      } else if (std::holds_alternative<CraneCont_E_node>(_frame)) {
        auto _f = std::move(std::get<CraneCont_E_node>(_frame));
        std::shared_ptr<Exp<t>> a1 = std::move(_f.a1);
        _stack.emplace_back(CraneCont_E_node_1{std::move(_result)});
        _stack.emplace_back(CraneEnter{crane_raw(a1)});
      } else {
        auto _f = std::move(std::get<CraneCont_E_node_1>(_frame));
        _result = Exp<T1>::e_node(std::move(_f._tmp2), std::move(_result));
      }
    }
    return _result;
  }

  template <typename F0> Exp<crane::obj> TFunctor_exp(F0 &&x0_) const {
    return this->template exp_map<crane::obj>(x0_);
  }
};

template <typename t> struct Decl {
  // DATA
  t a0;

  // ACCESSORS
  Decl<t> clone() const { return {a0}; }

  template <typename CraneU> operator Decl<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const t &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }

  // CREATORS
  static Decl<t> d_mk(t a0) { return {std::move(a0)}; }

  template <typename F0> Decl<crane::obj> TFunctor_decl(F0 &&f) const {
    const auto &[a0] = *this;
    return Decl<crane::obj>::d_mk(crane_call_erased(f, a0));
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

/// Not higher-kinded: its parameter is an ordinary type, so it has no carrier
/// at all. This is the entry that sits between the two that do.
template <typename t> using Endo = crane::fn<t(t)>;

template <typename T1> T1 endo(std::type_identity_t<Endo<T1>> endo0, T1 x0_) {
  return endo0(std::move(x0_));
}

template <typename T1, typename F1>
List<T1> TFunctor_list(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                       const List<T1> &l) {
  return l.template map<T1>([=](T1 _x0) -> T1 {
    return tfmap<T1, crane::obj, crane::obj>(h, f, _x0);
  });
}

const Endo<Nat> Endo_nat = [](Nat n) { return n; };

template <typename t> struct modu {
  Nat m_tag;
  List<Exp<t>> m_exps;
  List<Decl<t>> m_decls;

  // ACCESSORS
  template <typename CraneU> operator modu<CraneU>() const {
    return {m_tag, crane_convert<List<Exp<CraneU>>>(m_exps),
            crane_convert<List<Decl<CraneU>>>(m_decls)};
  }
};

modu<crane::obj> TFunctor_modu(TFunctor<Exp<crane::obj>> h, Endo<Nat> h0,
                               TFunctor<Decl<crane::obj>> h1,
                               crane::fn<crane::obj(crane::obj)> f,
                               const modu<crane::obj> &m);

template <typename F0> modu<bool> use_modu(F0 &&f, const modu<Nat> &m) {
  return tfmap<modu<crane::obj>, Nat, bool>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> modu<crane::obj> {
          return TFunctor_modu(
              [](auto &&_ec0, Exp<crane::obj> _ec1) {
                return _ec1.TFunctor_exp(_ec0);
              },
              Endo_nat,
              [](auto &&_ec0, Decl<crane::obj> _ec1) {
                return _ec1.TFunctor_decl(_ec0);
              },
              _x0, crane_convert<modu<crane::obj>>(_x1));
        };
      }(),
      f, m);
}

#endif // INCLUDED_MIXED_CLASS_DICT_CARRIER_CROSSED
