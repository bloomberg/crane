#ifndef INCLUDED_ALIAS_CARRIER_UNDER_MAP_LAMBDA
#define INCLUDED_ALIAS_CARRIER_UNDER_MAP_LAMBDA

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename t> struct Exp;
template <typename t> struct Instr;

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
      : v_(crane_convert_spine(
            _other, std::shared_ptr<List<A>>(nullptr),
            [](const List<CraneU> &_cell) -> const List<CraneU> * {
              if (std::holds_alternative<typename List<CraneU>::Cons>(
                      _cell.v())) {
                return std::get<typename List<CraneU>::Cons>(_cell.v()).l.get();
              } else {
                return nullptr;
              }
            },
            [&](const List<CraneU> &_other,
                std::shared_ptr<List<A>> _below) -> variant_t {
              if (std::holds_alternative<typename List<CraneU>::Nil>(
                      _other.v())) {
                return Nil{};
              } else {
                const auto &[a, l] =
                    std::get<typename List<CraneU>::Cons>(_other.v());
                return Cons{
                    [&]() -> A {
                      if constexpr (crane_convertible<A, const CraneU &>) {
                        return crane_convert<A>(a);
                      } else {
                        throw std::logic_error(
                            "unreachable: inactive constructor field at this "
                            "instantiation");
                      }
                    }(),
                    std::move(_below)};
              }
            },
            [](auto &&_alt) {
              return std::make_shared<List<A>>(std::move(_alt));
            })) {}

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
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

/// A tfmap whose carrier is an {e alias} -- texp t := (t * Exp t) -- is
/// given a synthesised carrier alias and spelled when it appears as an
/// ordinary subterm, but {e not} when it appears inside an inline lambda
/// passed to List.map. There the emitter writes no carrier at all and hands
/// the site to deduction:
///
/// Tv::tfmap((auto&& _ec0, texp<std::any> _ec1) { ... }, f, te)
///
/// Deduction sees through texp to std::pair and deduces T1 = std::pair,
/// so the call does not match:
///
/// error: no matching function for call to 'tfmap'
///
/// Hoisting the mapped function to a named top-level definition -- changing
/// nothing else, keeping List.map, the pair, the alias carrier and the
/// destructuring binder -- makes the same body mint a carrier and compile.
/// That control is what rules out those four as the cause: the inline lambda
/// is necessary, not merely sufficient. So the defect is not "an alias carrier
/// cannot be deduced" (though it cannot); it is that the inline-lambda path
/// skips the mint the named path performs.
///
/// TFunctor must stay a single-method class: a braces-and-fields class is
/// emitted as a concept with a member carrier alias, which spells every
/// carrier and reproduces nothing. Nothing is inside a Module, because the
/// synthesised alias is emitted at namespace scope while its body would name a
/// type inside the module -- a second, unrelated defect.
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

/// An alias carrier: arity 1, body arity 2.
template <typename t> using texp = std::pair<t, Exp<t>>;
template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&x, crane::rebind_t<T1, T2> x0) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1>(std::move(x0))));
}

texp<crane::obj> TFunctor_texp(crane::fn<crane::obj(crane::obj)> f,
                               const std::pair<crane::obj, Exp<crane::obj>> &p);

template <typename t> struct Instr {
  // TYPES
  struct I_op {
    Exp<t> a0;
  };

  struct I_call {
    texp<t> a0;
    List<std::pair<texp<t>, Nat>> a1;
  };

  using variant_t = std::variant<I_op, I_call>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  Instr() {}

  explicit Instr(I_op _v) : v_(std::move(_v)) {}

  explicit Instr(I_call _v) : v_(std::move(_v)) {}

  template <typename CraneU>
  Instr(const Instr<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename Instr<CraneU>::I_op>(
                  _other.v())) {
            const auto &[a0] =
                std::get<typename Instr<CraneU>::I_op>(_other.v());
            return I_op{crane_convert<Exp<t>>(a0)};
          } else {
            const auto &[a0, a1] =
                std::get<typename Instr<CraneU>::I_call>(_other.v());
            return I_call{crane_convert<texp<t>>(a0),
                          crane_convert<List<std::pair<texp<t>, Nat>>>(a1)};
          }
        }()) {}

  static Instr<t> i_op(Exp<t> a0) { return Instr<t>(I_op{std::move(a0)}); }

  static Instr<t> i_call(texp<t> a0, List<std::pair<texp<t>, Nat>> a1) {
    return Instr<t>(I_call{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

Instr<crane::obj> TFunctor_instr(crane::fn<crane::obj(crane::obj)> f,
                                 const Instr<crane::obj> &i);

template <typename F0> Instr<bool> use_instr(F0 &&f, const Instr<Nat> &i) {
  return tfmap<Instr<crane::obj>, Nat, bool>(
      [](auto &&_ec0, Instr<crane::obj> _ec1) {
        return TFunctor_instr(_ec0, _ec1);
      },
      f, i);
}

#endif // INCLUDED_ALIAS_CARRIER_UNDER_MAP_LAMBDA
