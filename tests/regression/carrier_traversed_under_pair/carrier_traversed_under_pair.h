#ifndef INCLUDED_CARRIER_TRAVERSED_UNDER_PAIR
#define INCLUDED_CARRIER_TRAVERSED_UNDER_PAIR

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
template <typename t> struct blk;

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

/// A higher-kinded carrier whose traversed type sits inside a {e pair}.
///
/// dict_carrier_type_args recovers the carrier by abstracting the
/// dictionary's codomain over the type the traversal varies in, and found
/// that type by descending the {e leading} argument of each application.
/// That conflates two questions -- how far to descend, and which argument the
/// composition is applied in -- which coincide only while every constructor
/// in the chain takes one argument. A pair separates them: the descent takes
/// the first component and abstracts over option nat, giving a carrier of
/// the right shape varying in the wrong place.
///
/// Deliberately none of the three contexts that produced the neighbouring
/// carrier defects: no mixed-class dictionary list, no List.map lambda over
/// an erased binder, no dictionary reached through a class constraint. What
/// is left is the pair.
///
/// The first component is an option rather than a bare nat so the defect
/// is observable. A wrong carrier is usually latent: every Crane-owned type
/// has an element-wise converting constructor that absorbs the difference
/// through std::any. std::optional has none, so the mismatch is an
/// error rather than a silently wrong instantiation.
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
};

template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&x, crane::rebind_t<T1, T2> x0) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(x), crane_convert<T1>(std::move(x0))));
}

List<std::pair<std::optional<Nat>, Exp<crane::obj>>>
TFunctor_tagged(crane::fn<crane::obj(crane::obj)> f,
                const List<std::pair<std::optional<Nat>, Exp<crane::obj>>> &l);

template <typename t> struct blk {
  Nat b_id;
  List<std::pair<std::optional<Nat>, Exp<t>>> b_code;

  // ACCESSORS
  template <typename CraneU> operator blk<CraneU>() const {
    return {b_id,
            crane_convert<List<std::pair<std::optional<Nat>, Exp<CraneU>>>>(
                b_code)};
  }
};

blk<crane::obj> TFunctor_blk(crane::fn<crane::obj(crane::obj)> f,
                             const blk<crane::obj> &b);

template <typename F0> blk<bool> use_blk(F0 &&f, const blk<Nat> &b) {
  return tfmap<blk<crane::obj>, Nat, bool>(
      [](auto &&_ec0, blk<crane::obj> _ec1) {
        return TFunctor_blk(_ec0, _ec1);
      },
      f, b);
}

#endif // INCLUDED_CARRIER_TRAVERSED_UNDER_PAIR
