#ifndef INCLUDED_HK_CALL_CARRIER_ERASED
#define INCLUDED_HK_CALL_CARRIER_ERASED

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename T> struct box;
template <typename T, typename Body> struct outer;

struct HkCallCarrierErased {
  static Nat bump(const Nat &n);
  static List<box<Nat>> on_boxes(const List<box<Nat>> &l);
  static outer<Nat, List<Nat>> on_outer(const outer<Nat, List<Nat>> &m);
};

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

template <typename t>
using TFunctor = crane::fn<t(crane::fn<crane::obj(crane::obj)>, t)>;

template <typename T1, typename T2, typename T3, typename F1>
crane::rebind_t<T1, T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor,
                              F1 &&f, crane::rebind_t<T1, T2> x) {
  return crane_container_cast<crane::rebind_t<T1, T3>>(
      tFunctor(crane_erase_fn(f), crane_convert<T1>(std::move(x))));
}

List<crane::obj> TFunctor_list(crane::fn<crane::obj(crane::obj)> x0_,
                               const List<crane::obj> &x1_);

template <typename T1, typename F1>
List<T1> TFunctor_list_(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                        List<T1> x0_) {
  return std::move(x0_).template map<T1>([=](T1 _x0) -> T1 {
    return tfmap<T1, crane::obj, crane::obj>(h, f, _x0);
  });
}

template <typename T> struct box {
  T b_payload;

  // ACCESSORS
  template <typename CraneU>
    requires crane_convertible<CraneU, const T &>
  operator box<CraneU>() const {
    return {crane_convert<CraneU>(b_payload)};
  }
};

box<crane::obj> TFunctor_box(crane::fn<crane::obj(crane::obj)> f,
                             const box<crane::obj> &b);

template <typename T, typename Body> struct outer {
  List<box<T>> o_boxes;
  Body o_body;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
    requires crane_convertible<CraneU1, const Body &>
  operator outer<CraneU0, CraneU1>() const {
    return {crane_convert<List<box<CraneU0>>>(o_boxes),
            crane_convert<CraneU1>(o_body)};
  }
};

template <typename T1, typename F1>
outer<crane::obj, T1> TFunctor_outer(std::type_identity_t<TFunctor<T1>> h,
                                     F1 &&f, const outer<crane::obj, T1> &m) {
  return outer<crane::obj, T1>{
      tfmap<List<box<crane::obj>>, crane::obj, crane::obj>(
          []() {
            return [](crane::fn<crane::obj(crane::obj)> _x0,
                      const auto &_x1) -> List<box<crane::obj>> {
              return TFunctor_list_<box<crane::obj>>(
                  [](auto &&_ec0, box<crane::obj> _ec1) {
                    return TFunctor_box(_ec0, _ec1);
                  },
                  _x0, crane_convert<List<box<crane::obj>>>(_x1));
            };
          }(),
          f, m.o_boxes),
      tfmap<T1, crane::obj, crane::obj>(std::move(h), f, m.o_body)};
}

#endif // INCLUDED_HK_CALL_CARRIER_ERASED
