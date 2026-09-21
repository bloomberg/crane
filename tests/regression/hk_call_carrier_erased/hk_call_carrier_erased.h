#ifndef INCLUDED_HK_CALL_CARRIER_ERASED
#define INCLUDED_HK_CALL_CARRIER_ERASED

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
template <typename T> struct box;
template <typename T, typename Body> struct outer;

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
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }
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
template <template <typename> class t>
using TFunctor =
    std::function<t<std::any>(std::function<std::any(std::any)>, t<std::any>)>;

template <template <typename> class T1, typename T2, typename F1,
          typename T3 = std::invoke_result_t<F1 &, T2 &>>
T1<T3> tfmap(std::type_identity_t<TFunctor<T1>> tFunctor, F1 &&f, T1<T2> x) {
  return crane_container_cast<T1<T3>>(
      tFunctor(crane_erase_fn(f), std::move(x)));
}

List<std::any> TFunctor_list(std::function<std::any(std::any)> x0_,
                             const List<std::any> &x1_);

template <template <typename> class T1, typename F1>
List<T1<std::any>> TFunctor_list_(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
                                  List<T1<std::any>> x0_) {
  return std::move(x0_).template map<std::any>(
      [=]<typename T2>(T1<T2> _x0) mutable -> T1<std::any> {
        return tfmap<T1, std::any>(h, f, _x0);
      });
}

template <typename T> struct box {
  T b_payload;

  // ACCESSORS
  template <typename _U> operator box<_U>() const {
    return {[&]() -> _U {
      if constexpr (std::is_same_v<T, std::any>) {
        return crane_any_cast<_U>(b_payload);
      } else {
        if constexpr (std::is_constructible_v<_U, const T &>) {
          return _U(b_payload);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }
    }()};
  }
};

box<std::any> TFunctor_box(std::function<std::any(std::any)> f,
                           const box<std::any> &b);

template <typename T, typename Body> struct outer {
  List<box<T>> o_boxes;
  Body o_body;

  // ACCESSORS
  template <typename _U0, typename _U1> operator outer<_U0, _U1>() const {
    return {List<box<_U0>>(o_boxes), [&]() -> _U1 {
              if constexpr (std::is_same_v<Body, std::any>) {
                return crane_any_cast<_U1>(o_body);
              } else {
                if constexpr (std::is_constructible_v<_U1, const Body &>) {
                  return _U1(o_body);
                } else {
                  throw std::logic_error("unreachable: inactive constructor "
                                         "field at this instantiation");
                }
              }
            }()};
  }
};

template <template <typename> class T1, typename F1>
outer<std::any, T1<std::any>>
TFunctor_outer(std::type_identity_t<TFunctor<T1>> h, F1 &&f,
               const outer<std::any, T1<std::any>> &m) {
  return outer<std::any, T1<std::any>>{
      tfmap<List>(
          []() {
            return [](std::function<std::any(std::any)> _x0,
                      List<std::any> _x1) -> List<std::any> {
              return TFunctor_list_<box>(
                  [](auto &&_ec0, box<std::any> _ec1) {
                    return TFunctor_box(_ec0, _ec1);
                  },
                  _x0, _x1);
            };
          }(),
          f, m.o_boxes),
      tfmap<T1, std::any>(std::move(h), f, m.o_body)};
}

struct HkCallCarrierErased {
  static Nat bump(Nat n);
  static List<box<Nat>> on_boxes(const List<box<Nat>> &l);
  static outer<Nat, List<Nat>> on_outer(const outer<Nat, List<Nat>> &m);
};

#endif // INCLUDED_HK_CALL_CARRIER_ERASED
