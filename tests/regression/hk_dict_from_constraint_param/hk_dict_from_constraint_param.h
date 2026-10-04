#ifndef INCLUDED_HK_DICT_FROM_CONSTRAINT_PARAM
#define INCLUDED_HK_DICT_FROM_CONSTRAINT_PARAM

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
template <typename T> struct box;
template <typename T, typename Body> struct holder;

struct HkDictFromConstraintParam {
  static holder<Nat, List<Nat>> run(const holder<Nat, List<Nat>> &m);
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
  template <typename CraneU> operator box<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const T &>) {
        return crane_convert<CraneU>(b_payload);
      } else {
        throw std::logic_error(
            "unreachable: inactive constructor field at this instantiation");
      }
    }()};
  }
};

box<crane::obj> TFunctor_box(crane::fn<crane::obj(crane::obj)> f,
                             const box<crane::obj> &b);

template <typename T, typename Body> struct holder {
  List<box<T>> h_boxes;
  Body h_body;

  // ACCESSORS
  template <typename CraneU0, typename CraneU1>
  operator holder<CraneU0, CraneU1>() const {
    return {crane_convert<List<box<CraneU0>>>(h_boxes), [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const Body &>) {
                return crane_convert<CraneU1>(h_body);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }
};

template <typename T1, typename F2>
holder<crane::obj, T1> TFunctor_holder(std::type_identity_t<TFunctor<T1>> h,
                                       TFunctor<box<crane::obj>> h0, F2 &&f,
                                       const holder<crane::obj, T1> &m) {
  return holder<crane::obj, T1>{
      tfmap<List<box<crane::obj>>, crane::obj, crane::obj>(
          [=]() {
            return [=](crane::fn<crane::obj(crane::obj)> _x0,
                       const auto &_x1) -> List<box<crane::obj>> {
              return TFunctor_list_<box<crane::obj>>(
                  h0, _x0, crane_convert<List<box<crane::obj>>>(_x1));
            };
          }(),
          f, m.h_boxes),
      tfmap<T1, crane::obj, crane::obj>(std::move(h), f, m.h_body)};
}

#endif // INCLUDED_HK_DICT_FROM_CONSTRAINT_PARAM
