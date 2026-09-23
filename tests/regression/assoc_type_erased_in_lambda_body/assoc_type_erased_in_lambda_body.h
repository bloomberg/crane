#ifndef INCLUDED_ASSOC_TYPE_ERASED_IN_LAMBDA_BODY
#define INCLUDED_ASSOC_TYPE_ERASED_IN_LAMBDA_BODY

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <concepts>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct IPZ;
struct MonId;

struct AssocTypeErasedInLambdaBody {
  static Nat go(const Nat &_x);
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
};

template <typename
I>concept IPtr = requires {
  typename I::iptr;
} && (requires {
  { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
} || requires {
  { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
});
using iptr = std::any;

struct IPZ {
  using iptr = Nat;

  static Nat zero_iptr() { return Nat::o(); }
};

static_assert(IPtr<IPZ>);
using prov = List<Nat>;
/// Stands in for EOU_monad: the callback is handed to a {e dictionary}
/// method, not to a plain polymorphic function.  A plain one does not
/// reproduce -- see the header.
template <typename I>
concept Mon = requires {
  typename I::template m<std::any>;
  {
    I::template ret<std::any>(std::declval<std::any>())
  } -> std::convertible_to<typename I::template m<std::any>>;
  {
    I::template bind0<std::any, std::any>(
        std::declval<typename I::template m<std::any>>(),
        std::declval<
            std::function<typename I::template m<std::any>(std::any)>>())
  } -> std::convertible_to<typename I::template m<std::any>>;
};

template <Mon _tcI0, typename T2>
typename _tcI0::template m<T2> ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Mon _tcI0, typename T2, typename T3, typename F1>
  requires std::is_invocable_r_v<typename _tcI0::template m<T3>, F1 &, T2 &>
typename _tcI0::template m<T3> bind0(typename _tcI0::template m<T2> x,
                                     F1 &&x0) {
  return _tcI0::template bind0<T2, T3>(std::move(x), x0);
}

template <typename a> using Id = a;

struct MonId {
  template <typename _A0> using m = _A0;

  template <typename _A0> static _A0 ret(_A0 a) { return a; }

  template <typename _A0, typename _A1>
  static _A1 bind0(_A0 ma, std::function<_A1(_A0)> k) {
    return k(std::move(ma));
  }
};

static_assert(Mon<MonId>);
template <typename I>
concept PTR = requires {
  typename I::ptr;
  {
    I::int_to_ptr(std::declval<Nat>(), std::declval<prov>())
  } -> std::convertible_to<Id<typename I::ptr>>;
  { I::ptr_tag() } -> std::convertible_to<Nat>;
};

template <IPtr _tcI0> struct PointerV {
  using iptr = typename _tcI0::iptr;
  using ptr = std::pair<typename _tcI0::iptr, prov>;

  static Id<std::pair<typename _tcI0::iptr, prov>> int_to_ptr(Nat,
                                                              List<Nat> pr) {
    return bind0<MonId, typename _tcI0::iptr,
                 std::pair<typename _tcI0::iptr, prov>>(
        ret<MonId, typename _tcI0::iptr>(_tcI0::zero_iptr()),
        [=](typename _tcI0::iptr x) mutable {
          return ret<MonId, std::pair<typename _tcI0::iptr, prov>>(
              std::make_pair(x, pr));
        });
  }

  static Nat ptr_tag() {
    return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
  }
};

#endif // INCLUDED_ASSOC_TYPE_ERASED_IN_LAMBDA_BODY
