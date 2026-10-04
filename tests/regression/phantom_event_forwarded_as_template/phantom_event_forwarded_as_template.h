#ifndef INCLUDED_PHANTOM_EVENT_FORWARDED_AS_TEMPLATE
#define INCLUDED_PHANTOM_EVENT_FORWARDED_AS_TEMPLATE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct FailE;
using ptr = crane::obj;
template <typename
I>concept Params = requires {
    typename I::ptr;
    { I::width() } -> std::convertible_to<Nat>;
  } && (requires {
    { I::zero_ptr() } -> std::convertible_to<typename I::ptr>;
  } || requires {
    { I::zero_ptr } -> std::convertible_to<typename I::ptr>;
  });

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
};

struct FailE {
  // DATA
  std::monostate a0;

  // ACCESSORS
  FailE clone() const { return {a0}; }

  // CREATORS
  static FailE Throw_(std::monostate a0) { return {a0}; }
};

template <typename ptr, typename e = void>
using semantic_function =
    crane::fn<std::shared_ptr<ITree<Nat>>(List<ptr>, std::optional<ptr>)>;
template <typename ptr, typename e>
using intrinsic_definitions = List<std::pair<Nat, semantic_function<ptr, e>>>;

template <Params _tcI0, typename T1>
semantic_function<typename _tcI0::ptr, T1> one() {
  return [=](List<typename _tcI0::ptr>, std::optional<typename _tcI0::ptr>) {
    return itree_ret(_tcI0::width());
  };
}

template <Params _tcI0, typename T1>
intrinsic_definitions<typename _tcI0::ptr, T1> defined_intrinsics() {
  return List<std::pair<Nat, crane::fn<std::shared_ptr<ITree<Nat>>(
                                 List<typename _tcI0::ptr>,
                                 std::optional<typename _tcI0::ptr>)>>>::
      cons(
          std::make_pair(Nat::o(), one<_tcI0, T1>()),
          List<
              std::pair<Nat, crane::fn<std::shared_ptr<ITree<Nat>>(
                                 List<typename _tcI0::ptr>,
                                 std::optional<typename _tcI0::ptr>)>>>::nil());
}

struct PhantomEventForwardedAsTemplate {
  template <Params _tcI0>
  static intrinsic_definitions<typename _tcI0::ptr, FailE> use() {
    return defined_intrinsics<_tcI0, FailE>();
  }
};

#endif // INCLUDED_PHANTOM_EVENT_FORWARDED_AS_TEMPLATE
