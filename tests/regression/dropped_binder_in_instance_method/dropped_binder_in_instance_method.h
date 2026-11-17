#ifndef INCLUDED_DROPPED_BINDER_IN_INSTANCE_METHOD
#define INCLUDED_DROPPED_BINDER_IN_INSTANCE_METHOD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <optional>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct Functorish_option;
struct Prov_nat;
template <typename I, typename N>
concept Prov = requires {
  {
    I::aid_to_prov(std::declval<std::optional<N>>())
  } -> std::convertible_to<std::optional<List<N>>>;
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
};

template <typename I>
concept Functorish = requires {
  typename I::template F<crane::obj>;
  {
    I::template fmapish<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
};

template <Functorish _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template F<T3> fmapish(F0 &&x,
                                       typename _tcI0::template F<T2> x0) {
  return _tcI0::template fmapish<T2, T3>(x, std::move(x0));
}

struct Functorish_option {
  template <typename CraneA0> using F = std::optional<CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static std::optional<CraneA1> fmapish(crane::fn<CraneA1(CraneA0)> f,
                                        std::optional<CraneA0> o) {
    if (o.has_value()) {
      const CraneA0 &a = *o;
      return std::make_optional<CraneA1>(f(a));
    } else {
      return std::optional<CraneA1>();
    }
  }
};

static_assert(Functorish<Functorish_option>);

struct Prov_nat {
  static std::optional<List<Nat>> aid_to_prov(std::optional<Nat> aid) {
    return Functorish_option::template fmapish<Nat, List<Nat>>(
        [](const Nat &x) { return List<Nat>::cons(x, List<Nat>::nil()); },
        std::move(aid));
  }
};

static_assert(Prov<Prov_nat, Nat>);
std::optional<List<Nat>> plain(const std::optional<Nat> &o);
std::optional<List<Nat>> run(const std::optional<Nat> &o);

#endif // INCLUDED_DROPPED_BINDER_IN_INSTANCE_METHOD
