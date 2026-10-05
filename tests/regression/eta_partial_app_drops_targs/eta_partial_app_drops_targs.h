#ifndef INCLUDED_ETA_PARTIAL_APP_DROPS_TARGS
#define INCLUDED_ETA_PARTIAL_APP_DROPS_TARGS

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
struct Mon_option;
template <typename I>
concept Mon = requires {
  typename I::template m<crane::obj>;
  {
    I::template mret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template mbind<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};
template <typename I>
concept Fun = requires {
  typename I::template F<crane::obj>;
  {
    I::template ffmap<crane::obj, crane::obj>(
        std::declval<crane::fn<crane::obj(crane::obj)>>(),
        std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
  {
    I::fconst(std::declval<crane::obj>(),
              std::declval<typename I::template F<crane::obj>>())
  } -> std::convertible_to<typename I::template F<crane::obj>>;
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
};

template <Mon _tcI0, typename T2>
typename _tcI0::template m<T2> mret(const T2 &x) {
  return _tcI0::template mret<T2>(x);
}

template <Mon _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> mbind(typename _tcI0::template m<T2> x,
                                     F1 &&x0) {
  return _tcI0::template mbind<T2, T3>(std::move(x), x0);
}

template <Mon _tcI0, typename T2, typename T3>
typename _tcI0::template m<T3> liftM(std::type_identity_t<crane::fn<T3(T2)>> f,
                                     typename _tcI0::template m<T2> x) {
  return mbind<_tcI0, T2, T3>(
      std::move(x), [=](const T2 &a) { return mret<_tcI0, T3>(f(a)); });
}

template <Fun _tcI0, typename T2, typename T3, typename F0>
typename _tcI0::template F<T3> ffmap(F0 &&x,
                                     typename _tcI0::template F<T2> x0) {
  return _tcI0::template ffmap<T2, T3>(x, std::move(x0));
}

struct Mon_option {
  template <typename CraneA0> using m = std::optional<CraneA0>;

  template <typename CraneA0> static std::optional<CraneA0> mret(CraneA0 a) {
    return std::make_optional<CraneA0>(std::move(a));
  }

  template <typename CraneA0, typename CraneA1>
  static std::optional<CraneA1>
  mbind(std::optional<CraneA0> o,
        crane::fn<std::optional<CraneA1>(CraneA0)> k) {
    if (o.has_value()) {
      const CraneA0 &a = *o;
      return k(a);
    } else {
      return std::optional<CraneA1>();
    }
  }
};

static_assert(Mon<Mon_option>);

template <Mon _tcI0> struct Fun_Mon {
  template <typename CraneA0> using m = typename _tcI0::template m<CraneA0>;
  template <typename CraneA0> using F = typename _tcI0::template m<CraneA0>;

  template <typename CraneA0, typename CraneA1>
  static typename _tcI0::template m<CraneA1>
  ffmap(crane::fn<CraneA1(CraneA0)> a0,
        typename _tcI0::template m<CraneA0> a1) {
    return liftM<_tcI0, CraneA0, CraneA1>(std::move(a0), std::move(a1));
  }

  static typename _tcI0::template m<crane::obj> fconst(crane::obj a,
                                                       crane::obj x) {
    return liftM<_tcI0, crane::obj, crane::obj>(
        [=](const auto &) { return a; },
        crane_any_cast<typename _tcI0::template m<crane::obj>>(x));
  }
};

std::optional<List<Nat>> run(const std::optional<Nat> &o);

#endif // INCLUDED_ETA_PARTIAL_APP_DROPS_TARGS
