#ifndef INCLUDED_HKT_NULLARY_METHOD_TYARG
#define INCLUDED_HKT_NULLARY_METHOD_TYARG

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;

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

/// emptyc takes no value argument, so its element type is not deducible and
/// must be passed explicitly.  The generic body omits it:
///
/// return sizec<_tcI0>(addc<_tcI0>(x, addc<_tcI0>(y, emptyc<_tcI0>())));
///
/// error: no matching function for call to 'emptyc'
/// (the wrapper is declared template <Coll _tcI0, typename T2>)
template <typename I>
concept Coll = requires {
  typename I::template C<crane::obj>;
  {
    I::template emptyc<crane::obj>()
  } -> std::convertible_to<typename I::template C<crane::obj>>;
  {
    I::template addc<crane::obj>(
        std::declval<crane::obj>(),
        std::declval<typename I::template C<crane::obj>>())
  } -> std::convertible_to<typename I::template C<crane::obj>>;
  {
    I::template sizec<crane::obj>(
        std::declval<typename I::template C<crane::obj>>())
  } -> std::convertible_to<Nat>;
};

struct HktNullaryMethodTyarg {
  template <Coll _tcI0, typename T2>
  static typename _tcI0::template C<T2> emptyc() {
    return _tcI0::template emptyc<T2>();
  }

  template <Coll _tcI0, typename T2>
  static typename _tcI0::template C<T2>
  addc(const T2 &x, typename _tcI0::template C<T2> x0) {
    return _tcI0::template addc<T2>(x, std::move(x0));
  }

  template <Coll _tcI0, typename T2>
  static Nat sizec(typename _tcI0::template C<T2> x) {
    return _tcI0::template sizec<T2>(std::move(x));
  }

  template <typename T1> static Nat llen(const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return Nat::o();
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return Nat::s(llen<T1>(*a1));
    }
  }

  struct LC {
    template <typename CraneA0> using C = List<CraneA0>;

    template <typename CraneA0> static List<CraneA0> emptyc() {
      return List<CraneA0>::nil();
    }

    template <typename CraneA0>
    static List<CraneA0> addc(CraneA0 x, List<CraneA0> l) {
      return List<CraneA0>::cons(std::move(x), std::move(l));
    }

    template <typename CraneA0> static Nat sizec(List<CraneA0> a0) {
      return llen<CraneA0>(std::move(a0));
    }
  };

  static_assert(Coll<LC>);

  template <Coll _tcI0, typename T2> static Nat two(const T2 &x, const T2 &y) {
    return sizec<_tcI0, T2>(
        addc<_tcI0, T2>(x, addc<_tcI0, T2>(y, emptyc<_tcI0, T2>())));
  }

  static inline const Nat run =
      two<LC, Nat>(Nat::s(Nat::o()), Nat::s(Nat::s(Nat::o())));
};

#endif // INCLUDED_HKT_NULLARY_METHOD_TYARG
