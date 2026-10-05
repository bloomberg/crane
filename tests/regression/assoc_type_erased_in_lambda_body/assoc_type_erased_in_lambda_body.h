#ifndef INCLUDED_ASSOC_TYPE_ERASED_IN_LAMBDA_BODY
#define INCLUDED_ASSOC_TYPE_ERASED_IN_LAMBDA_BODY

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <concepts>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

struct Nat;
template <typename A> struct List;
struct IPZ;
struct MonId;
using iptr = crane::obj;
using prov = List<Nat>;
template <typename a> using Id = a;
template <typename
I>concept IPtr = requires {
    typename I::iptr;
  } && (requires {
    { I::zero_iptr() } -> std::convertible_to<typename I::iptr>;
  } || requires {
    { I::zero_iptr } -> std::convertible_to<typename I::iptr>;
  });
/// Stands in for EOU_monad: the callback is handed to a {e dictionary}
/// method, not to a plain polymorphic function.  A plain one does not
/// reproduce -- see the header.
template <typename I>
concept Mon = requires {
  typename I::template m<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
  {
    I::template bind0<crane::obj, crane::obj>(
        std::declval<typename I::template m<crane::obj>>(),
        std::declval<
            crane::fn<typename I::template m<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template m<crane::obj>>;
};
template <typename I>
concept PTR = requires {
  typename I::ptr;
  {
    I::int_to_ptr(std::declval<Nat>(), std::declval<prov>())
  } -> std::convertible_to<Id<typename I::ptr>>;
  { I::ptr_tag() } -> std::convertible_to<Nat>;
};

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

struct IPZ {
  using iptr = Nat;

  static Nat zero_iptr() { return Nat::o(); }
};

static_assert(IPtr<IPZ>);

template <Mon _tcI0, typename T2>
typename _tcI0::template m<T2> ret(const T2 &x) {
  return _tcI0::template ret<T2>(x);
}

template <Mon _tcI0, typename T2, typename T3, typename F1>
typename _tcI0::template m<T3> bind0(typename _tcI0::template m<T2> x,
                                     F1 &&x0) {
  return _tcI0::template bind0<T2, T3>(std::move(x), x0);
}

struct MonId {
  template <typename CraneA0> using m = Id<CraneA0>;

  template <typename CraneA0> static Id<CraneA0> ret(CraneA0 a) { return a; }

  template <typename CraneA0, typename CraneA1>
  static Id<CraneA1> bind0(Id<CraneA0> ma, crane::fn<Id<CraneA1>(CraneA0)> k) {
    return k(std::move(ma));
  }
};

static_assert(Mon<MonId>);

template <IPtr _tcI0> struct PointerV {
  using iptr = typename _tcI0::iptr;
  using ptr = std::pair<typename _tcI0::iptr, prov>;

  static Id<std::pair<typename _tcI0::iptr, prov>> int_to_ptr(Nat,
                                                              List<Nat> pr) {
    return bind0<MonId, typename _tcI0::iptr,
                 std::pair<typename _tcI0::iptr, prov>>(
        ret<MonId, typename _tcI0::iptr>(_tcI0::zero_iptr()),
        [=](const typename _tcI0::iptr &x) {
          return ret<MonId, std::pair<typename _tcI0::iptr, prov>>(
              std::make_pair(x, pr));
        });
  }

  static Nat ptr_tag() {
    return Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::s(Nat::o())))))));
  }
};

#endif // INCLUDED_ASSOC_TYPE_ERASED_IN_LAMBDA_BODY
