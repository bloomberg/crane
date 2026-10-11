#ifndef INCLUDED_ARROW_BEHIND_TYPE_FUNCTION
#define INCLUDED_ARROW_BEHIND_TYPE_FUNCTION

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

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

struct ArrowBehindTypeFunction {
  template <typename r, typename a> using cont = crane::fn<r(crane::fn<r(a)>)>;

  template <typename T1, typename T2> static cont<T1, T2> cret(T2 a) {
    return [=, a = std::move(a)](const crane::fn<T1(T2)> &k) { return k(a); };
  }

  template <typename T1, typename T2, typename T3>
  static cont<T1, T3>
  cbind(std::type_identity_t<cont<T1, T2>> m,
        std::type_identity_t<crane::fn<cont<T1, T3>(T2)>> f) {
    return [=, f = std::move(f), m = std::move(m)](const crane::fn<T1(T3)> &k) {
      return m([=](const T2 &a) { return crane::apply2(f, a, k); });
    };
  }

  template <typename T1, typename T2, typename T3>
  static cont<T1, T2> callcc(
      std::type_identity_t<crane::fn<cont<T1, T2>(crane::fn<cont<T1, T3>(T2)>)>>
          f) {
    return [=, f = std::move(f)](crane::fn<T1(T2)> k) {
      return crane::apply2(
          f, [=](T2 a) { return [=](crane::fn<T1(T3)>) { return k(a); }; }, k);
    };
  }

  static inline const uint64_t escaped = callcc<uint64_t, uint64_t, uint64_t>(
      [](const crane::fn<crane::fn<uint64_t(crane::fn<uint64_t(uint64_t)>)>(
             uint64_t)> &esc) {
        return cbind<uint64_t, uint64_t, uint64_t>(
            esc(UINT64_C(5)),
            [](uint64_t) { return cret<uint64_t, uint64_t>(UINT64_C(100)); });
      })([](uint64_t x) { return (x * UINT64_C(2)); });
  using nfun = crane::obj;
  static uint64_t applyl(uint64_t n, nfun v, const List<uint64_t> &x);
  static inline const uint64_t product = applyl(
      UINT64_C(2), crane_erase_fn([](uint64_t _x0, uint64_t _x1) -> uint64_t {
        return (_x0 * _x1);
      }),
      List<uint64_t>::cons(
          UINT64_C(3),
          List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())));
};

#endif // INCLUDED_ARROW_BEHIND_TYPE_FUNCTION
