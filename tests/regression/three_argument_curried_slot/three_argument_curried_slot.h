#ifndef INCLUDED_THREE_ARGUMENT_CURRIED_SLOT
#define INCLUDED_THREE_ARGUMENT_CURRIED_SLOT

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <atomic>
#include <cstdint>
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

struct ThreeArgumentCurriedSlot {
  template <typename T1> static T1 idp(T1 x) { return x; }

  static uint64_t add3(uint64_t a, uint64_t b, uint64_t c);
  static uint64_t f3(uint64_t x0_, uint64_t x1_, uint64_t x2_);

  template <typename T1> static List<T1> wrap(const T1 &x) {
    return List<T1>::cons(x, List<T1>::nil());
  }

  static inline const List<crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)>>
      ws = []() {
        return crane_convert<
            List<crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)>>>(
            wrap<crane::fn<crane::fn<crane::fn<uint64_t(uint64_t)>(uint64_t)>(
                uint64_t)>>([](uint64_t _ec0) {
              return [=](uint64_t _ec1) {
                return [=](uint64_t _ec2) { return add3(_ec0, _ec1, _ec2); };
              };
            }));
      }();
  static inline const uint64_t result =
      (f3(UINT64_C(1), UINT64_C(2), UINT64_C(3)) + []() {
        auto &&_sv = ws;
        if (std::holds_alternative<typename List<
                crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)>>::Nil>(
                _sv.v())) {
          return UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<
              crane::fn<uint64_t(uint64_t, uint64_t, uint64_t)>>::Cons>(
              _sv.v());
          return a0(UINT64_C(1), UINT64_C(1), UINT64_C(1));
        }
      }());
};

#endif // INCLUDED_THREE_ARGUMENT_CURRIED_SLOT
