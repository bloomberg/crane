#ifndef INCLUDED_RANK2_CALLBACK_KEPT_AS_FN
#define INCLUDED_RANK2_CALLBACK_KEPT_AS_FN

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

struct Rank2CallbackKeptAsFn {
  template <typename T1, typename T2>
  static std::pair<T1, T1>
  both(T1 f,
       std::type_identity_t<crane::fn<T1(crane::obj, List<crane::obj>, T1)>> g,
       const List<T2> &l) {
    auto f0_impl = [&](auto &_self_f0, const List<crane::obj> &m) -> T1 {
      if (std::holds_alternative<typename List<crane::obj>::Nil>(m.v())) {
        return f;
      } else {
        const auto &[a0, a1] = std::get<typename List<crane::obj>::Cons>(m.v());
        return crane_any_cast<std::pair<T1, T1>>(
            crane_call_erased(g, a0, *a1, _self_f0(_self_f0, *a1)));
      }
    };
    auto f0 = [&](const List<crane::obj> &m) -> T1 {
      return f0_impl(f0_impl, m);
    };
    return std::make_pair(f0(l), f0(l));
  }

  template <typename T1> static uint64_t len(const List<T1> &l) {
    static const auto erased_fn = crane::immortal(crane_erase_fn<crane::obj>(
        [](crane::obj, List<crane::obj>, uint64_t k) { return (k + 1); }));
    return both<uint64_t, T1>([]() { return UINT64_C(0); }(), erased_fn, l)
        .first;
  }

  static inline const uint64_t result = len<bool>(List<bool>::cons(
      true,
      List<bool>::cons(false, List<bool>::cons(true, List<bool>::nil()))));
};

#endif // INCLUDED_RANK2_CALLBACK_KEPT_AS_FN
