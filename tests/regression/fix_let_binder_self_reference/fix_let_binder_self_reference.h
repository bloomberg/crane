#ifndef INCLUDED_FIX_LET_BINDER_SELF_REFERENCE
#define INCLUDED_FIX_LET_BINDER_SELF_REFERENCE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
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

struct FixLetBinderSelfReference {
  static inline const std::pair<crane::fn<uint64_t(List<uint64_t>)>,
                                crane::fn<uint64_t(List<uint64_t>)>>
      both = []() {
        return []() {
          crane::fn<uint64_t(crane::fn<uint64_t(List<uint64_t>)>,
                             List<uint64_t>)>
              h = [](const crane::fn<uint64_t(List<uint64_t>)> &g,
                     const List<uint64_t> &l) { return (g(l) + UINT64_C(1)); };
          auto f_impl = [=](auto &_self_f, List<uint64_t> l) -> uint64_t {
            crane::fn<uint64_t(List<uint64_t>)> h0 = [=](List<uint64_t> _pa0) {
              return h(
                  [=](List<uint64_t> _ec0) { return _self_f(_self_f, _ec0); },
                  _pa0);
            };
            if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
              return UINT64_C(0);
            } else {
              const auto &[a0, a1] =
                  std::get<typename List<uint64_t>::Cons>(l.v());
              return h0(*a1);
            }
          };
          auto f = [=,
                    f_impl = std::move(f_impl)](List<uint64_t> l) -> uint64_t {
            return f_impl(f_impl, l);
          };
          return std::make_pair(
              f, [=](List<uint64_t> _pa0) { return h(f, _pa0); });
        }();
      }();
  static inline const uint64_t result =
      (both.first(List<uint64_t>::cons(
           UINT64_C(4),
           List<uint64_t>::cons(
               UINT64_C(5),
               List<uint64_t>::cons(UINT64_C(6), List<uint64_t>::nil())))) +
       both.second(List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil())));
};

#endif // INCLUDED_FIX_LET_BINDER_SELF_REFERENCE
