#ifndef INCLUDED_ANON_LIFT_NAME_COLLISION
#define INCLUDED_ANON_LIFT_NAME_COLLISION

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <memory>
#include <stdexcept>
#include <type_traits>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ =
          Cons{[&]() -> A {
                 if constexpr (std::is_same_v<_U, std::any>) {
                   return crane_any_cast<A>(a);
                 } else {
                   if constexpr (std::is_constructible_v<A, const _U &>) {
                     return A(a);
                   } else {
                     throw std::logic_error("unreachable: inactive constructor "
                                            "field at this instantiation");
                   }
                 }
               }(),
               (l ? std::make_shared<List<A>>(*l) : nullptr)};
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

/// Eliminators applied directly are lifted into anonymous helpers, and every
/// one of them is named _anon_F.  Two in the same file collide — here
/// nat_rect and list_rect become one overload set and neither call
/// matches — and one used from a sibling module is not visible there at all
/// ("use of undeclared identifier '_anon_F'").  A single lifted helper in a
/// single module works, so the defect is the name, not the lifting.
struct Helper {
  static inline const uint64_t count = []() {
    return []() {
      auto f_impl = [](auto &_self_f, uint64_t n) -> uint64_t {
        if (n <= 0) {
          return UINT64_C(0);
        } else {
          uint64_t n0 = n - 1;
          return (_self_f(_self_f, n0) + 1);
        }
      };
      auto f = [&](uint64_t n) -> uint64_t { return f_impl(f_impl, n); };
      return f(UINT64_C(3));
    }();
  }();
};

struct AnonLiftNameCollision {
  template <typename T1> static uint64_t _run_F(const List<T1> l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<T1>::Cons>(l.v());
      return (_run_F<T1>(*a1) + 1);
    }
  }

  static inline const uint64_t run = (Helper::count + []() {
    return _run_F<uint64_t>(
        List<uint64_t>::cons(UINT64_C(1), List<uint64_t>::nil()));
  }());
};

#endif // INCLUDED_ANON_LIFT_NAME_COLLISION
