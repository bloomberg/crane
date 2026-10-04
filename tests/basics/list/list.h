#ifndef INCLUDED_LIST
#define INCLUDED_LIST

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

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

  template <typename T1, typename F1> T1 list_rect(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return f0(a0, *a1, a1->template list_rect<T1>(std::move(f), f0));
    }
  }

  template <typename T1, typename F1> T1 list_rec(T1 f, F1 &&f0) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return f;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return f0(a0, *a1, a1->template list_rec<T1>(std::move(f), f0));
    }
  }

  List<A> tl() const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<A>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return *a1;
    }
  }

  A hd(A x) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return x;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return a0;
    }
  }

  A last(A x) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return x;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return a1->last(a0);
    }
  }

  List<A> app(List<A> l2) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return l2;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(l2)));
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return List<T1>::nil();
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<T1>::cons(f(a0), a1->template map<T1>(f));
    }
  }

  static const List<uint64_t> &mytest() {
    static const List<uint64_t> v =
        List<uint64_t>::cons(
            UINT64_C(3),
            List<uint64_t>::cons(
                UINT64_C(1),
                List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())))
            .app(List<uint64_t>::cons(
                UINT64_C(8),
                List<uint64_t>::cons(
                    UINT64_C(3),
                    List<uint64_t>::cons(
                        UINT64_C(7),
                        List<uint64_t>::cons(UINT64_C(9),
                                             List<uint64_t>::nil())))));
    return v;
  }
};

#endif // INCLUDED_LIST
