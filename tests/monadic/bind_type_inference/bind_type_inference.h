#ifndef INCLUDED_BIND_TYPE_INFERENCE
#define INCLUDED_BIND_TYPE_INFERENCE

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <system_error>
#include <utility>
#include <variant>
#include <vector>

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
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
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct BindTypeInference {
  template <typename T1> static T1 ignoreAndReturn(const T1 &b) { return b; }

  static int64_t test1();

  template <typename T1, typename T2>
  static T2 transform(const T1 &ma, std::type_identity_t<crane::fn<T2(T1)>> f) {
    T1 x = ma;
    return f(std::move(x));
  }

  static int64_t test2();

  template <typename T1, typename T2, typename T3>
  static T3 nested(const T1 &a, std::type_identity_t<crane::fn<T2(T1)>> f,
                   std::type_identity_t<crane::fn<T3(T2)>> g) {
    T1 x = a;
    T2 y = f(std::move(x));
    return g(std::move(y));
  }

  static int64_t test3();
  static int64_t test4();
  static List<int64_t> intToList(int64_t n);
  static List<int64_t> test5();
  static int64_t test6();
};

#endif // INCLUDED_BIND_TYPE_INFERENCE
