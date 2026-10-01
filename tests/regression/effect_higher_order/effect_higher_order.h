#ifndef INCLUDED_EFFECT_HIGHER_ORDER
#define INCLUDED_EFFECT_HIGHER_ORDER

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

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

struct EffectHigherOrder {
  /// 1. Higher-order function with effectful callback
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, std::string &>
  static void apply_effect(F0 &&f, std::string x0_) {
    f(std::move(x0_));
    return;
  }

  /// 2. Map-like function over a list with effects
  static void for_each_str(crane::fn<void(std::string)> f,
                           const List<std::string> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
      f(a0);
      for_each_str(std::move(f), *a1);
      return;
    }
  }

  /// 3. Callback that returns a value
  template <typename F0> static std::string with_line(F0 &&f) {
    std::string _bind_result = []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
    return f(_bind_result);
  }

  /// 4. Nested bind in callback
  static std::string transform_input(crane::fn<std::string(std::string)> f) {
    std::string line;
    std::getline(std::cin, line);
    return f(line);
  }

  /// 5. Effectful callback passed as argument
  static void greet_all(const List<std::string> &names);
  /// 6. Callback with env effect
  static std::string lookup_or_ask(std::string name);
  /// 7. Chain of lookups
  static List<std::string> lookup_all(const List<std::string> &names);
  /// 8. Effect in let-bound function
  static std::string process_input();
};

#endif // INCLUDED_EFFECT_HIGHER_ORDER
