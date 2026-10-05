#ifndef INCLUDED_EFFECT_RECURSIVE_LIST
#define INCLUDED_EFFECT_RECURSIVE_LIST

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <cstdlib>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

struct EffectRecursiveList {
  /// 1. Recursive function building a list from stdin lines
  static List<std::string> read_n_lines(uint64_t n);

  /// 2. Map a function over a list with effects
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, const std::string &>
  static void map_effect(F0 &&f, const List<std::string> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
      f(a0);
      map_effect(f, *a1);
      return;
    }
  }

  /// 3. Fold a list with effects, accumulating a result
  static std::string fold_effect(const List<std::string> &xs, std::string acc);
  /// 4. Read lines and store each in env with index
  static uint64_t store_lines(std::string prefix, uint64_t n);
  /// 5. Collect env values into a list
  static List<std::optional<std::string>>
  collect_envs(const List<std::string> &names);
  /// 6. Read a line and prepend to existing list
  static List<std::string> read_and_prepend(const List<std::string> &xs);
};

#endif // INCLUDED_EFFECT_RECURSIVE_LIST
