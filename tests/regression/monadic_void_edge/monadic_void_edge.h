#ifndef INCLUDED_MONADIC_VOID_EDGE
#define INCLUDED_MONADIC_VOID_EDGE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <system_error>
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

struct MonadicVoidEdge {
  /// 1. Bind where LHS is void and RHS returns a value
  static uint64_t bind_void_then_value();
  /// 2. Bind where both sides are void
  static void bind_void_void();
  /// 3. Let-binding the result of a monadic void call
  static uint64_t let_bind_monadic_void();
  /// 4. Passing unit through a chain of binds
  static void unit_chain();
  /// 5. Match on a value obtained from a bind
  static uint64_t match_after_bind();
  /// 6. Void function called in a non-tail bind position
  static std::string void_nontail();
  /// 7. Nested binds returning unit at every level
  static void deeply_nested_void();

  /// 8. Higher-order: pass a monadic void function as callback
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_effect(F0 &&f, uint64_t x0_) {
    f(x0_);
    return;
  }

  static void test_apply_effect();
  /// 9. Monadic function returning option unit
  static std::optional<std::monostate> maybe_print(bool b);
  /// 10. Bind result used in a pair
  static std::pair<uint64_t, uint64_t> bind_into_pair();
  /// 11. Void function result stored in list (should stay Unit, not void)
  static List<std::monostate> unit_in_list();
  /// 12. Mixed: some binds void, some value, interleaved
  static uint64_t mixed_binds();
  /// 13. Function that takes itree as argument and sequences
  static void sequence_effects(const std::monostate &e1,
                               const std::monostate &e2);

  static void test_sequence();
};

#endif // INCLUDED_MONADIC_VOID_EDGE
