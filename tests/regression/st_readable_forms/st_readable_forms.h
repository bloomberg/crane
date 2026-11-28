#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

template <typename T1> struct code_const;
template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
enum class Refs;
template <typename I, typename V, typename A>
concept Code = requires {
  { I::code() } -> std::convertible_to<uint64_t>;
};

struct ListDef {
  static List<uint64_t> seq(uint64_t start, uint64_t len);
};

struct Nat {};

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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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

template <typename Err> struct ExceptE {
  // DATA
  Err a0;

  // ACCESSORS
  ExceptE<Err> clone() const { return {a0}; }

  template <typename CraneU> operator ExceptE<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const Err &>) {
        return crane_convert<CraneU>(a0);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static ExceptE<Err> Throw_(Err a0) { return {std::move(a0)}; }
};

struct Err {
  // DATA
  std::string x;

  // ACCESSORS
  Err clone() const { return {x}; }

  // CREATORS
  static Err error(std::string x) { return {std::move(x)}; }
};

enum class Refs { BUILD_REFS };

struct ST {
  template <typename T2, typename T3, typename F2>
  static T3 for_each_with(const List<T2> &xs, const T3 &v, F2 &&f);
};

template <typename T1> struct code_const {
  constexpr static uint64_t code() { return UINT64_C(0); }
};

/// pair_parts, run in C++.
uint64_t pair_parts();
/// fib_step, run in C++.
uint64_t fib_step(uint64_t n);
/// One step of sum_with: add element i to acc.
uint64_t add_at(std::span<const uint64_t> arr, uint64_t acc, uint64_t i);
/// sum_with, run in C++.
uint64_t sum_with();
/// run_count_back, run in C++.
uint64_t count_back(std::span<uint64_t> arr, uint64_t k);
/// count_back over a fresh four-element array.
uint64_t run_count_back();
/// Ignores its reference.
uint64_t ignore_ref(const uint64_t *_x0, uint64_t n);
/// Writes r, then hands it to ignore_ref.
uint64_t pass_view(uint64_t *r0);
/// unused_param, run in C++.
uint64_t unused_param();

struct STReadableForms {
  /// pair_parts, run in C++.
  static inline const uint64_t pair_parts = ::pair_parts();
  /// fib_step, run in C++.
  static uint64_t fib_step(uint64_t n);
  /// sum_with, run in C++.
  static inline const uint64_t sum_with = ::sum_with();
  /// run_count_back, run in C++.
  static inline const uint64_t count_back = run_count_back();
  /// unused_param, run in C++.
  static inline const uint64_t unused_param = ::unused_param();
};

template <typename T2, typename T3, typename F2>
T3 ST::for_each_with(const List<T2> &xs, const T3 &v, F2 &&f) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  T3 _loop_v = v;
  const List<T2> *_loop_xs = &xs;
  while (true) {
    if (std::holds_alternative<typename List<T2>::Nil>(_loop_xs->v())) {
      return _loop_v;
    } else {
      const auto &[a0, a1] = std::get<typename List<T2>::Cons>(_loop_xs->v());
      _loop_v = f(_loop_v, a0);
      _loop_xs = crane_raw(a1);
    }
  }
}
