#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
#include <atomic>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstddef>
#include <cstdint>
#include <memory>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;

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

  uint64_t length() const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_length_in_Cons {};

    using _frame = std::variant<_call, _after_length_in_Cons>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_length_in_Cons{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_Cons>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }
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

struct STArrayHelpers {
  /// Only reads a cell.
  static uint64_t peek(std::span<const uint64_t> arr, uint64_t i);
  /// Reads one cell and writes it back.
  static void bump(std::span<uint64_t> arr, uint64_t i);
  /// A write two calls deep.
  static void middle(std::span<uint64_t> arr, uint64_t i);
  /// Writes only through middle, so still takes the writable view.
  static void outer(std::span<uint64_t> arr);
  /// Swaps the first and last cells: ST.swap_array is called, not unfolded.
  static void swap_ends(std::span<uint64_t> arr, uint64_t last);
  /// Returns one of its arrays: it keeps them, so takes them by value.
  static std::shared_ptr<crane::array_storage<uint64_t>>
  pick(bool b, std::shared_ptr<crane::array_storage<uint64_t>> arr1,
       std::shared_ptr<crane::array_storage<uint64_t>> arr2);
  /// Writes its first array and passes both to pick, which keeps them:
  /// by value too.
  static std::shared_ptr<crane::array_storage<uint64_t>>
  write_then_pick(std::shared_ptr<crane::array_storage<uint64_t>> arr1,
                  std::shared_ptr<crane::array_storage<uint64_t>> arr2);
  /// Returns its array through the monad's Ret, a legacy mapping whose
  /// argument Crane takes to be only read: borrowed, and copied where it is
  /// returned.
  static std::shared_ptr<crane::array_storage<uint64_t>>
  keep(const std::shared_ptr<crane::array_storage<uint64_t>> &arr);
  /// Zeroes n cells from i: a tail-recursive write loop keeps the
  /// writable view.
  static void zero_from(std::span<uint64_t> arr, uint64_t i, uint64_t n);
  /// Sums n cells from i: a non-tail-recursive read keeps the read view.
  static uint64_t sum_from(std::span<const uint64_t> arr, uint64_t i,
                           uint64_t n);
  /// Writes a cell, then refills the array canonically.
  static void
  write_and_refill(const std::shared_ptr<crane::array_storage<uint64_t>> &arr,
                   uint64_t v);
  /// Replaces its array, then writes the new one.
  static void
  regrow_then_write(std::shared_ptr<crane::array_storage<uint64_t>> &arr,
                    uint64_t n);
  /// A bool array: reads one cell and writes its negation back.
  static void flip(std::span<bool> arr, uint64_t i);
  /// Drives bump, outer and swap_ends over an array made from xs.
  static List<uint64_t> helpers_list(const List<uint64_t> &xs);
  /// Writes through the array keep and write_then_pick return, then reads the
  /// originals.
  static std::pair<List<uint64_t>, List<uint64_t>> keep_list(uint64_t n);
  /// Drives write_and_refill, then reads the array back.
  static std::pair<uint64_t, List<uint64_t>> refill_list(uint64_t n);
  /// Drives the recursive helpers zero_from and sum_from.
  static std::pair<uint64_t, List<uint64_t>> loops_list(uint64_t n);
  /// Checks that the caller sees the array regrow_then_write reseated.
  static List<uint64_t> regrow_list(uint64_t n);
  /// Flips cells 0 and 2 of a bool array made from bs.
  static List<bool> flip_list(const List<bool> &bs);
  /// Flips cell 1 of a bool array filled with false.
  static std::pair<bool, List<bool>> bools_filled(uint64_t n);
};
