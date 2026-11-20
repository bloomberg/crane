#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <crane_st.h>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>
#include <vector>

struct nat_ix_stref;
template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::STRefToIx(std::declval<crane::obj>()) } -> std::convertible_to<T>;
};

struct StArrayHelpers {
  /// Reads one cell and writes it back.
  static void bump(const std::shared_ptr<std::vector<uint64_t>> &arr,
                   uint64_t i);
  /// A write two calls deep.
  static void middle(const std::shared_ptr<std::vector<uint64_t>> &arr,
                     uint64_t i);
  static void outer(const std::shared_ptr<std::vector<uint64_t>> &arr);
  /// Swaps the first and last cells: swapArray is called, not unfolded.
  static void swap_ends(const std::shared_ptr<std::vector<uint64_t>> &arr,
                        uint64_t last);
  /// Returns one of its arrays: it keeps them, so takes them by value.
  static std::shared_ptr<std::vector<uint64_t>>
  pick(bool b, std::shared_ptr<std::vector<uint64_t>> arr1,
       std::shared_ptr<std::vector<uint64_t>> arr2);
  /// Writes its first array and passes both to pick, which keeps them:
  /// by value too.
  static std::shared_ptr<std::vector<uint64_t>>
  write_then_pick(std::shared_ptr<std::vector<uint64_t>> arr1,
                  std::shared_ptr<std::vector<uint64_t>> arr2);
  /// Returns its array through the monad's Ret, a legacy mapping whose
  /// argument Crane takes to be only read: borrowed, and copied where it is
  /// returned.
  static std::shared_ptr<std::vector<uint64_t>>
  keep(const std::shared_ptr<std::vector<uint64_t>> &arr);
  /// Replaces its array, then writes the new one.
  static void regrow_then_write(std::shared_ptr<std::vector<uint64_t>> &arr,
                                uint64_t n);
  /// A bool array: reads one cell and writes its negation back.
  static void flip(const std::shared_ptr<std::vector<bool>> &arr, uint64_t i);
  static List<uint64_t> helpers_list(const List<uint64_t> &xs);
  static std::pair<List<uint64_t>, List<uint64_t>> keep_list(uint64_t n);
  static List<uint64_t> regrow_list(uint64_t n);
  static List<bool> flip_list(const List<bool> &bs);
  static std::pair<bool, List<bool>> bools_filled(uint64_t n);
};

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
        _result = (std::move(_result) + 1);
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

struct STRefNat {
  // DATA
  uint64_t s;

  // ACCESSORS
  STRefNat clone() const { return {s}; }

  // CREATORS
  static STRefNat mkstref(uint64_t s) { return {s}; }

  uint64_t STRefToIxNat() const;
};

struct STMonad {
  template <typename _tcI0, typename T1 = void, typename T2, typename T3 = void,
            typename T4>
    requires STRefClass<_tcI0, T2>
  static void swapArray(const T2 &_x,
                        const std::shared_ptr<std::vector<T4>> &arr,
                        const T2 &i, const T2 &j);
};

struct nat_ix_stref {
  static crane::obj mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

  static uint64_t STRefToIx(crane::obj _p_a0) {
    STRefNat a0 = crane::any_cast<STRefNat>(_p_a0);
    return a0.STRefToIxNat();
  }
};

static_assert(STRefClass<nat_ix_stref, uint64_t>);

template <typename _tcI0, typename T1, typename T2, typename T3, typename T4>
  requires STRefClass<_tcI0, T2>
void STMonad::swapArray(const T2 &, const std::shared_ptr<std::vector<T4>> &arr,
                        const T2 &i, const T2 &j) {
  T4 vi = (*arr)[i];
  T4 vj = (*arr)[j];
  (*arr)[i] = std::move(vj);
  (*arr)[j] = std::move(vi);
  return;
}

inline uint64_t STRefNat::STRefToIxNat() const {
  const auto &[s] = *this;
  return s;
}
