#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <array_storage.h>
#include <atomic>
#include <concepts>
#include <crane_itree.h>
#include <crane_st.h>
#include <crane_string.h>
#include <cstdint>
#include <memory>
#include <optional>
#include <span>
#include <stdexcept>
#include <string>
#include <string_view>
#include <template_argument.h>
#include <type_traits>
#include <utility>
#include <variant>

struct nat_ix_stref;
template <typename A> struct List;
template <typename A> struct Sig;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::STRefToIx(std::declval<crane::obj>()) } -> std::convertible_to<T>;
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

  template <typename F0> List<A> filter(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<A>::nil();
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        if (f(a0)) {
          auto _cell = typename List<A>::Cons(a0, nullptr);
          List<A> &_node =
              (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                      : _root.emplace(std::move(_cell)));
          _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
          _loop_self = crane_raw(a1);
          continue;
        } else {
          _loop_self = crane_raw(a1);
          continue;
        }
      }
    }
    return std::move(*_root);
  }

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

  List<A> app(List<A> m) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<A>> _root{};
    std::shared_ptr<List<A>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = std::move(m);
        (_write ? *(*_write = std::make_shared<List<A>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<A>::Cons(a0, nullptr);
        List<A> &_node =
            (_write ? *(*_write = std::make_shared<List<A>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<A>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  template <typename CraneU> operator Sig<CraneU>() const {
    return {[&]() -> CraneU {
      if constexpr (crane_convertible<CraneU, const A &>) {
        return crane_convert<CraneU>(x);
      } else {
        throw std::logic_error("unreachable: inactive constructor field at "
                               "this instantiation");
      }
    }()};
  }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
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
  static void swapArray(const T2 &_x, std::span<T4> arr, const T2 &i,
                        const T2 &j);
};

struct nat_ix_stref {
  static crane::obj mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

  static uint64_t STRefToIx(crane::obj _p_a0) {
    STRefNat a0 = crane::any_cast<STRefNat>(_p_a0);
    return a0.STRefToIxNat();
  }
};

static_assert(STRefClass<nat_ix_stref, uint64_t>);

template <typename T1 = void, typename T2 = void>
Sig<uint64_t> lomuto_scan(std::span<uint64_t> arr, uint64_t pv, uint64_t,
                          uint64_t hi, uint64_t i, uint64_t s) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  uint64_t _loop_s = s;
  uint64_t _loop_i = i;
  while (true) {
    if (_loop_i < hi) {
      uint64_t v = std::span<const uint64_t>{arr}[_loop_i];
      if (v <= pv) {
        STMonad::template swapArray<nat_ix_stref, crane::obj, uint64_t,
                                    crane::obj, uint64_t>(UINT64_C(0), arr,
                                                          _loop_i, _loop_s);
        _loop_s = (_loop_s + 1);
        _loop_i = (_loop_i + 1);
      } else {
        _loop_i = (_loop_i + 1);
      }
    } else {
      return Sig<uint64_t>::exist(_loop_s);
    }
  }
}

template <typename T1 = void, typename T2 = void>
Sig<uint64_t> partition(std::span<uint64_t> arr, uint64_t lo, uint64_t hi,
                        uint64_t pividx) {
  uint64_t pv = std::span<const uint64_t>{arr}[pividx];
  STMonad::template swapArray<nat_ix_stref>(UINT64_C(0), arr, pividx, hi);
  Sig<uint64_t> p = lomuto_scan<crane::obj, void>(arr, pv, lo, hi, lo, lo);
  STMonad::template swapArray<nat_ix_stref>(
      UINT64_C(0),
      arr,
      [&]() {
        const auto &[x] = p;
        return x;
      }(),
      hi);
  return p;
}

template <typename T1 = void, typename T2 = void>
void quicksort_ST(std::span<uint64_t> arr, uint64_t lo, uint64_t hi) {
  if (lo < hi) {
    Sig<uint64_t> p = partition<crane::obj, T2>(
        arr, lo, hi,
        (lo +
         (UINT64_C(2) ? (((hi - lo) > hi ? 0 : (hi - lo))) / UINT64_C(2) : 0)));
    auto _once1 = [&]() {
      const auto &[x] = p;
      return x;
    }();
    quicksort_ST<crane::obj, T2>(
        arr, lo,
        (((_once1 - UINT64_C(1)) > _once1 ? 0 : (_once1 - UINT64_C(1)))));
    quicksort_ST<crane::obj, T2>(
        arr,
        ([&]() {
          auto &[x0] = p;
          return x0;
        }() + UINT64_C(1)),
        hi);
    return;
  } else {
    return;
  }
}

template <typename F1>
  requires std::is_invocable_r_v<List<uint64_t>, F1 &, List<uint64_t>>
List<uint64_t> quicksort_fun_functional(const List<uint64_t> &l,
                                        F1 &&quicksort_fun0) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    const List<uint64_t> &a1_value = *a1;
    return quicksort_fun0(a1_value.filter([=](uint64_t x) {
      return x < a0;
    }))
               .app(List<uint64_t>::cons(a0, List<uint64_t>::nil()).app(
        quicksort_fun0(a1_value.filter([=](uint64_t x) { return a0 <= x; }))));
  }
}

struct StQuicksort {
  static List<uint64_t> quicksort_fun(const List<uint64_t> &x);
  static List<uint64_t> quicksort_ST_mine(const List<uint64_t> &xs);
  static uint64_t nth(uint64_t n, const List<uint64_t> &l, uint64_t default0);
  static std::string list_to_string_helper(const List<uint64_t> &l);
  static std::string list_to_string(const List<uint64_t> &l);
  [[gnu::used]] static inline const List<uint64_t> input_lst1 =
      List<uint64_t>::cons(
          UINT64_C(212498),
          List<uint64_t>::cons(
              UINT64_C(127),
              List<uint64_t>::cons(
                  UINT64_C(5981),
                  List<uint64_t>::cons(
                      UINT64_C(2749812),
                      List<uint64_t>::cons(
                          UINT64_C(74879),
                          List<uint64_t>::cons(
                              UINT64_C(126),
                              List<uint64_t>::cons(
                                  UINT64_C(4),
                                  List<uint64_t>::cons(
                                      UINT64_C(51),
                                      List<uint64_t>::cons(
                                          UINT64_C(2412),
                                          List<uint64_t>::cons(
                                              UINT64_C(10645),
                                              List<uint64_t>::nil()))))))))));
  static std::string test_quicksort_ST();
  static std::string test_quicksort_fun();
};

template <typename _tcI0, typename T1, typename T2, typename T3, typename T4>
  requires STRefClass<_tcI0, T2>
void STMonad::swapArray(const T2 &, std::span<T4> arr, const T2 &i,
                        const T2 &j) {
  T4 vi = std::span<const T4>{arr}[i];
  T4 vj = std::span<const T4>{arr}[j];
  arr[i] = std::move(vj);
  arr[j] = std::move(vi);
  return;
}

inline uint64_t STRefNat::STRefToIxNat() const {
  const auto &[s] = *this;
  return s;
}
