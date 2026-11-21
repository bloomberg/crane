#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <algorithm>
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

template <typename A> struct List;
template <typename Err> struct ExceptE;
struct Err;
struct STRefNat;
template <typename I, typename T>
concept Ix = requires {
  {
    I::range(std::declval<T>(), std::declval<T>())
  } -> std::convertible_to<List<T>>;
  {
    I::index(std::declval<T>(), std::declval<T>(), std::declval<T>())
  } -> std::convertible_to<std::optional<uint64_t>>;
  {
    I::rangeSize(std::declval<T>(), std::declval<T>())
  } -> std::convertible_to<uint64_t>;
  { I::toNat(std::declval<T>()) } -> std::convertible_to<uint64_t>;
  { I::fromNat(std::declval<uint64_t>()) } -> std::convertible_to<T>;
  { I::suc(std::declval<T>()) } -> std::convertible_to<T>;
  { I::sub(std::declval<T>(), std::declval<T>()) } -> std::convertible_to<T>;
  { I::max(std::declval<T>(), std::declval<T>()) } -> std::convertible_to<T>;
  { I::zero() } -> std::convertible_to<T>;
};
template <typename I, typename T>
concept STRefClass = requires {
  { I::mkSTRef(std::declval<T>()) } -> std::convertible_to<crane::obj>;
  { I::STRefToIx(std::declval<crane::obj>()) } -> std::convertible_to<T>;
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
  template <typename T1 = void, typename T2, typename T3, typename F2>
  static T3 for_each_with(const List<T2> &xs, const T3 &v, F2 &&f);
};

template <typename _tcI0, typename _tcI1, typename T1, typename T2 = void,
          typename T3 = void>
  requires STRefClass<_tcI0, T1> && Ix<_tcI1, T1>
T1 partition(std::shared_ptr<crane::array_storage<uint64_t>> arr, T1 arr_idx,
             const T1 &left, const T1 &right, const T1 &pivotIndex) {
  uint64_t pivotValue = std::span<const uint64_t>{*arr}[pivotIndex];
  STMonad::template swapArray<_tcI0, T3, T1, T2, uint64_t>(
      arr_idx, std::span<uint64_t>{*arr}, pivotIndex, right);
  T1 storeIndex = STMonad::template for_each_with<T3, T1, T1>(
      _tcI1::range(left, _tcI1::sub(right, _tcI1::suc(_tcI1::zero()))), left,
      [=](const T1 &storeIndex, const T1 &i) {
        uint64_t val = std::span<const uint64_t>{*arr}[i];
        if (val <= pivotValue) {
          STMonad::template swapArray<_tcI0, T3, T1, T2, uint64_t>(
              arr_idx, std::span<uint64_t>{*arr}, i, storeIndex);
          return _tcI1::suc(storeIndex);
        } else {
          return storeIndex;
        }
      });
  STMonad::template swapArray<_tcI0, T3, T1, T2, uint64_t>(
      std::move(arr_idx), std::span<uint64_t>{*arr}, storeIndex, right);
  return storeIndex;
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
  struct nat_idx {
    static List<uint64_t> range(uint64_t fp, uint64_t sp) {
      auto _once1 = (UINT64_C(1) + sp);
      return ListDef::seq(fp, (((_once1 - fp) > _once1 ? 0 : (_once1 - fp))));
    }

    constexpr static std::optional<uint64_t> index(uint64_t fp, uint64_t sp,
                                                   uint64_t i) {
      if ((fp <= i && i <= sp)) {
        return std::make_optional<uint64_t>((((i - fp) > i ? 0 : (i - fp))));
      } else {
        return std::optional<uint64_t>();
      }
    }

    constexpr static uint64_t rangeSize(uint64_t fp, uint64_t sp) {
      auto _once2 = (UINT64_C(1) + sp);
      return (((_once2 - fp) > _once2 ? 0 : (_once2 - fp)));
    }

    constexpr static uint64_t toNat(uint64_t n) { return n; }

    constexpr static uint64_t fromNat(uint64_t n) { return n; }

    constexpr static uint64_t suc(uint64_t x) { return (x + 1); }

    constexpr static uint64_t sub(uint64_t a0, uint64_t a1) {
      return (((a0 - a1) > a0 ? 0 : (a0 - a1)));
    }

    constexpr static uint64_t max(uint64_t a0, uint64_t a1) {
      return std::max(a0, a1);
    }

    constexpr static uint64_t zero() { return UINT64_C(0); }
  };

  static_assert(Ix<nat_idx, uint64_t>);

  struct nat_stref {
    static crane::obj mkSTRef(uint64_t x) { return STRefNat::mkstref(x); }

    static uint64_t STRefToIx(crane::obj _p_a0) {
      STRefNat a0 = crane::any_cast<STRefNat>(_p_a0);
      return a0.STRefToIxNat();
    }
  };

  static_assert(STRefClass<nat_stref, uint64_t>);
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

template <typename T1, typename T2, typename T3, typename F2>
T3 STMonad::for_each_with(const List<T2> &xs, const T3 &v, F2 &&f) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  T3 _loop_v = v;
  const List<T2> *_loop_xs = &xs;
  while (true) {
    if (std::holds_alternative<typename List<T2>::Nil>(_loop_xs->v())) {
      return _loop_v;
    } else {
      const auto &[a0, a1] = std::get<typename List<T2>::Cons>(_loop_xs->v());
      T3 v_ = f(_loop_v, a0);
      _loop_v = std::move(v_);
      _loop_xs = crane_raw(a1);
    }
  }
}

inline uint64_t STRefNat::STRefToIxNat() const {
  const auto &[s] = *this;
  return s;
}
