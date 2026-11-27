#pragma once

#include "crane_fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;
struct Ascii;
struct String;

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f0, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f0(std::move(_loop_a0), a1);
      }
    }
  }
};

struct Ascii {
  // DATA
  bool a0;
  bool a1;
  bool a2;
  bool a3;
  bool a4;
  bool a5;
  bool a6;
  bool a7;

  // ACCESSORS
  Ascii clone() const { return {a0, a1, a2, a3, a4, a5, a6, a7}; }

  // CREATORS
  static Ascii ascii0(bool a0, bool a1, bool a2, bool a3, bool a4, bool a5,
                      bool a6, bool a7) {
    return {a0, a1, a2, a3, a4, a5, a6, a7};
  }
};

struct String {
  // TYPES
  struct EmptyString {};

  struct String0 {
    Ascii a0;
    std::shared_ptr<String> a1;
  };

  using variant_t = std::variant<EmptyString, String0>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  String() {}

  explicit String(EmptyString _v) : v_(_v) {}

  explicit String(String0 _v) : v_(std::move(_v)) {}

  static String emptystring() { return String(EmptyString{}); }

  static String string0(Ascii a0, crane::shared_child_slot<String> a1) {
    return String(String0{std::move(a0), a1.take()});
  }

  // MANIPULATORS
  ~String() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
    auto _next = [&](variant_t &_v) -> std::shared_ptr<String> {
      if (auto *_alt = std::get_if<String0>(&_v)) {
        if (_alt->a1 && _alt->a1.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->a1);
        }
      }
      return nullptr;
    };
    std::shared_ptr<String> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  String(const String &) = default;
  String &operator=(const String &) = default;
  String(String &&) = default;
  String &operator=(String &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  uint64_t length() const {
    const String *_self = this;

    // Explicit stack replaces the non-tail recursion of length: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const String *_self;
    };

    struct _after_length_in_String0 {};

    using _frame = std::variant<_call, _after_length_in_String0>;
    uint64_t _result{};
    crane::small_vector<_frame> _stack;
    _stack.emplace_back(_call{_self});
    while (!_stack.empty()) {
      _frame &_popped = _stack.back();
      if (std::holds_alternative<_call>(_popped)) {
        auto _f = std::move(std::get<_call>(_popped));
        _stack.pop_back();
        const String *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename String::EmptyString>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[_, a1] = std::get<typename String::String0>(_sv.v());
          _stack.emplace_back(_after_length_in_String0{});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_length_in_String0>(_popped));
        _stack.pop_back();
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// @nil (nat * A) in a polymorphic definition still loses the type
/// parameter (the @nil A case in poly_nil_type_erased is fixed): the
/// fold_left receiver is a list of crane::obj pairs and its requires
/// clause rejects the step function.

/// @nil (list A) in a definition constrained by a class: no fold_left
/// matched a list of erased elements.
template <typename I, typename A>
concept Sz = requires {
  { I::sz(std::declval<A>()) } -> std::convertible_to<uint64_t>;
};

struct PolyNilPairTypeErased {
  template <typename T1> static uint64_t f(const T1 &) {
    return List<std::pair<uint64_t, T1>>::nil().template fold_left<uint64_t>(
        [](uint64_t acc, std::pair<uint64_t, T1>) { return (acc + 1); },
        UINT64_C(3));
  }

  static inline const uint64_t t = f<bool>(true);

  struct sz_nat {
    constexpr static uint64_t sz(uint64_t n) { return n; }
  };

  static_assert(Sz<sz_nat, uint64_t>);

  template <typename _tcI0, typename T1>
    requires Sz<_tcI0, T1>
  static String f1(const T1 &) {
    List<bool> l = List<List<T1>>::nil().template fold_left<List<bool>>(
        [](List<bool>,
           List<T1>) { return List<bool>::cons(true, List<bool>::nil()); },
        List<bool>::nil());
    if (std::holds_alternative<typename List<bool>::Nil>(l.v_mut())) {
      return String::emptystring();
    } else {
      return String::string0(
          Ascii::ascii0(true, false, false, false, false, true, true, false),
          String::string0(Ascii::ascii0(false, true, false, false, false, true,
                                        true, false),
                          String::emptystring()));
    }
  }

  static String f4(uint64_t n);
  static inline const uint64_t t4 = f4(UINT64_C(5)).length();
};
