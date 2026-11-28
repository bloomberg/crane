#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "shared_block.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Datatypes {
  static crane::obj id(crane::obj x);
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
        _result = (_result + 1);
      }
    }
    return _result;
  }
};

struct IdFnResultUnboxed {
  struct pt {
    uint64_t px;
    bool py;
  };

  struct stream {
    // TYPES
    template <typename CraneS0 = stream> struct SCons_ {
      uint64_t a0;
      CraneS0 a1;
    };

    using SCons = SCons_<>;
    using variant_t = std::variant<SCons>;

  private:
    // DATA
    crane::lazy<variant_t> lazy_v_;

  public:
    // CREATORS
    stream() {}

    explicit stream(SCons _v)
        : lazy_v_(crane::lazy<variant_t>(variant_t(std::move(_v)))) {}

    explicit stream(crane::fn<variant_t()> _thunk)
        : lazy_v_(crane::lazy<variant_t>(std::move(_thunk))) {}

    static stream scons(uint64_t a0, stream a1) {
      return stream(crane::lazy<variant_t>(
          std::in_place, std::in_place_index<0>, a0, std::move(a1)));
    }

    explicit stream(crane::lazy<variant_t> _cell) : lazy_v_(std::move(_cell)) {}

    template <typename F> static stream lazy_(F &&thunk) {
      return stream(crane::lazy<variant_t>::delegate(std::forward<F>(thunk)));
    }

    // ACCESSORS
    const variant_t &v() const { return lazy_v_.force(); }

    const crane::lazy<variant_t> &lazy_cell() const { return lazy_v_; }
  };

  static stream sconst(uint64_t n);
  static inline const List<uint64_t> as_value =
      List<uint64_t>(crane::any_cast<List<crane::obj>>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
              Datatypes::id(crane_erase_fn([](uint64_t) {
                return List<crane::obj>::cons(UINT64_C(1),
                                              List<crane::obj>::nil());
              })))(crane::obj(UINT64_C(0)))));
  static uint64_t len(const List<uint64_t> &x0_);
  static inline const uint64_t as_argument =
      len(List<uint64_t>(crane::any_cast<List<crane::obj>>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
              Datatypes::id(
                  crane_erase_fn([](uint64_t) {
                    return List<crane::obj>::cons(
                        UINT64_C(1), List<crane::obj>::cons(
                                         UINT64_C(2), List<crane::obj>::nil()));
                  })))(crane::obj(UINT64_C(0))))));
  static inline const uint64_t as_receiver =
      List<uint64_t>(crane::any_cast<List<crane::obj>>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(
              Datatypes::id(crane_erase_fn([](uint64_t) {
                return List<crane::obj>::cons(
                    UINT64_C(3),
                    List<crane::obj>::cons(
                        UINT64_C(4), List<crane::obj>::cons(
                                         UINT64_C(5),
                                         List<crane::obj>::nil())));
              })))(crane::obj(UINT64_C(0)))))
          .length();
  static inline const uint64_t as_number = crane::any_cast<uint64_t>(
      crane::any_cast<crane::fn<crane::obj(crane::obj)>>(Datatypes::id(
          crane_erase_fn([](uint64_t x) { return x + UINT64_C(1); })))(
          crane::obj(UINT64_C(4))));
  static List<uint64_t> dup(uint64_t n);
  static inline const uint64_t dup_len = dup(UINT64_C(3)).length();
  static inline const uint64_t matched_nil = []() {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto id_1 = crane::immortal(Datatypes::id(
        crane_erase_fn([](uint64_t) { return List<crane::obj>::nil(); })));
    auto &&_sv =
        List<uint64_t>(crane::any_cast<List<crane::obj>>(
            crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
                crane::obj(UINT64_C(0)))));
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv.v())) {
      return UINT64_C(7);
    } else {
      return UINT64_C(1);
    }
  }();
  static uint64_t head_or_7(uint64_t n);
  static inline const uint64_t matched_head = head_or_7(UINT64_C(5));
  static inline const uint64_t stream_head = []() {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto id_1 =
        crane::immortal(Datatypes::id(
            crane_erase_fn([](bool) { return sconst(UINT64_C(9)); })));
    auto &&_sv = crane::any_cast<stream>(
        crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
            crane::obj(true)));
    const auto &[a0, _] = std::get<typename stream::SCons>(_sv.v());
    return a0;
  }();
  static inline const uint64_t pair_sum = []() -> uint64_t {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto id_1 =
        crane::immortal(Datatypes::id(crane_erase_fn([](uint64_t k) {
          return std::make_pair(crane::obj(k), crane::obj(UINT64_C(2)));
        })));
    auto [a, b] = crane_any_cast<std::pair<uint64_t, uint64_t>>(
        crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
            crane::obj(UINT64_C(5))));
    return a + b;
  }();
  static inline const uint64_t pair_list_sum = []() {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto id_1 =
        crane::immortal(Datatypes::id(crane_erase_fn([](uint64_t k) {
          return List<crane::obj>::cons(
              std::make_pair(crane::obj(k), crane::obj(UINT64_C(3))),
              List<crane::obj>::nil());
        })));
    auto &&_sv = List<std::pair<uint64_t, uint64_t>>(
        crane::any_cast<List<crane::obj>>(
            crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
                crane::obj(UINT64_C(5)))));
    if (std::holds_alternative<
            typename List<std::pair<uint64_t, uint64_t>>::Nil>(_sv.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, _] =
          std::get<typename List<std::pair<uint64_t, uint64_t>>::Cons>(_sv.v());
      const auto &[a, b] = a0;
      return a + b;
    }
  }();

  template <typename T1> static T1 pick(bool b, T1 x, T1 y) {
    if (b) {
      return x;
    } else {
      return y;
    }
  }

  static inline const uint64_t record_of_if = []() -> pt {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto id_1 =
        crane::immortal(Datatypes::id(crane_erase_fn([](pt y) { return y; })));
    if (pick<bool>(true, true, true)) {
      return crane::any_cast<pt>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
              crane::obj(pt{UINT64_C(3), true})));
    } else {
      return pt{UINT64_C(0), true};
    }
  }().px;

  template <typename T1> static T1 hd_or(T1 d, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return d;
    } else {
      const auto &[a0, _] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  }

  static inline const uint64_t excess_argument =
      hd_or<crane::fn<uint64_t(uint64_t)>>(
          [](uint64_t k) { return k + UINT64_C(7); },
          List<crane::fn<uint64_t(uint64_t)>>::nil())(crane::any_cast<uint64_t>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(Datatypes::id(
              crane_erase_fn([](uint64_t k) { return k * UINT64_C(2); })))(
              crane::obj(UINT64_C(5)))));
  static inline const uint64_t local_callee_argument = []() {
    // Built on the first call and immortal: every thread reads it without
    // touching its counts.
    static const auto id_1 = crane::immortal(Datatypes::id(
        crane_erase_fn([](uint64_t l) { return l * UINT64_C(2); })));
    crane::fn<uint64_t(uint64_t)> cf =
        [](uint64_t k) { return k + UINT64_C(1); };
    return cf(UINT64_C(0)) +
           cf(crane::any_cast<uint64_t>(
               crane::any_cast<crane::fn<crane::obj(crane::obj)>>(id_1)(
                   crane::obj(UINT64_C(4)))));
  }();
  static inline const uint64_t record_field =
      crane::any_cast<pt>(
          crane::any_cast<crane::fn<crane::obj(crane::obj)>>(Datatypes::id(
              crane_erase_fn([](uint64_t k) { return pt{k, true}; })))(
              crane::obj(UINT64_C(6))))
          .px;
};
