#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <concepts>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
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
    requires std::is_invocable_r_v<List<T1>, F0 &, A &>
  List<T1> flat_map(F0 &&f) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of flat_map: _call frames
    // are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_flat_map_in_Cons {
      A a0;
    };

    using _frame = std::variant<_call, _after_flat_map_in_Cons>;
    List<T1> _result{};
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
          _result = List<T1>::nil();
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_flat_map_in_Cons{a0});
          _stack.emplace_back(_call{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_after_flat_map_in_Cons>(_popped));
        _stack.pop_back();
        auto a0 = std::move(_f.a0);
        _result = f(a0).app(std::move(_result));
      }
    }
    return _result;
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
        _result = (_result + 1);
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

/// A monad class whose bind is polymorphic in both type arguments boxes
/// and unboxes inconsistently across nested binds.
template <typename I>
concept Monad = requires {
  typename I::template M<crane::obj>;
  {
    I::template ret<crane::obj>(std::declval<crane::obj>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
  {
    I::template bind<crane::obj, crane::obj>(
        std::declval<typename I::template M<crane::obj>>(),
        std::declval<crane::fn<typename I::template M<crane::obj>(crane::obj)>>())
  } -> std::convertible_to<typename I::template M<crane::obj>>;
};

struct MonadClassNestedBind {
  template <Monad _tcI0, typename T2>
  static typename _tcI0::template M<T2> ret(const T2 &x) {
    return _tcI0::template ret<T2>(x);
  }

  template <Monad _tcI0, typename T2, typename T3, typename F1>
  static typename _tcI0::template M<T3> bind(typename _tcI0::template M<T2> x,
                                             F1 &&x0) {
    return _tcI0::template bind<T2, T3>(std::move(x), x0);
  }

  struct MOption {
    template <typename CraneA0> using M = std::optional<CraneA0>;

    template <typename CraneA0> static std::optional<CraneA0> ret(CraneA0 x) {
      return std::make_optional<CraneA0>(std::move(x));
    }

    template <typename CraneA0, typename CraneA1>
    static std::optional<CraneA1>
    bind(std::optional<CraneA0> m,
         crane::fn<std::optional<CraneA1>(CraneA0)> f) {
      if (m.has_value()) {
        const CraneA0 &x = *m;
        return f(x);
      } else {
        return std::optional<CraneA1>();
      }
    }
  };

  static_assert(Monad<MOption>);

  struct MList {
    template <typename CraneA0> using M = List<CraneA0>;

    template <typename CraneA0> static List<CraneA0> ret(CraneA0 x) {
      return List<CraneA0>::cons(std::move(x), List<CraneA0>::nil());
    }

    template <typename CraneA0, typename CraneA1>
    static List<CraneA1> bind(List<CraneA0> m,
                              crane::fn<List<CraneA1>(CraneA0)> f) {
      return m.template flat_map<CraneA1>(std::move(f));
    }
  };

  static_assert(Monad<MList>);

  template <Monad _tcI0>
  static typename _tcI0::template M<List<uint64_t>> chain(uint64_t x) {
    return _tcI0::template bind<uint64_t, List<uint64_t>>(
        _tcI0::template ret<uint64_t>(x), [](uint64_t n) {
          return _tcI0::template bind<uint64_t, List<uint64_t>>(
              _tcI0::template ret<uint64_t>(n + UINT64_C(1)), [=](uint64_t m) {
                return _tcI0::template ret<List<uint64_t>>(List<uint64_t>::cons(
                    n, List<uint64_t>::cons(m, List<uint64_t>::nil())));
              });
        });
  }

  static inline const uint64_t total = []() -> uint64_t {
    auto _cs = chain<MOption>(UINT64_C(1));
    if (_cs.has_value()) {
      const List<uint64_t> &l = *_cs;
      return l.length();
    } else {
      return UINT64_C(0);
    }
  }() + chain<MList>(UINT64_C(2)).length();
};
