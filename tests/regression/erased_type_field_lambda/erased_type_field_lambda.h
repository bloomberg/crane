#ifndef INCLUDED_ERASED_TYPE_FIELD_LAMBDA
#define INCLUDED_ERASED_TYPE_FIELD_LAMBDA

#include "crane_fn.h"
#include "small_vector.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
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

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{[&]() -> A {
                        if constexpr (std::is_same_v<_U, std::any>) {
                          return crane_any_cast<A>(a);
                        } else {
                          return A(a);
                        }
                      }(),
                      (l ? std::make_shared<List<A>>(*l) : nullptr)};
    }
  }

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    crane::small_vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        std::atomic_thread_fence(std::memory_order_acquire);
        _drain(_cur->v_mut());
      }
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &, A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }

  uint64_t length() const {
    const List<A> *_self = this;

    /// _Enter: captures varying parameters for each recursive call.
    struct _Enter {
      const List<A> *_self;
    };

    /// _Resume_Cons: resumes after recursive call with _result.
    struct _Resume_Cons {};

    using _Frame = std::variant<_Enter, _Resume_Cons>;
    uint64_t _result{};
    crane::small_vector<_Frame> _stack;
    _stack.emplace_back(_Enter{_self});
    /// Loopified length: _Enter -> _Resume_Cons.
    while (!_stack.empty()) {
      _Frame _frame = std::move(_stack.back());
      _stack.pop_back();
      if (std::holds_alternative<_Enter>(_frame)) {
        auto _f = std::move(std::get<_Enter>(_frame));
        const List<A> *_self = _f._self;
        auto &&_sv = *_self;
        if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
          _result = UINT64_C(0);
        } else {
          const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_Resume_Cons{});
          _stack.emplace_back(_Enter{crane_raw(a1)});
        }
      } else {
        auto _f = std::move(std::get<_Resume_Cons>(_frame));
        _result = (std::move(_result) + 1);
      }
    }
    return _result;
  }
};

/// A record with a Type field erases its dependent fields to std::any, so
/// pairs is declared List<pair<std::any, std::function<uint64_t(std::any)>>>.
/// The producers are not erased to match: each element is built as a
/// pair<uint64_t, <concrete lambda>>, which does not convert, and the lambda
/// body adds to a std::any besides.
struct ErasedTypeFieldLambda {
  struct slot {
    List<std::pair<std::any, std::function<uint64_t(std::any)>>> pairs;
  };

  using sty = std::any;
  static uint64_t weigh(const slot &s);
  static inline const List<slot> slots = List<slot>::cons(
      slot{List<std::pair<std::any, std::function<uint64_t(std::any)>>>::cons(
          std::make_pair(UINT64_C(1), crane_erase_fn<uint64_t>(
                                          [](const auto &x) { return x; })),
          List<std::pair<std::any, std::function<uint64_t(std::any)>>>::cons(
              std::make_pair(
                  UINT64_C(2), crane_erase_fn<uint64_t>([](const auto &x) {
                    return (std::any_cast<uint64_t>(x) * UINT64_C(10));
                  })),
              List<std::pair<std::any,
                             std::function<uint64_t(std::any)>>>::nil()))},
      List<slot>::cons(
          slot{List<std::pair<std::any, std::function<uint64_t(std::any)>>>::
                   cons(std::make_pair(
                            List<uint64_t>::cons(
                                UINT64_C(1),
                                List<uint64_t>::cons(
                                    UINT64_C(2),
                                    List<uint64_t>::cons(
                                        UINT64_C(3), List<uint64_t>::nil()))),
                            crane_erase_fn<uint64_t>(
                                [](const List<uint64_t> &_x) {
                                  return _x.length();
                                })),
                        List<std::pair<std::any, std::function<uint64_t(
                                                     std::any)>>>::nil())},
          List<slot>::nil()));
  static inline const uint64_t run = slots.template fold_left<uint64_t>(
      [](uint64_t a, const slot &s) { return (a + weigh(s)); }, UINT64_C(0));
};

#endif // INCLUDED_ERASED_TYPE_FIELD_LAMBDA
