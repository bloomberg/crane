#ifndef INCLUDED_EXISTENTIAL_CTOR_ERASED_FN
#define INCLUDED_EXISTENTIAL_CTOR_ERASED_FN

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

struct ExistentialCtorErasedFn {
  /// The same erased-function-parameter failure reached through a user
  /// inductive with an existential constructor rather than through sigT.
  struct dynamic {
    // DATA
    std::any a;
    std::function<uint64_t(std::any)> a1;

    // ACCESSORS
    dynamic clone() const { return {a, a1}; }

    // CREATORS
    static dynamic dyn(std::any a, std::function<uint64_t(std::any)> a1) {
      return {std::move(a), std::move(a1)};
    }
  };

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::any &,
                                   std::function<uint64_t(std::any)> &>
  static T1 dynamic_rect(F0 &&f, const dynamic &d) {
    const auto &[a0, a1] = d;
    return std::any_cast<T1>(f(a0, a1));
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, std::any &,
                                   std::function<uint64_t(std::any)> &>
  static T1 dynamic_rec(F0 &&f, const dynamic &d) {
    const auto &[a0, a1] = d;
    return std::any_cast<T1>(f(a0, a1));
  }

  static uint64_t read(const dynamic &d);
  static inline const List<dynamic> items = List<dynamic>::cons(
      dynamic::dyn(UINT64_C(7), std::function<uint64_t(std::any)>(
                                    [](const std::any &n) -> uint64_t {
                                      return std::any_cast<uint64_t>(n);
                                    })),
      List<dynamic>::cons(
          dynamic::dyn(true, std::function<uint64_t(std::any)>(
                                 [](const std::any &b) -> uint64_t {
                                   if (std::any_cast<bool>(b)) {
                                     return UINT64_C(1);
                                   } else {
                                     return UINT64_C(0);
                                   }
                                 })),
          List<dynamic>::cons(
              dynamic::dyn(
                  List<std::any>::cons(
                      UINT64_C(1),
                      List<std::any>::cons(
                          UINT64_C(2),
                          List<std::any>::cons(UINT64_C(3),
                                               List<std::any>::nil()))),
                  crane_erase_fn<uint64_t>(
                      [](const List<std::any> &_x) { return _x.length(); })),
              List<dynamic>::nil())));
  static inline const uint64_t total = items.template fold_left<uint64_t>(
      [](uint64_t acc, const dynamic &d) { return (acc + read(d)); },
      UINT64_C(0));
};

#endif // INCLUDED_EXISTENTIAL_CTOR_ERASED_FN
