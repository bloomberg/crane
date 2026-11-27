#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "lazy.h"
#include "obj.h"
#include "small_vector.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

struct Nat {};

struct Z {};

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
    requires std::is_invocable_r_v<T1, F0 &, A &, T1 &&>
  T1 fold_right(F0 &&f, T1 a0) const {
    const List<A> *_self = this;

    // Explicit stack replaces the non-tail recursion of fold_right: _call
    // frames are pending calls, _after frames resume a caller.
    struct _call {
      const List<A> *_self;
    };

    struct _after_fold_right_in_Cons {
      A a1;
    };

    using _frame = std::variant<_call, _after_fold_right_in_Cons>;
    T1 _result{};
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
          _result = a0;
        } else {
          const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
          _stack.emplace_back(_after_fold_right_in_Cons{a1});
          _stack.emplace_back(_call{crane_raw(a2)});
        }
      } else {
        auto _f = std::move(std::get<_after_fold_right_in_Cons>(_popped));
        _stack.pop_back();
        auto a1 = std::move(_f.a1);
        _result = f(a1, std::move(_result));
      }
    }
    return _result;
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
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
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: generated program, shrunk by ephyra and delta-reduced
/// (unrelated-looking declarations kept are needed for the trigger).
///
/// A fold_right step lambda over list pt passes match e5 with [] | [_] | _ :: _
/// :: _ => .. as a local fixpoint's argument while the fixpoint's step folds
/// over e5: the nested match calls v_mut() on a const List<pt> ("function is
/// not marked const"). The eta closure around the partial
/// application captures e5 by copy, so e5 is const in its body, while
/// the ownership plan, made over Core, saw the match where e5 is owned.
/// Same family as the fixed sum_match_const_v_mut.
struct FoldStepListMatchConstVMut {
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

  static inline const uint64_t t_2 = []() {
    return []() {
      crane::fn<List<int64_t>(List<bool>)> w62 =
          List<List<pt>>::nil().template fold_right<
              crane::fn<List<int64_t>(List<bool>)>>(
              [](List<pt> e5, crane::fn<List<int64_t>(List<bool>)>) {
                auto go6 =
                    [](List<bool> l7, crane::fn<List<int64_t>(List<bool>)>,
                       List<bool>)
                         -> List<int64_t> {
                      // Loop replaces the tail recursion: each recursive call
                      // updates the loop variables.
                      List<bool> _loop_l7 = std::move(l7);
                      while (true) {
                        if (std::holds_alternative<typename List<bool>::Nil>(
                                _loop_l7.v_mut())) {
                          return List<int64_t>::nil();
                        } else {
                          auto &[_, a1] = std::get<typename List<bool>::Cons>(
                              _loop_l7.v_mut());
                          const List<bool> &a1_value = *a1;
                          _loop_l7 = List<bool>(a1_value);
                        }
                      }
                    };
                return [=](List<bool> _pa0) {
                  return go6(
                      [&]() {
                        if (std::holds_alternative<typename List<pt>::Nil>(
                                e5.v())) {
                          return List<bool>::nil();
                        } else {
                          const auto &[_, a10] =
                              std::get<typename List<pt>::Cons>(e5.v());
                          auto &&_sv = *a10;
                          if (std::holds_alternative<typename List<pt>::Nil>(
                                  _sv.v())) {
                            return List<bool>::nil();
                          } else {
                            return List<bool>::nil();
                          }
                        }
                      }(),
                      [](const List<bool> &) { return List<int64_t>::nil(); },
                      _pa0);
                };
              },
              [](List<bool>) { return List<int64_t>::nil(); });
      auto _once5 = [&]() {
        List<int64_t> w63 = w62(List<bool>::nil());
        return w63.template fold_left<uint64_t>(
            [](uint64_t w65, int64_t e) {
              auto _once3 =
                  (e < 0 ? static_cast<int64_t>(-static_cast<uint64_t>(e)) : e);
              auto _once4 = w65 * UINT64_C(3) +
                            (static_cast<uint64_t>(_once3 < 0 ? 0 : _once3) *
                             UINT64_C(2) +
                             (e < INT64_C(0) ? UINT64_C(1) : UINT64_C(0)));
              return (UINT64_C(10007) ? _once4 % UINT64_C(10007) : _once4);
            },
            UINT64_C(1));
      }() + [&]() {
        List<int64_t> w63 = w62(List<bool>::nil());
        return w63.template fold_left<uint64_t>(
            [](uint64_t w65, int64_t e) {
              auto _once1 =
                  (e < 0 ? static_cast<int64_t>(-static_cast<uint64_t>(e)) : e);
              auto _once2 = w65 * UINT64_C(3) +
                            (static_cast<uint64_t>(_once1 < 0 ? 0 : _once1) *
                             UINT64_C(2) +
                             (e < INT64_C(0) ? UINT64_C(1) : UINT64_C(0)));
              return (UINT64_C(10007) ? _once2 % UINT64_C(10007) : _once2);
            },
            UINT64_C(1));
      }();
      return (UINT64_C(10007) ? _once5 % UINT64_C(10007) : _once5);
    }();
  }();
};
